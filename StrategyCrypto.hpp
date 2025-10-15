// =====================================================================================
// Northwestern Trading Contest â€” CRYPTO strategy (C++20)
// Low-latency market making + sniping + big-print momentum follow, inventory-aware.
// EXACT same template style as your HFT file (top-of-book only, same API calls).
// Crypto-specific: 0.4% fee per fill => ~0.8% round trip; we gate quoting on fees.
// =====================================================================================

#include <array>
#include <cmath>
#include <cstdint>
#include <limits>
#include <string>

// ---- API from templateHFT.hpp --------------------------------------------------------
enum class Side { buy = 0, sell = 1 };
enum class Ticker : std::uint8_t { ETH = 0, BTC = 1, LTC = 2 }; // NOLINT

bool place_market_order(Side side, Ticker ticker, float quantity);
std::int64_t place_limit_order(Side side, Ticker ticker, float quantity, float price, bool ioc = false);
bool cancel_order(Ticker ticker, std::int64_t order_id);
void println(const std::string &text);

// =====================================================================================
//                                   STRATEGY
// =====================================================================================

class Strategy {
  // ------------------------ Crypto params --------------------------------------------
  static constexpr int    NTICK = 3;
  static constexpr float  MIN_TICK = 0.01f;

  // Fees: 0.4% per fill â†’ ~0.8% round-trip; add cushion
  static constexpr float  FEE_PER_FILL = 0.004f;
  static constexpr float  FEE_ROUNDTRIP = 2.0f * FEE_PER_FILL;  // ~0.8%
  static constexpr float  FEE_GUARD = 0.0095f;                  // require >~0.95% full spread

  // Quoting & control
  static constexpr float  EDGE_EPS = 0.002f;         // absolute edge floor
  static constexpr float  REQUOTE_FRAC = 0.25f;      // reprice if mid shifts â‰¥ 25% of spread
  static constexpr float  OBI_PULL = 0.70f;          // pull that side if imbalance extreme
  static constexpr float  MOMENTUM_TAKE_OBI = 0.35f; // require some imbalance to chase

  static constexpr float  INVENTORY_SOFT = 2000.0f;
  static constexpr float  INVENTORY_HARD = 3000.0f;

  static constexpr float  MAX_SNIPE_QTY = 500.0f;
  static constexpr float  MAX_QUOTE_QTY = 200.0f;
  static constexpr float  BIG_PRINT_QTY = 2000.0f;

  static constexpr float  EMA_FAST_A = 0.35f;
  static constexpr float  EMA_SLOW_A = 0.08f;
  static constexpr float  SKEW_PER_1000 = 0.10f;     // skew per 1000 inventory (fraction of spread)

  // ------------------------ Per-ticker state ------------------------------------------
  struct Book {
    float bid_px = 0, bid_sz = 0;
    float ask_px = std::numeric_limits<float>::infinity(), ask_sz = 0;
    float mid = 0, spread = 0, micro = 0, obi = 0; // obi in [-1,1]
    float ema_fast = 0, ema_slow = 0;
    bool  has_bid = false, has_ask = false;

    static inline float weighted_mid(float bid_px, float ask_px, float bid_sz, float ask_sz) {
      float wb = (ask_sz <= 0 ? 0.0f : ask_sz);
      float wa = (bid_sz <= 0 ? 0.0f : bid_sz);
      float den = wb + wa;
      if (den <= 0) return (bid_px + ask_px) * 0.5f;
      return (wb * bid_px + wa * ask_px) / den;
    }

    void update_derived() {
      has_bid = bid_px > 0 && bid_sz > 0;
      has_ask = std::isfinite(ask_px) && ask_sz > 0;
      if (has_bid && has_ask) {
        mid    = 0.5f * (bid_px + ask_px);
        spread = std::max(MIN_TICK, ask_px - bid_px);
        micro  = weighted_mid(bid_px, ask_px, bid_sz, ask_sz);
        float den = bid_sz + ask_sz;
        obi = (den > 0) ? (bid_sz - ask_sz) / den : 0.0f;
      }
    }

    void push_ema() {
      if (!(has_bid && has_ask)) return;
      if (ema_fast == 0) { ema_fast = mid; ema_slow = mid; return; }
      ema_fast = EMA_FAST_A * mid + (1.0f - EMA_FAST_A) * ema_fast;
      ema_slow = EMA_SLOW_A * mid + (1.0f - EMA_SLOW_A) * ema_slow;
    }
  };

  struct Quote {
    std::int64_t id_bid = 0, id_ask = 0;
    float px_bid = 0, px_ask = 0;
    float qty_bid = 0, qty_ask = 0;
  };

  std::array<Book, NTICK>  books_{};
  std::array<Quote, NTICK> quotes_{};
  std::array<float, NTICK> pos_{};
  float capital_remaining_ = 100000.0f;

  static inline float round_to_tick(float px) {
    return std::round(px / MIN_TICK) * MIN_TICK;
  }

  struct Targets { float bid_px = 0, ask_px = 0, qty_bid = 0, qty_ask = 0; };

  Targets compute_targets(int k) {
    Targets t{};
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return t;

    const float fair   = b.micro;
    const float spread = b.spread;

    // Half-edge baseline (relative to spread), plus absolute floor
    float edge_rel = 0.35f * spread;        // base half-edge from spread
    float edge     = std::max(EDGE_EPS, edge_rel);

    // Fee guard: only quote if full spread (2*edge) clears round-trip fees w/ cushion
    if (2.0f * edge <= FEE_GUARD) {
      t.qty_bid = 0; t.qty_ask = 0; // signal cancel on both sides
      return t;
    }

    // Inventory skew + momentum lean
    float inv  = pos_[k];
    float skew = (inv / 1000.0f) * SKEW_PER_1000 * spread;      // widen â€œdangerâ€ side
    float mom  = (b.ema_fast - b.ema_slow);
    float lean = 0.25f * mom + 0.20f * b.obi * spread;          // steer w/ imbalance & ema

    float bid_edge = edge + (skew > 0 ? skew : 0) + (lean < 0 ? -lean : 0);
    float ask_edge = edge + (skew < 0 ? -skew : 0) + (lean > 0 ?  lean : 0);

    t.bid_px = round_to_tick(std::min(fair - bid_edge, b.bid_px)); // keep price-time priority
    t.ask_px = round_to_tick(std::max(fair + ask_edge, b.ask_px));

    // Size relative to TOB depth; cap by risk
    float sz_hint = 0.25f * std::max(10.0f, std::min(b.bid_sz, b.ask_sz));
    t.qty_bid = std::min(MAX_QUOTE_QTY, std::max(10.0f, sz_hint));
    t.qty_ask = std::min(MAX_QUOTE_QTY, std::max(10.0f, sz_hint));

    if (std::fabs(inv) > INVENTORY_SOFT) {
      float scale = std::max(0.2f, 1.0f - (std::fabs(inv) - INVENTORY_SOFT) / (INVENTORY_HARD - INVENTORY_SOFT + 1.0f));
      t.qty_bid *= (inv < 0 ? 1.0f : scale);
      t.qty_ask *= (inv > 0 ? 1.0f : scale);
    }
    if (inv >=  INVENTORY_HARD) t.qty_bid = 0;
    if (inv <= -INVENTORY_HARD) t.qty_ask = 0;

    return t;
  }

  void try_requote(int k, const Targets &t) {
    Quote &q = quotes_[k];
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;

    auto need_move = [&](float old_px, float new_px) {
      return std::fabs(new_px - old_px) >= std::max(MIN_TICK, REQUOTE_FRAC * b.spread);
    };

    bool fade_bid = (b.obi < -OBI_PULL);
    bool fade_ask = (b.obi >  OBI_PULL);

    // ----- BID -----
    if (t.qty_bid <= 0 || fade_bid) {
      if (q.id_bid) { cancel_order(static_cast<Ticker>(k), q.id_bid); q.id_bid = 0; }
    } else {
      if (!q.id_bid || need_move(q.px_bid, t.bid_px)) {
        if (q.id_bid) { cancel_order(static_cast<Ticker>(k), q.id_bid); q.id_bid = 0; }
        q.px_bid = t.bid_px;
        q.qty_bid = t.qty_bid;
        q.id_bid = place_limit_order(Side::buy, static_cast<Ticker>(k), q.qty_bid, q.px_bid, /*IOC=*/false);
      }
    }

    // ----- ASK -----
    if (t.qty_ask <= 0 || fade_ask) {
      if (q.id_ask) { cancel_order(static_cast<Ticker>(k), q.id_ask); q.id_ask = 0; }
    } else {
      if (!q.id_ask || need_move(q.px_ask, t.ask_px)) {
        if (q.id_ask) { cancel_order(static_cast<Ticker>(k), q.id_ask); q.id_ask = 0; }
        q.px_ask = t.ask_px;
        q.qty_ask = t.qty_ask;
        q.id_ask = place_limit_order(Side::sell, static_cast<Ticker>(k), q.qty_ask, q.px_ask, /*IOC=*/false);
      }
    }
  }

  // Sniping with IOC only when top-of-book is clearly stale versus fair AND covers fees
  void try_snipe(int k) {
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;

    const float fair   = b.micro;
    const float spread = b.spread;

    // Require post-fee edge on the take: (fair - ask) or (bid - fair) must exceed fee per take + cushion
    const float take_guard = FEE_PER_FILL + 0.0015f; // ~0.55% absolute minimum on the take leg

    if (fair - b.ask_px > std::max(EDGE_EPS, 0.30f * spread) && (fair - b.ask_px) > take_guard && pos_[k] <  INVENTORY_HARD) {
      float qty = std::min(MAX_SNIPE_QTY, std::max(10.0f, 0.5f * b.ask_sz));
      place_limit_order(Side::buy, static_cast<Ticker>(k), qty, b.ask_px, /*IOC=*/true);
    }
    if (b.bid_px - fair > std::max(EDGE_EPS, 0.30f * spread) && (b.bid_px - fair) > take_guard && pos_[k] > -INVENTORY_HARD) {
      float qty = std::min(MAX_SNIPE_QTY, std::max(10.0f, 0.5f * b.bid_sz));
      place_limit_order(Side::sell, static_cast<Ticker>(k), qty, b.bid_px, /*IOC=*/true);
    }
  }

  // Big-print momentum follow (IOC), gated by imbalance so we don't chase noise
  void momentum_follow(int k, Side aggressive_side, float px, float qty_hint) {
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;
    if (std::fabs(b.obi) < MOMENTUM_TAKE_OBI) return;

    float max_qty = std::min(MAX_SNIPE_QTY, std::max(50.0f, 0.25f * qty_hint));
    if (aggressive_side == Side::buy && pos_[k] < INVENTORY_HARD) {
      float px_take = std::max(b.ask_px, px) + 0.01f;
      place_limit_order(Side::buy, static_cast<Ticker>(k), max_qty, px_take, /*IOC=*/true);
    } else if (aggressive_side == Side::sell && pos_[k] > -INVENTORY_HARD) {
      float px_hit = std::min(b.bid_px, px) - 0.01f;
      place_limit_order(Side::sell, static_cast<Ticker>(k), max_qty, px_hit, /*IOC=*/true);
    }
  }

public:
  Strategy() {
    println("CRYPTO strategy initialized.");
  }

  // -----------------------------------------------------------------------------  
  void on_trade_update(Ticker ticker, Side side, float quantity, float price) {
    const int k = static_cast<int>(ticker);
    if (quantity >= BIG_PRINT_QTY) {
      momentum_follow(k, side, price, quantity);
    }
  }

  // -----------------------------------------------------------------------------
  void on_orderbook_update(Ticker ticker, Side side, float quantity, float price) {
    const int k = static_cast<int>(ticker);
    Book &b = books_[k];

    if (side == Side::buy) {
      if (price > b.bid_px || !b.has_bid) { b.bid_px = price; b.bid_sz = quantity; }
      else if (std::fabs(price - b.bid_px) < 1e-6f) { b.bid_sz = quantity; }
      if (b.bid_sz <= 0) { b.has_bid = false; b.bid_px = 0; }
    } else {
      if (price < b.ask_px || !b.has_ask) { b.ask_px = price; b.ask_sz = quantity; }
      else if (std::fabs(price - b.ask_px) < 1e-6f) { b.ask_sz = quantity; }
      if (b.ask_sz <= 0) { b.has_ask = false; b.ask_px = std::numeric_limits<float>::infinity(); }
    }

    b.update_derived();
    b.push_ema();

    if (b.has_bid && b.has_ask) {
      try_snipe(k);                   // opportunistic taker (IOC) when TOB is stale post-fee
      Targets t = compute_targets(k); // fee-aware maker quotes
      try_requote(k, t);
    }
  }

  // -----------------------------------------------------------------------------
  void on_account_update(Ticker ticker, Side side, float price, float quantity, float capital_remaining) {
    const int k = static_cast<int>(ticker);
    capital_remaining_ = capital_remaining;
    pos_[k] += (side == Side::buy ? quantity : -quantity);

    // Hard inventory brakes
    if (pos_[k] >=  INVENTORY_HARD && quotes_[k].id_bid) {
      cancel_order(ticker, quotes_[k].id_bid); quotes_[k].id_bid = 0;
    }
    if (pos_[k] <= -INVENTORY_HARD && quotes_[k].id_ask) {
      cancel_order(ticker, quotes_[k].id_ask); quotes_[k].id_ask = 0;
    }
    (void)price;
  }
};