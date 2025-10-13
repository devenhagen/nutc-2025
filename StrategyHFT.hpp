// =====================================================================================
// Northwestern Trading Contest — HFT strategy (C++20)
// Implements senior-level, low-latency market making + sniping with inventory control.
// Follows the exact Strategy interface and order APIs from templateHFT.hpp.
// References:
// - NUTC Case Packet (HFT section: no fees; shared order book; rate limiting; 100k capital; no leverage). :contentReference[oaicite:0]{index=0}
// - Function signatures (place_market_order, place_limit_order, cancel_order) and Strategy callbacks. :contentReference[oaicite:1]{index=1}
//
// Notes inspired by the Traders@MIT 2019 code you shared:
// - Use size-weighted microprice / fair value (weighting by opposite side size).
// - Momentum follow on very large prints; “stale quote sniping” when top-of-book is off fair.
// - Quote rebalancing/skew by inventory; adverse-selection fade on one-sided order book.
// =====================================================================================

#include <array>
#include <cmath>
#include <cstdint>
#include <limits>
#include <string>

// ---- API from templateHFT.hpp --------------------------------------------------------
// (Do not modify these declarations; provided by the exchange harness.)
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
  // ------------------------ Tunable params (conservative defaults) --------------------
  static constexpr int    NTICK = 3;                       // number of tickers supported
  static constexpr float  MIN_TICK = 0.01f;                // assume 1c tick if not provided
  static constexpr float  EDGE_EPS = 0.002f;               // absolute edge floor ($0.002)
  static constexpr float  REQUOTE_FRAC = 0.25f;            // reprice if mid moves ≥ 25% of spread
  static constexpr float  OBI_PULL = 0.70f;                // fade quotes if |OBI| is extreme
  static constexpr float  MOMENTUM_TAKE_OBI = 0.35f;       // require some imbalance to follow
  static constexpr float  INVENTORY_SOFT = 2000.0f;        // skew quotes after this
  static constexpr float  INVENTORY_HARD = 3000.0f;        // stop quoting that side after this
  static constexpr float  MAX_SNIPE_QTY = 500.0f;          // cap IOC snipes to avoid overfill
  static constexpr float  MAX_QUOTE_QTY = 200.0f;          // size of each standing quote
  static constexpr float  BIG_PRINT_QTY = 2000.0f;         // “very large” tape print threshold
  static constexpr float  EMA_FAST_A = 0.35f;              // fast EMA coefficient
  static constexpr float  EMA_SLOW_A = 0.08f;              // slow EMA coefficient
  static constexpr float  SKEW_PER_1000 = 0.10f;           // quote skew per 1000 inventory (10%)

  // ------------------------ Per-ticker state ------------------------------------------
  struct Book {
    float bid_px = 0, bid_sz = 0;
    float ask_px = std::numeric_limits<float>::infinity(), ask_sz = 0;
    float mid = 0, spread = 0, micro = 0, obi = 0; // obi in [-1,1]
    float ema_fast = 0, ema_slow = 0;              // mid EMAs
    bool  has_bid = false, has_ask = false;

    // size-weighted “microprice” (weights by opposite side size; cf. TAMIT idea)
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
        obi = (den > 0) ? (bid_sz - ask_sz) / den : 0.0f; // order book imbalance
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
  float capital_remaining_ = 100000.0f; // updated from on_account_update

  // Helper to clamp price to reasonable granularity
  static inline float round_to_tick(float px) {
    // Round to nearest cent to avoid hammering rate limits with tiny price drift
    return std::round(px / MIN_TICK) * MIN_TICK;
  }

  // Desired quote prices (skew by inventory; edge away from fair)
  struct Targets { float bid_px = 0, ask_px = 0, qty_bid = 0, qty_ask = 0; };

  Targets compute_targets(int k) {
    Targets t{};
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return t;

    const float fair = b.micro;                 // size-weighted fair
    const float spread = b.spread;
    const float edge = std::max(EDGE_EPS, 0.35f * spread);

    // Inventory skew: push the “danger” side away from fair
    float inv = pos_[k];
    float skew = (inv / 1000.0f) * SKEW_PER_1000 * spread;
    // also use momentum (EMA) to lean slightly
    float mom = (b.ema_fast - b.ema_slow);

    // Protect against adverse selection: lean with OBI and momentum
    float lean = 0.25f * mom + 0.20f * b.obi * spread;

    float bid_edge = edge + std::max(0.0f, skew) + std::max(0.0f, -lean);
    float ask_edge = edge + std::max(0.0f, -skew) + std::max(0.0f,  lean);

    t.bid_px = round_to_tick(std::min(fair - bid_edge, b.bid_px)); // price-time priority
    t.ask_px = round_to_tick(std::max(fair + ask_edge, b.ask_px));

    // Size: anchor to top-of-book depth but cap
    float sz_hint = 0.25f * std::max(10.0f, std::min(b.bid_sz, b.ask_sz));
    t.qty_bid = std::min(MAX_QUOTE_QTY, std::max(10.0f, sz_hint));
    t.qty_ask = std::min(MAX_QUOTE_QTY, std::max(10.0f, sz_hint));

    // Risk limits: scale down size as we approach hard limits
    if (std::fabs(inv) > INVENTORY_SOFT) {
      float scale = std::max(0.2f, 1.0f - (std::fabs(inv) - INVENTORY_SOFT) / (INVENTORY_HARD - INVENTORY_SOFT + 1.0f));
      t.qty_bid *= (inv < 0 ? 1.0f : scale); // if short, keep bidding to cover
      t.qty_ask *= (inv > 0 ? 1.0f : scale); // if long, keep offering to lighten
    }
    if (inv >= INVENTORY_HARD) { t.qty_bid = 0; }   // stop adding to long
    if (inv <= -INVENTORY_HARD){ t.qty_ask = 0; }   // stop adding to short
    return t;
  }

  void try_requote(int k, const Targets &t) {
    Quote &q = quotes_[k];
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;

    // Cancel/replace logic (avoid churn): only move if mid moved sufficiently vs our last px
    auto need_move = [&](float old_px, float new_px) {
      return std::fabs(new_px - old_px) >= std::max(MIN_TICK, REQUOTE_FRAC * b.spread);
    };

    // Fade quotes in extreme imbalance to avoid adverse selection
    bool fade_bid = (b.obi < -OBI_PULL);
    bool fade_ask = (b.obi >  OBI_PULL);

    // ----- BID side -----
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

    // ----- ASK side -----
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

  // Sniping: when top of book is stale vs fair, cross the spread with IOC
  void try_snipe(int k) {
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;
    const float fair = b.micro;
    const float spread = b.spread;
    const float take_edge = std::max(EDGE_EPS, 0.30f * spread);
    const float inv = pos_[k];

    // buy IOC if offer is cheap
    if (b.ask_px + take_edge < fair && inv < INVENTORY_HARD) {
      float qty = std::min(MAX_SNIPE_QTY, std::max(10.0f, 0.5f * b.ask_sz));
      place_limit_order(Side::buy, static_cast<Ticker>(k), qty, b.ask_px, /*IOC=*/true);
    }
    // sell IOC if bid is rich
    if (b.bid_px - take_edge > fair && inv > -INVENTORY_HARD) {
      float qty = std::min(MAX_SNIPE_QTY, std::max(10.0f, 0.5f * b.bid_sz));
      place_limit_order(Side::sell, static_cast<Ticker>(k), qty, b.bid_px, /*IOC=*/true);
    }
  }

  // Momentum follow after very large prints (inspired by TAMIT logic: BIG BUY/SELL DETECTED)
  void momentum_follow(int k, Side aggressive_side, float px, float qty_hint) {
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;

    // Require some supportive imbalance to avoid buying tops/selling bottoms
    if (std::fabs(b.obi) < MOMENTUM_TAKE_OBI) return;

    float max_qty = std::min(MAX_SNIPE_QTY, std::max(50.0f, 0.25f * qty_hint));
    if (aggressive_side == Side::buy && pos_[k] < INVENTORY_HARD) {
      // join the buy-side and lift offers slightly above best
      float px_take = std::max(b.ask_px, px) + 0.01f;
      place_limit_order(Side::buy, static_cast<Ticker>(k), max_qty, px_take, /*IOC=*/true);
    } else if (aggressive_side == Side::sell && pos_[k] > -INVENTORY_HARD) {
      float px_hit = std::min(b.bid_px, px) - 0.01f;
      place_limit_order(Side::sell, static_cast<Ticker>(k), max_qty, px_hit, /*IOC=*/true);
    }
  }

public:
  Strategy() {
    // Keep initial state zeros; avoid heavy allocation to respect CPU/RAM limits in case packet. :contentReference[oaicite:2]{index=2}
    println("HFT strategy initialized.");
  }

  // -----------------------------------------------------------------------------
  // Called whenever two orders match (anyone’s orders). side = aggressive side.
  // -----------------------------------------------------------------------------
  void on_trade_update(Ticker ticker, Side side, float quantity, float price) {
    const int k = static_cast<int>(ticker);

    // Update last known trade into book proxies if we lack a side
    // (We don’t overwrite quotes; we only use trade info for momentum/sniping.)
    if (!books_[k].has_bid || !books_[k].has_ask) {
      // no direct book change here; we’ll react on on_orderbook_update
    }

    // Large print detection -> momentum follow (IOC), sized conservatively.
    if (quantity >= BIG_PRINT_QTY) {
      momentum_follow(k, side, price, quantity);
    }
  }

  // -----------------------------------------------------------------------------
  // Called whenever the orderbook changes for a price level (top-of-book events
  // will arrive as quantities at best prices). We maintain best bid/ask snapshots.
  // -----------------------------------------------------------------------------
  void on_orderbook_update(Ticker ticker, Side side, float quantity, float price) {
    const int k = static_cast<int>(ticker);
    Book &b = books_[k];

    // Update best bid/ask when level changes at top.
    // The harness provides “total quantity at price”; we only track best levels.
    if (side == Side::buy) {
      // If incoming price is above current best, it becomes best. If at best, update size.
      if (price > b.bid_px || !b.has_bid) { b.bid_px = price; b.bid_sz = quantity; }
      else if (std::fabs(price - b.bid_px) < 1e-6f) { b.bid_sz = quantity; }
      // If best level depleted, we may keep a stale price; next updates will correct it.
      if (b.bid_sz <= 0) { b.has_bid = false; b.bid_px = 0; }
    } else {
      if (price < b.ask_px || !b.has_ask) { b.ask_px = price; b.ask_sz = quantity; }
      else if (std::fabs(price - b.ask_px) < 1e-6f) { b.ask_sz = quantity; }
      if (b.ask_sz <= 0) { b.has_ask = false; b.ask_px = std::numeric_limits<float>::infinity(); }
    }

    b.update_derived();
    b.push_ema();

    if (b.has_bid && b.has_ask) {
      // First, try to snipe obviously stale top-of-book
      try_snipe(k);

      // Then (re)quote passively with inventory & momentum aware skew
      Targets t = compute_targets(k);
      try_requote(k, t);
    }
  }

  // -----------------------------------------------------------------------------
  // Called whenever one of our orders is filled.
  // Updates inventory and capital remaining for risk control/position skew.
  // -----------------------------------------------------------------------------
  void on_account_update(Ticker ticker, Side side, float price, float quantity, float capital_remaining) {
    const int k = static_cast<int>(ticker);
    capital_remaining_ = capital_remaining;
    // Update signed position (buy adds, sell subtracts)
    pos_[k] += (side == Side::buy ? quantity : -quantity);

    // If at/over hard limit, pull that side immediately
    if (pos_[k] >=  INVENTORY_HARD && quotes_[k].id_bid) {
      cancel_order(ticker, quotes_[k].id_bid); quotes_[k].id_bid = 0;
    }
    if (pos_[k] <= -INVENTORY_HARD && quotes_[k].id_ask) {
      cancel_order(ticker, quotes_[k].id_ask); quotes_[k].id_ask = 0;
    }
  }
};
