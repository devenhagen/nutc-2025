#include <array>
#include <cmath>
#include <cstdint>
#include <limits>
#include <string>

// ---- Exchange API (from templateHFT.hpp) ----
// These functions and enums are provided by the competition harness.
enum class Side { buy = 0, sell = 1 };
enum class Ticker : std::uint8_t { ETH = 0, BTC = 1, LTC = 2 };  // 3 traded tickers
bool place_market_order(Side side, Ticker ticker, float quantity);
std::int64_t place_limit_order(Side side, Ticker ticker, float quantity, float price, bool ioc = false);
bool cancel_order(Ticker ticker, std::int64_t order_id);
void println(const std::string &text);

// ---- HFT Trading Strategy Class ---- 
class Strategy {
  // *** Tunable Parameters *** (set for safety; adjust for aggressiveness if needed)
  static constexpr int    NTICK        = 3;         // number of tickers supported
  static constexpr float  MIN_TICK     = 0.01f;     // minimum price increment (assume 1 cent if not given)
  static constexpr float  EDGE_EPS     = 0.002f;    // minimum absolute edge on quotes (~$0.002):contentReference[oaicite:18]{index=18}
  static constexpr float  REQUOTE_FRAC = 0.25f;     // repricing threshold as fraction of spread (25%)
  static constexpr float  OBI_PULL     = 0.70f;     // OBI extreme threshold to pull quotes (≥70% imbalance)
  static constexpr float  MOMENTUM_TAKE_OBI = 0.35f; // minimum imbalance to allow momentum follow IOC
  static constexpr float  INVENTORY_SOFT = 2000.0f; // soft inventory limit (start reducing size)
  static constexpr float  INVENTORY_HARD = 3000.0f; // hard inventory limit (stop quoting that direction)
  static constexpr float  MAX_SNIPE_QTY = 500.0f;   // max size for sniping IOC orders (to limit impact)
  static constexpr float  MAX_QUOTE_QTY = 200.0f;   // max size for passive quotes
  static constexpr float  BIG_PRINT_QTY = 2000.0f;  // threshold for "very large" trade volume
  static constexpr float  EMA_FAST_A   = 0.35f;     // smoothing factor for fast EMA (responsive)
  static constexpr float  EMA_SLOW_A   = 0.08f;     // smoothing factor for slow EMA (longer term)
  static constexpr float  SKEW_PER_1000 = 0.10f;    // quote price skew (as % of spread) per 1000 units inventory

  // *** Per-Ticker Market State ***
  struct Book {
    float bid_px = 0.0f, bid_sz = 0.0f;
    float ask_px = std::numeric_limits<float>::infinity(), ask_sz = 0.0f;
    float mid = 0.0f, spread = 0.0f;
    float micro = 0.0f, obi = 0.0f;       // microprice (fair value) and order book imbalance (-1 to 1)
    float ema_fast = 0.0f, ema_slow = 0.0f;
    bool  has_bid = false, has_ask = false;

    // Compute size-weighted microprice (mid weighted by opposite side size):contentReference[oaicite:19]{index=19}
    static inline float weighted_mid(float bid_px, float ask_px, float bid_sz, float ask_sz) {
      float w_bid = (ask_sz <= 0 ? 0.0f : ask_sz);
      float w_ask = (bid_sz <= 0 ? 0.0f : bid_sz);
      float total_w = w_bid + w_ask;
      if (total_w <= 0) {
        return 0.5f * (bid_px + ask_px);  // if no depth info, fall back to simple mid
      }
      // Heavier side’s price gets more weight – yields fair value towards the lighter side
      return (w_bid * bid_px + w_ask * ask_px) / total_w;
    }

    // Update derived values (mid, spread, microprice, OBI) whenever top-of-book changes
    void update_derived() {
      has_bid = (bid_px > 0.0f && bid_sz > 0.0f);
      has_ask = (ask_px < std::numeric_limits<float>::infinity() && ask_sz > 0.0f);
      if (has_bid && has_ask) {
        mid    = 0.5f * (bid_px + ask_px);
        spread = std::max(MIN_TICK, ask_px - bid_px);
        micro  = weighted_mid(bid_px, ask_px, bid_sz, ask_sz);
        // Order Book Imbalance: (bid_vol - ask_vol) / (bid_vol + ask_vol):contentReference[oaicite:20]{index=20}:contentReference[oaicite:21]{index=21}
        float total_vol = bid_sz + ask_sz;
        obi   = (total_vol > 0 ? (bid_sz - ask_sz) / total_vol : 0.0f);
      } else {
        // If one side missing, we can't compute mid or micro meaningfully
        // (We wait until both sides present to act)
      }
    }

    // Push latest mid into EMAs (called each update when both sides present)
    void push_ema() {
      if (!(has_bid && has_ask)) return;
      if (ema_fast == 0.0f && ema_slow == 0.0f) {
        // Initialize EMAs to current mid on first update
        ema_fast = mid;
        ema_slow = mid;
      } else {
        // EMA update: ema_new = alpha*current + (1-alpha)*ema_old
        ema_fast = EMA_FAST_A * mid + (1.0f - EMA_FAST_A) * ema_fast;
        ema_slow = EMA_SLOW_A * mid + (1.0f - EMA_SLOW_A) * ema_slow;
      }
    }
  };

  struct Quote {  // our current resting orders (one bid and one ask per ticker)
    std::int64_t id_bid = 0, id_ask = 0;
    float px_bid = 0.0f, px_ask = 0.0f;
    float qty_bid = 0.0f, qty_ask = 0.0f;
  };

  // State arrays for all tickers
  std::array<Book, NTICK>  books_{};
  std::array<Quote, NTICK> quotes_{};
  std::array<float, NTICK> pos_{};                 // inventory position per ticker
  float capital_remaining_ = 100000.0f;            // track remaining capital (for risk control)

  // Helper: Round a price to the nearest tick (to avoid spamming tiny price differences)
  static inline float round_to_tick(float price) {
    return std::round(price / MIN_TICK) * MIN_TICK;
  }

  // Structure for target quote parameters (computed each update)
  struct Targets { float bid_px=0, ask_px=0, qty_bid=0, qty_ask=0; };

  // Compute where and how much we *want* to quote on each side, given current market and inventory
  Targets compute_targets(int k) {
    Targets t{};
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return t;  // need a valid market

    // Fair value and spread
    float fair = b.micro; 
    float spread = b.spread;
    // Base edge: at least EDGE_EPS or some fraction of spread (e.g. 35%)
    float edge = std::max(EDGE_EPS, 0.35f * spread);

    // **Inventory-based skew**: move quotes away on the side where we have excess inventory:contentReference[oaicite:22]{index=22}
    float inv = pos_[k];
    float skew_offset = (inv / 1000.0f) * SKEW_PER_1000 * spread;
    // **Momentum and order flow lean**: lean quotes with the market trend
    float momentum = b.ema_fast - b.ema_slow;               // positive = upward trend, negative = downward
    float lean_offset = 0.25f * momentum + 0.20f * b.obi * spread;
    // lean_offset > 0 => market pressure up (or ask side small), lean_offset < 0 => pressure down

    // Calculate quote edges for each side incorporating skew and lean (only penalize “dangerous” side)
    float bid_edge = edge + std::max(0.0f, skew_offset) + std::max(0.0f, -lean_offset);
    float ask_edge = edge + std::max(0.0f, -skew_offset) + std::max(0.0f,  lean_offset);

    // **Target prices:** fair +/- edge, clamped not to cross the current best quotes (join best or behind it)
    t.bid_px = round_to_tick(std::min(fair - bid_edge, b.bid_px));
    t.ask_px = round_to_tick(std::max(fair + ask_edge, b.ask_px));
    // (We use min with best bid: never bid higher than current best bid, to avoid taking liquidity unintentionally.
    //  Likewise, never ask lower than best ask.)

    // **Target size:** base on top-of-book sizes, to participate meaningfully but not dominate.
    float size_hint = 0.25f * std::max(10.0f, std::min(b.bid_sz, b.ask_sz));  // 25% of smaller top depth, min 10
    t.qty_bid = std::min(MAX_QUOTE_QTY, std::max(10.0f, size_hint));
    t.qty_ask = std::min(MAX_QUOTE_QTY, std::max(10.0f, size_hint));

    // **Inventory risk adjustments:** If inventory is beyond soft limit, reduce quote size on that side to reduce risk.
    if (std::fabs(inv) > INVENTORY_SOFT) {
      float excess = std::fabs(inv) - INVENTORY_SOFT;
      float scale = std::max(0.2f, 1.0f - excess / (INVENTORY_HARD - INVENTORY_SOFT + 1.0f));
      if (inv > INVENTORY_SOFT) { 
        // long inventory – scale down bid size (don’t want more longs), keep ask size (want to sell out)
        t.qty_bid *= scale;  
      } else if (inv < -INVENTORY_SOFT) {
        // short inventory – scale down ask size, keep bid size
        t.qty_ask *= scale;
      }
    }
    // Hard inventory limit: stop quoting that side entirely to not accumulate further
    if (inv >=  INVENTORY_HARD) { t.qty_bid = 0.0f; }
    if (inv <= -INVENTORY_HARD) { t.qty_ask = 0.0f; }

    return t;
  }

  // Adjust (or cancel/recreate) our quotes to match the target prices and sizes
  void try_requote(int k, const Targets &t) {
    Quote &q = quotes_[k];
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;  // no valid market data to act on

    // Lambda: decide if we need to move an existing order based on price change threshold
    auto need_move = [&](float old_px, float new_px) {
      return std::fabs(new_px - old_px) >= std::max(MIN_TICK, REQUOTE_FRAC * b.spread);
    };

    // Determine if we should pull quotes due to adverse conditions
    bool fade_bid = (b.obi < -OBI_PULL);   // book skewed heavily to sell side (lots of asks) – fade our bid
    bool fade_ask = (b.obi >  OBI_PULL);   // book skewed heavily to buy side – fade our ask
    // **Momentum-based fade:** if strong trend, avoid quoting against it
    float mom_diff = b.ema_fast - b.ema_slow;
    if (mom_diff > 0.0f && mom_diff > 0.25f * b.spread) {  // up-trend: avoid selling into it
      fade_ask = true;
    } else if (mom_diff < 0.0f && -mom_diff > 0.25f * b.spread) {  // down-trend: avoid buying into it
      fade_bid = true;
    }

    // ----- Bid side -----
    if (t.qty_bid <= 0.0f || fade_bid) {
      // We do not want a bid quote (either inventory too long, or danger on buy side)
      if (q.id_bid) {
        cancel_order(static_cast<Ticker>(k), q.id_bid);
        q.id_bid = 0;
      }
    } else {
      // We want to place/update a bid
      if (!q.id_bid || need_move(q.px_bid, t.bid_px)) {
        // If we have no bid, or our current bid price is too far from target, (re)place it
        if (q.id_bid) {
          cancel_order(static_cast<Ticker>(k), q.id_bid);
          q.id_bid = 0;
        }
        q.px_bid  = t.bid_px;
        q.qty_bid = t.qty_bid;
        q.id_bid  = place_limit_order(Side::buy, static_cast<Ticker>(k), q.qty_bid, q.px_bid, /*ioc=*/false);
      }
      // If our existing bid is close enough to target (and exists), we leave it to avoid churn.
    }

    // ----- Ask side -----
    if (t.qty_ask <= 0.0f || fade_ask) {
      // We do not want an ask quote (either inventory too short, or danger on sell side)
      if (q.id_ask) {
        cancel_order(static_cast<Ticker>(k), q.id_ask);
        q.id_ask = 0;
      }
    } else {
      if (!q.id_ask || need_move(q.px_ask, t.ask_px)) {
        if (q.id_ask) {
          cancel_order(static_cast<Ticker>(k), q.id_ask);
          q.id_ask = 0;
        }
        q.px_ask  = t.ask_px;
        q.qty_ask = t.qty_ask;
        q.id_ask  = place_limit_order(Side::sell, static_cast<Ticker>(k), q.qty_ask, q.px_ask, /*ioc=*/false);
      }
    }
  }

  // Attempt to aggressively snipe a stale quote if the top-of-book is far off fair value
  void try_snipe(int k) {
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;
    float fair = b.micro;
    float spread = b.spread;
    // Define the minimum edge we want to gain by sniping (e.g. 30% of current spread or EDGE_EPS)
    float take_edge = std::max(EDGE_EPS, 0.30f * spread);
    float inv = pos_[k];

    // If best ask is sufficiently below fair value, buy it (provided we are not at hard long inventory)
    if (b.ask_px + take_edge < fair && inv < INVENTORY_HARD) {
      float qty = std::min(MAX_SNIPE_QTY, std::max(10.0f, 0.5f * b.ask_sz));
      place_limit_order(Side::buy, static_cast<Ticker>(k), qty, b.ask_px, /*ioc=*/true);
      // IOC buy will lift the current ask up to 'qty'. Any unfilled is canceled immediately.
    }
    // If best bid is sufficiently above fair, sell into it
    if (b.bid_px - take_edge > fair && inv > -INVENTORY_HARD) {
      float qty = std::min(MAX_SNIPE_QTY, std::max(10.0f, 0.5f * b.bid_sz));
      place_limit_order(Side::sell, static_cast<Ticker>(k), qty, b.bid_px, /*ioc=*/true);
    }
  }

  // Momentum ignition / follow-on: after a very large trade occurs, follow the aggressive side if conditions allow
  void momentum_follow(int k, Side aggressive_side, float trade_price, float trade_qty) {
    const Book &b = books_[k];
    if (!(b.has_bid && b.has_ask)) return;
    // Only act if some imbalance supports the move (avoid buying into a lone large sell, etc.)
    if (std::fabs(b.obi) < MOMENTUM_TAKE_OBI) return;  // require at least moderate OBI to confirm direction

    // Decide an IOC quantity – portion of the big print, but capped
    float qty_take = std::min(MAX_SNIPE_QTY, std::max(50.0f, 0.25f * trade_qty));
    if (aggressive_side == Side::buy && pos_[k] < INVENTORY_HARD) {
      // Large buy happened (price likely up): lift the ask slightly above current best
      float px = std::max(b.ask_px, trade_price) + MIN_TICK;  // a tick above to ensure we get priority
      place_limit_order(Side::buy, static_cast<Ticker>(k), qty_take, px, /*ioc=*/true);
    } else if (aggressive_side == Side::sell && pos_[k] > -INVENTORY_HARD) {
      // Large sell happened (price likely down): hit the bid slightly below current best
      float px = std::min(b.bid_px, trade_price) - MIN_TICK;
      place_limit_order(Side::sell, static_cast<Ticker>(k), qty_take, px, /*ioc=*/true);
    }
    // Note: using IOC ensures we don’t leave these aggressive orders in the book; we either get filled immediately or cancel.
  }

public:
  Strategy() {
    // Initialize all positions and state to zero (already default for arrays).
    // We avoid any heavy setup to respect CPU/memory limits. 
    println("HFT strategy initialized.");
  }

  // Called whenever ANY trade occurs (could involve our orders or others'). 
  // `side` here indicates the aggressor side (e.g., Side::buy means a buyer took liquidity).
  void on_trade_update(Ticker ticker, Side side, float quantity, float price) {
    int k = static_cast<int>(ticker);
    // We don’t explicitly update book here (order book updates will come via on_orderbook_update events).
    // However, we can use trades to detect momentum:
    if (quantity >= BIG_PRINT_QTY) {
      // A very large trade occurred – trigger momentum follow logic
      momentum_follow(k, side, price, quantity);
    }
  }

  // Called whenever the order book changes at a price level.
  // We use this primarily to maintain the *best bid/ask* snapshot (Book) and react when top-of-book updates.
  void on_orderbook_update(Ticker ticker, Side side, float quantity, float price) {
    int k = static_cast<int>(ticker);
    Book &b = books_[k];

    // Update our stored best bid/ask if this update affects the top-of-book:
    if (side == Side::buy) {
      // Buy side update -> potential change in best bid
      if (price > b.bid_px || !b.has_bid) {
        // New price is higher than current best bid (or we had none) -> update best bid
        b.bid_px = price;
        b.bid_sz = quantity;
      } else if (std::fabs(price - b.bid_px) < 1e-6f) {
        // Same price level (best bid) updated volume
        b.bid_sz = quantity;
      }
      if (b.bid_sz <= 0.0f) {
        // Best bid depleted
        b.has_bid = false;
        b.bid_px = 0.0f;
      }
    } else {  // side == Side::sell
      // Sell side update -> potential change in best ask
      if (price < b.ask_px || !b.has_ask) {
        b.ask_px = price;
        b.ask_sz = quantity;
      } else if (std::fabs(price - b.ask_px) < 1e-6f) {
        b.ask_sz = quantity;
      }
      if (b.ask_sz <= 0.0f) {
        b.has_ask = false;
        b.ask_px = std::numeric_limits<float>::infinity();
      }
    }

    // After updating top-of-book, refresh derived values:
    b.update_derived();
    b.push_ema();

    // Only act when both sides of book are present (valid bid & ask)
    if (b.has_bid && b.has_ask) {
      // 1. Aggressive sniping: take any obvious mispricing immediately
      try_snipe(k);
      // 2. Passive quoting: update our quotes based on new market state
      Targets targets = compute_targets(k);
      try_requote(k, targets);
    }
    // If one side of the market is empty (no bid or no ask), we hold off actions until it repopulates,
    // because fair value is uncertain. Our quotes from before might remain, but strategy can choose to cancel if needed.
  }

  // Called whenever one of *our* orders (passive quotes) is fully or partially filled.
  // Updates our inventory and remaining cash, and handles inventory-based quote removal.
  void on_account_update(Ticker ticker, Side side, float price, float quantity, float capital_remaining) {
    int k = static_cast<int>(ticker);
    capital_remaining_ = capital_remaining;
    // Update inventory: buy fills add positive inventory, sell fills subtract
    pos_[k] += (side == Side::buy ? quantity : -quantity);

    // If we hit hard inventory limits due to this fill, cancel the opposing quote immediately to stop further accumulation.
    if (pos_[k] >=  INVENTORY_HARD && quotes_[k].id_bid) {
      cancel_order(ticker, quotes_[k].id_bid);
      quotes_[k].id_bid = 0;
    }
    if (pos_[k] <= -INVENTORY_HARD && quotes_[k].id_ask) {
      cancel_order(ticker, quotes_[k].id_ask);
      quotes_[k].id_ask = 0;
    }
    // (The next on_orderbook_update will recalc and possibly place new quotes on the allowed side)
  }
};
