# NUTC 2025 - High-Frequency Trading Strategy

Algorithmic trading implementation for the Northwestern Trading Competition's HFT and Crypto cases.

## Overview

This project implements a sophisticated high-frequency trading strategy in C++20 designed for the Northwestern Trading Competition. The strategy combines market making with opportunistic sniping, featuring advanced inventory management and momentum following capabilities.

## Strategy Features

### Core Components

- **Market Making**: Provides liquidity by continuously quoting both bid and ask prices
- **Stale Quote Sniping**: Identifies and exploits mispriced orders using IOC (Immediate-or-Cancel) orders
- **Momentum Following**: Detects large trades and follows momentum with supportive order book imbalance
- **Inventory Management**: Dynamic position sizing and quote skewing based on current inventory levels

### Key Parameters

- **Capital**: $100,000 starting capital
- **Supported Assets**: ETH, BTC, LTC
- **Tick Size**: $0.01 minimum price increment
- **Inventory Limits**: 
  - Soft limit: ±2,000 units (begins quote skewing)
  - Hard limit: ±3,000 units (stops quoting that side)
- **Quote Sizes**: Up to 200 units per side
- **Snipe Sizes**: Up to 500 units for IOC orders

### Strategy Logic

1. **Fair Value Calculation**: Uses size-weighted microprice based on opposite side depth
2. **Quote Pricing**: Edges away from fair value with inventory-based skewing
3. **Risk Management**: Scales down quote sizes as inventory approaches limits
4. **Adverse Selection Protection**: Fades quotes during extreme order book imbalance
5. **Momentum Detection**: Follows large prints (>2,000 units) with supportive imbalance

## Technical Implementation

### Architecture

- **Language**: C++20 with modern features
- **Memory Management**: Stack-allocated arrays for low latency
- **Order Management**: Maintains active quote tracking with cancel/replace logic
- **State Management**: Per-ticker book state with EMA-based momentum indicators

### Key Classes

- `Strategy`: Main strategy class implementing all trading logic
- `Book`: Per-ticker order book state and derived metrics
- `Quote`: Active order tracking for bid/ask quotes

### API Integration

The strategy implements the required interface from `templateHFT.hpp`:
- `place_market_order()`: Market order execution
- `place_limit_order()`: Limit order placement with IOC support
- `cancel_order()`: Order cancellation
- Event callbacks: `on_trade_update()`, `on_orderbook_update()`, `on_account_update()`

## Usage

1. Compile the strategy with a C++20 compatible compiler
2. Integrate with the NUTC exchange harness
3. The strategy will automatically begin market making and opportunistic trading

## Competition Notes

- **No Trading Fees**: Strategy optimized for fee-free environment
- **Shared Order Book**: All participants see the same market data
- **Rate Limiting**: Strategy respects exchange rate limits
- **No Leverage**: Cash-only trading with $100k capital constraint

## Performance Considerations

- **Low Latency**: Optimized for minimal execution delay
- **CPU Efficient**: Avoids dynamic allocation during trading
- **Memory Bounded**: Fixed-size data structures for predictable performance
- **Rate Limit Aware**: Conservative order management to avoid throttling

## References

- NUTC Case Packet (HFT section specifications)
- Traders@MIT 2019 strategies for momentum and microprice concepts
- Template HFT interface and order management APIs
