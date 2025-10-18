# Northwestern Trading Contest 2025

## Project Overview

This repository contains trading strategies developed for the Northwestern Trading Contest (NUTC) 2025. The project implements sophisticated high-frequency trading (HFT) and cryptocurrency trading algorithms using C++20, focusing on market making, sniping, and momentum following strategies.

## Strategy Components

### 1. Template Framework (`template.hpp`)
- **Purpose**: Competition-provided base template with trading API interface
- **Source**: Provided by NUTC organizers
- **Features**:
  - Market and limit order placement functions
  - Order cancellation capabilities
  - Strategy class with callback methods for trade updates, orderbook updates, and account updates
  - Support for ETH, BTC, and LTC trading pairs
  - Logging functionality for debugging

### 2. HFT Strategy (`StrategyHFT.hpp`)
- **Focus**: High-frequency trading with no fees, shared order book
- **Key Features**:
  - **Market Making**: Sophisticated quoting with inventory-aware skewing
  - **Sniping**: Opportunistic IOC (Immediate or Cancel) orders when top-of-book is stale
  - **Momentum Following**: Large print detection and momentum-based trading
  - **Risk Management**: Hard and soft inventory limits with position-based quote adjustments
  - **Fair Value Calculation**: Size-weighted microprice for accurate fair value estimation
  - **Order Book Imbalance (OBI)**: Adverse selection protection through imbalance monitoring

### 3. Crypto Strategy (`StrategyCrypto.hpp`)
- **Focus**: Cryptocurrency trading with 0.4% fees per fill (~0.8% round-trip)
- **Key Features**:
  - **Fee-Aware Trading**: All strategies account for transaction costs
  - **Enhanced Risk Controls**: Fee guards prevent unprofitable trades
  - **Crypto-Specific Optimizations**: Tailored for cryptocurrency market dynamics
  - **Inventory Management**: Advanced position sizing and risk controls
  - **Momentum Detection**: Big-print momentum following with imbalance requirements

## Technical Implementation

### Core Algorithms
1. **Fair Value Calculation**: Size-weighted microprice using opposite side size weighting
2. **Inventory Skewing**: Dynamic quote adjustment based on current position
3. **Momentum Detection**: EMA-based trend following with large print triggers
4. **Adverse Selection Protection**: OBI-based quote fading to avoid toxic flow
5. **Risk Management**: Multi-tier inventory limits with automatic quote adjustments

### Key Parameters
- **Inventory Limits**: Soft (2000) and Hard (3000) position limits
- **Quote Sizing**: Dynamic sizing based on order book depth
- **Edge Requirements**: Minimum edge floors and spread-based calculations
- **Momentum Thresholds**: Large print detection at 2000+ quantity
- **Fee Considerations**: 0.4% per fill in crypto strategy

### Performance Optimizations
- **Low Latency**: Optimized for high-frequency execution
- **Memory Efficiency**: Fixed-size arrays and minimal allocations
- **Rate Limit Compliance**: Intelligent requoting to avoid excessive API calls
- **Price-Time Priority**: Respects exchange priority rules

## Strategy Logic Flow

1. **Order Book Updates**: Monitor top-of-book changes and update fair value
2. **Sniping**: Check for stale quotes and execute profitable IOC orders
3. **Market Making**: Place/update limit orders with inventory-aware pricing
4. **Momentum Following**: React to large prints with directional trades
5. **Risk Management**: Continuously monitor and adjust positions

## File Structure

```
├── template.hpp          # Competition-provided trading API template
├── StrategyHFT.hpp      # High-frequency trading strategy (our implementation)
├── StrategyCrypto.hpp   # Cryptocurrency trading strategy (our implementation)
└── README.md            # Project documentation
```

## Usage

Each strategy file contains a complete `Strategy` class that can be compiled and run in the NUTC trading environment. The strategies are designed to be:

- **Self-contained**: No external dependencies beyond the provided API
- **Configurable**: Tunable parameters for different market conditions
- **Robust**: Comprehensive error handling and risk management
- **Efficient**: Optimized for low-latency execution

## Key Features

- **Multi-Asset Support**: ETH, BTC, and LTC trading
- **Advanced Market Making**: Inventory-aware quoting with dynamic pricing
- **Opportunistic Trading**: Sniping and momentum following capabilities
- **Risk Management**: Multi-tier position limits and adverse selection protection
- **Fee Optimization**: Crypto-specific fee-aware trading logic
- **Performance Focused**: Low-latency, high-frequency execution

## Development Notes

- Built for C++20 compatibility
- Follows NUTC case packet specifications
- Implements senior-level trading strategies
- References Traders@MIT 2019 methodologies
- Designed for competitive trading environments

This project represents a comprehensive approach to algorithmic trading, combining market making, momentum following, and risk management in both fee-free (HFT) and fee-aware (Crypto) trading environments.
