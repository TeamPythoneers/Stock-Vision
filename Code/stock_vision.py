# ============================================================
# StockVision - Stock Analyzer & Trading Simulator (GUI)
# Enhanced with Smart Money Concepts (SMC) Analysis
# ============================================================
# Install: pip install yfinance pandas matplotlib requests numpy

from __future__ import annotations

import datetime
import json
import webbrowser
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import matplotlib.dates as mdates
import matplotlib.patches as mpatches
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import tkinter as tk
import yfinance as yf
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from tkinter import messagebox, ttk


# ============================================================
# COLORS & FONTS
# ============================================================
BG_COLOR = "#f8fafc"
CARD_COLOR = "#ffffff"
CARD2_COLOR = "#e2e8f0"
ACCENT_COLOR = "#0ea5e9"
ACCENT2_COLOR = "#0284c7"
GREEN_COLOR = "#22c55e"
RED_COLOR = "#ef4444"
YELLOW_COLOR = "#f59e0b"
PURPLE_COLOR = "#8b5cf6"
ORANGE_COLOR = "#f97316"
TEXT_COLOR = "#0f172a"
SUBTEXT_COLOR = "#64748b"
BORDER_COLOR = "#cbd5e1"
FONT_BIG = ("Helvetica", 28, "bold")
FONT_HEADING = ("Helvetica", 13, "bold")
FONT_BODY = ("Helvetica", 11)
FONT_SMALL = ("Helvetica", 9)
FONT_TINY = ("Helvetica", 8)

# ============================================================
# SYMBOL RESOLVER
# ============================================================
INDEX_MAP = {
    "NASDAQ": "^IXIC",
    "NASDAQ100": "^NDX",
    "NDX": "^NDX",
    "DOW": "^DJI",
    "DOWJONES": "^DJI",
    "DJI": "^DJI",
    "SP500": "^GSPC",
    "S&P500": "^GSPC",
    "S&P": "^GSPC",
    "GSPC": "^GSPC",
    "VIX": "^VIX",
    "RUSSELL2000": "^RUT",
    "RUT": "^RUT",
    "NIFTY": "^NSEI",
    "NIFTY50": "^NSEI",
    "SENSEX": "^BSESN",
    "BANKNIFTY": "^NSEBANK",
    "NIKKEI": "^N225",
    "NIKKEI225": "^N225",
    "FTSE": "^FTSE",
    "FTSE100": "^FTSE",
    "DAX": "^GDAXI",
    "CAC40": "^FCHI",
    "HANGSENG": "^HSI",
    "HSI": "^HSI",
    "ASX200": "^AXJO",
    "ASX": "^AXJO",
    "SSE": "000001.SS",
}

FOREX_SUFFIXES = {
    "USD",
    "EUR",
    "GBP",
    "JPY",
    "AUD",
    "CAD",
    "CHF",
    "NZD",
    "HKD",
    "SGD",
    "INR",
    "CNY",
    "MXN",
    "ZAR",
    "NOK",
    "SEK",
    "DKK",
    "TRY",
    "BRL",
    "RUB",
    "KRW",
}

CRYPTO_MAP = {
    "BITCOIN": "BTC-USD",
    "BTC": "BTC-USD",
    "ETHEREUM": "ETH-USD",
    "ETH": "ETH-USD",
    "DOGECOIN": "DOGE-USD",
    "DOGE": "DOGE-USD",
    "SOLANA": "SOL-USD",
    "SOL": "SOL-USD",
    "RIPPLE": "XRP-USD",
    "XRP": "XRP-USD",
    "CARDANO": "ADA-USD",
    "ADA": "ADA-USD",
    "LITECOIN": "LTC-USD",
    "LTC": "LTC-USD",
    "BNBCOIN": "BNB-USD",
    "BNB": "BNB-USD",
    "AVAX": "AVAX-USD",
    "AVALANCHE": "AVAX-USD",
    "MATIC": "MATIC-USD",
    "POLYGON": "MATIC-USD",
    "SHIB": "SHIB-USD",
}

ASSET_TYPE_LABELS = {
    "stock": "Stock",
    "index": "Index",
    "forex": "Forex Pair",
    "crypto": "Cryptocurrency",
    "etf": "ETF",
}

TIMEFRAME_OPTIONS = ["1mo", "3mo", "6mo", "1y", "1m", "3m", "5m", "15m", "30m", "1h", "4h"]
TIMEFRAME_FETCH_MAP = {
    # Swing / positional
    "1mo": {"period": "1mo", "interval": "1d", "label": "1 Month"},
    "3mo": {"period": "3mo", "interval": "1d", "label": "3 Months"},
    "6mo": {"period": "6mo", "interval": "1d", "label": "6 Months"},
    "1y": {"period": "1y", "interval": "1d", "label": "1 Year"},
    # Intraday
    "1m": {"period": "7d", "interval": "1m", "label": "1 Minute"},
    "3m": {"period": "7d", "interval": "1m", "resample": "3min", "label": "3 Minutes"},
    "5m": {"period": "60d", "interval": "5m", "label": "5 Minutes"},
    "15m": {"period": "60d", "interval": "15m", "label": "15 Minutes"},
    "30m": {"period": "60d", "interval": "30m", "label": "30 Minutes"},
    "1h": {"period": "730d", "interval": "60m", "label": "1 Hour"},
    "4h": {"period": "730d", "interval": "60m", "resample": "4h", "label": "4 Hours"},
}


def resolve_symbol(raw: str) -> Tuple[str, str]:
    s = raw.upper().strip().replace(" ", "").replace("/", "")
    if s in INDEX_MAP:
        return INDEX_MAP[s], "index"
    if s.startswith("^"):
        return s, "index"
    if s in CRYPTO_MAP:
        return CRYPTO_MAP[s], "crypto"
    if s.endswith("-USD") or s.endswith("-USDT"):
        return s, "crypto"
    if s.endswith("=X"):
        return s, "forex"
    if len(s) == 6:
        base, quote = s[:3], s[3:]
        if base in FOREX_SUFFIXES and quote in FOREX_SUFFIXES:
            return f"{s}=X", "forex"
    if s in ("XAUUSD", "XAGUSD", "XPTUSD", "XPDUSD"):
        return f"{s}=X", "forex"
    if s.endswith(".NS") or s.endswith(".BO"):
        return s, "stock"
    return s, "stock"


def get_asset_currency(info: Dict[str, Any], asset_type: str) -> str:
    return str(info.get("currency", "USD"))


class SmartMoneyAnalyzer:
    """
    Analyzes price data using Smart Money Concepts:
    - IOP (Imbalance of Power) — candle anatomy
    - Supply & Demand Zones   — institutional footprints
    - FVG / BAG               — price gaps & inefficiencies
    - Liquidity               — stop hunts, grabs, sweeps
    """

    def __init__(self, data: pd.DataFrame):
        self.data = data.copy()
        self.results = {}

    def analyze_all(self):
        self._analyze_iop()
        self._analyze_supply_demand()
        self._analyze_fvg_bag()
        self._analyze_liquidity()
        self._generate_smc_summary()
        return self.results

    # ──────────────────────────────────────────────
    # 1. IOP — Imbalance of Power (candle anatomy)
    # ──────────────────────────────────────────────
    def _analyze_iop(self):
        df = self.data
        last = df.iloc[-1]

        o, h, l, c = last["Open"], last["High"], last["Low"], last["Close"]
        rng = max(h - l, 1e-9)  # FIX: ensure non-zero range

        body = abs(c - o)
        upper_wick = h - max(o, c)
        lower_wick = min(o, c) - l
        close_pct = (body / rng) * 100
        is_green = c >= o

        if close_pct >= 70:
            candle_type = "TREND CANDLE 🔥"
            if is_green:
                power = "Strong BULLISH Power 🟢"
                power_note = "Buyers controlled 70%+ of the candle range. Institutional footprint."
            else:
                power = "Strong BEARISH Power 🔴"
                power_note = "Sellers controlled 70%+ of the candle range. Institutional footprint."
        elif close_pct <= 40:
            candle_type = "INDECISION / WEAK 😐"
            power = "Conflicted — WAIT ⚖️"
            power_note = "Long wicks, small body. Both sides fought — no clear winner. Don't trade indecision."
        else:
            candle_type = "MODERATE CANDLE"
            if is_green and upper_wick > body * 0.7:
                power = "Hidden BEARISH Power ⚠️"
                power_note = "Green candle but huge upper wick — sellers entered aggressively."
            elif not is_green and lower_wick > body * 0.7:
                power = "Hidden BULLISH Power 💡"
                power_note = "Red candle but huge lower wick — buyers defended hard."
            elif is_green:
                power = "Moderate Bullish 📗"
                power_note = "Buyers in control but without conviction."
            else:
                power = "Moderate Bearish 📕"
                power_note = "Sellers in control but without full dominance."

        liq_signal = ""
        if len(df) >= 6:
            prev_low = df["Low"].iloc[-6:-1].min()
            prev_high = df["High"].iloc[-6:-1].max()
            if l < prev_low and c > prev_low:
                liq_signal = (
                    "🪤 Stop-Hunt Below! Wick pierced prior lows but closed back "
                    "— possible BULLISH reversal trap."
                )
            elif h > prev_high and c < prev_high:
                liq_signal = (
                    "🪤 Stop-Hunt Above! Wick pierced prior highs but closed back "
                    "— possible BEARISH reversal trap."
                )

        self.results["iop"] = {
            "candle_type": candle_type,
            "power": power,
            "power_note": power_note,
            "close_pct": close_pct,
            "upper_wick": upper_wick,
            "lower_wick": lower_wick,
            "body": body,
            "is_green": is_green,
            "liq_signal": liq_signal,
        }

    # ──────────────────────────────────────────────
    # 2. Supply & Demand Zones
    # ──────────────────────────────────────────────
    def _analyze_supply_demand(self):
        df = self.data
        n = len(df)

        opens = df["Open"].values
        highs = df["High"].values
        lows = df["Low"].values
        closes = df["Close"].values

        zones = []
        for i in range(2, n - 2):
            o, h, l, c = opens[i], highs[i], lows[i], closes[i]

            next_body = abs(closes[i + 1] - opens[i + 1])
            this_body = abs(c - o)
            explosive = next_body > this_body * 1.3 or next_body > (h - l) * 0.6

            prev_rng = highs[i - 1] - lows[i - 1]
            this_rng = h - l
            tight_base = this_rng < prev_rng * 0.7

            if not explosive or not tight_base:
                continue

            prev_c = closes[i - 1]
            next_c = closes[i + 1]

            if prev_c < o and next_c > c:
                pattern = "DBR" if closes[i - 2] < prev_c else "RBR"
                zone_type = "DEMAND"
                zone_top = max(o, c)
                zone_bottom = min(o, c)
            elif prev_c > o and next_c < c:
                pattern = "RBD" if closes[i - 2] > prev_c else "DBD"
                zone_type = "SUPPLY"
                zone_top = max(o, c)
                zone_bottom = min(o, c)
            else:
                continue

            future_lows = lows[i + 2:]
            future_highs = highs[i + 2:]
            times_tested = int(
                np.sum((future_lows <= zone_top) & (future_highs >= zone_bottom))
            )

            if times_tested == 0:
                freshness = "🆕 Fresh (Full Strength)"
            elif times_tested == 1:
                freshness = "⚡ Tested Once (Still Valid)"
            elif times_tested == 2:
                freshness = "⚠️ Tested Twice (Weakening)"
            else:
                freshness = "❌ Exhausted (Avoid)"

            current_price = closes[-1]
            proximity = abs(current_price - (zone_top + zone_bottom) / 2)
            zone_width = max(zone_top - zone_bottom, 1e-9)
            near = proximity < zone_width * 3

            zones.append(
                {
                    "type": zone_type,
                    "pattern": pattern,
                    "top": zone_top,
                    "bottom": zone_bottom,
                    "times_tested": times_tested,
                    "freshness": freshness,
                    "near": near,
                    "idx": i,
                    "date": df.index[i],
                }
            )

        demand_zones = [z for z in zones if z["type"] == "DEMAND"][-3:]
        supply_zones = [z for z in zones if z["type"] == "SUPPLY"][-3:]

        current_price = closes[-1]
        nearest_demand = (
            min(demand_zones, key=lambda z: abs(current_price - z["top"]))
            if demand_zones
            else None
        )
        nearest_supply = (
            min(supply_zones, key=lambda z: abs(current_price - z["bottom"]))
            if supply_zones
            else None
        )

        self.results["sd"] = {
            "demand_zones": demand_zones,
            "supply_zones": supply_zones,
            "nearest_demand": nearest_demand,
            "nearest_supply": nearest_supply,
            "all_zones": demand_zones + supply_zones,
        }

    # ──────────────────────────────────────────────
    # 3. FVG & BAG — Gap Analysis
    # ──────────────────────────────────────────────
    def _analyze_fvg_bag(self):
        df = self.data
        n = len(df)

        highs = df["High"].values
        lows = df["Low"].values
        opens = df["Open"].values
        closes = df["Close"].values

        high_roll = pd.Series(highs).rolling(20).mean().values
        low_roll = pd.Series(lows).rolling(20).mean().values

        gaps = []
        for i in range(1, n - 1):
            c1_high = highs[i - 1]
            c1_low = lows[i - 1]
            c3_high = highs[i + 1]
            c3_low = lows[i + 1]
            c2_body = abs(closes[i] - opens[i])
            c2_rng = max(highs[i] - lows[i], 1e-9)  # FIX: guard zero division
            momentum = c2_body / c2_rng

            avg_rng = max((high_roll[i] or 0) - (low_roll[i] or 0), 1e-9)

            if c3_low > c1_high:
                gap_mid = (c1_high + c3_low) / 2
                is_bag = momentum > 0.75 and c2_rng > avg_rng
                gap_type = "BAG 💥" if is_bag else "FVG 🟡"
                filled = bool(np.any(lows[i + 2:] <= c1_high))
                gaps.append(
                    {
                        "type": gap_type,
                        "direction": "BULLISH",
                        "top": c3_low,
                        "bottom": c1_high,
                        "mid": gap_mid,
                        "filled": filled,
                        "is_bag": is_bag,
                        "idx": i,
                        "date": df.index[i],
                    }
                )

            elif c3_high < c1_low:
                gap_mid = (c1_low + c3_high) / 2
                is_bag = momentum > 0.75 and c2_rng > avg_rng
                gap_type = "BAG 💥" if is_bag else "FVG 🟡"
                filled = bool(np.any(highs[i + 2:] >= c1_low))
                gaps.append(
                    {
                        "type": gap_type,
                        "direction": "BEARISH",
                        "top": c1_low,
                        "bottom": c3_high,
                        "mid": gap_mid,
                        "filled": filled,
                        "is_bag": is_bag,
                        "idx": i,
                        "date": df.index[i],
                    }
                )

        unfilled = [g for g in gaps if not g["filled"]][-6:]
        recent_all = gaps[-8:]
        current_price = closes[-1]
        nearby_gaps = [
            g
            for g in unfilled
            if abs(current_price - g["mid"]) / max(current_price, 1e-9) < 0.08
        ]

        self.results["fvg"] = {
            "all_gaps": recent_all,
            "unfilled": unfilled,
            "nearby": nearby_gaps,
        }

    # ──────────────────────────────────────────────
    # 4. Liquidity Analysis — Stop Hunts / Sweeps
    # ──────────────────────────────────────────────
    def _analyze_liquidity(self):
        df = self.data
        n = len(df)
        hunts = []

        highs = df["High"].values
        lows = df["Low"].values
        closes = df["Close"].values
        opens = df["Open"].values

        for i in range(5, n - 1):
            window_highs = highs[i - 5:i]
            window_lows = lows[i - 5:i]
            prev_high = window_highs.max()
            prev_low = window_lows.min()

            cur_h, cur_l, cur_c, cur_o = highs[i], lows[i], closes[i], opens[i]

            if cur_h > prev_high and cur_c < prev_high:
                wick_size = cur_h - max(cur_o, cur_c)
                body_size = max(abs(cur_c - cur_o), 1e-9)
                if wick_size > body_size * 0.5:
                    hunts.append(
                        {
                            "type": "BEARISH HUNT 🔴",
                            "level": prev_high,
                            "wick": wick_size,
                            "idx": i,
                            "date": df.index[i],
                            "note": "Price spiked above highs (grabbed buy stops) then snapped back.",
                        }
                    )

            if cur_l < prev_low and cur_c > prev_low:
                wick_size = min(cur_o, cur_c) - cur_l
                body_size = max(abs(cur_c - cur_o), 1e-9)
                if wick_size > body_size * 0.5:
                    hunts.append(
                        {
                            "type": "BULLISH HUNT 🟢",
                            "level": prev_low,
                            "wick": wick_size,
                            "idx": i,
                            "date": df.index[i],
                            "note": "Price spiked below lows (grabbed sell stops) then snapped back.",
                        }
                    )

        recent_hunts = hunts[-5:]

        tol = (highs.max() - lows.min()) * 0.005
        eq_highs, eq_lows = [], []

        for i in range(len(highs) - 5):
            j_range = range(i + 2, min(i + 10, len(highs)))
            for j in j_range:
                if abs(highs[i] - highs[j]) < tol:
                    eq_highs.append(
                        {"level": (highs[i] + highs[j]) / 2, "date1": df.index[i], "date2": df.index[j]}
                    )
                if abs(lows[i] - lows[j]) < tol:
                    eq_lows.append(
                        {"level": (lows[i] + lows[j]) / 2, "date1": df.index[i], "date2": df.index[j]}
                    )

        def dedup(levels, key="level", tol_pct=0.005):
            seen = []
            for lv in levels:
                ref = max(lv[key], 1e-9)
                if not any(abs(lv[key] - s[key]) / ref < tol_pct for s in seen):
                    seen.append(lv)
            return seen[-3:]

        eq_highs = dedup(eq_highs)
        eq_lows = dedup(eq_lows)

        sweep_detected = ""
        recent_n = min(10, n)
        recent_slice = df.iloc[-recent_n:]
        last_window_highs = highs[max(n - 10, 0):n - 1]
        last_window_lows = lows[max(n - 10, 0):n - 1]

        if len(last_window_highs) > 0 and len(last_window_lows) > 0:
            highs_breached = int(np.sum(recent_slice["High"].max() > last_window_highs))
            lows_breached = int(np.sum(recent_slice["Low"].min() < last_window_lows))

            if highs_breached >= 3 and recent_slice["Close"].iloc[-1] < recent_slice["High"].max() * 0.995:
                sweep_detected = (
                    "⚠️ Potential BEARISH SWEEP detected — price pushed above multiple highs recently. "
                    "Watch for explosive reversal."
                )
            elif lows_breached >= 3 and recent_slice["Close"].iloc[-1] > recent_slice["Low"].min() * 1.005:
                sweep_detected = (
                    "⚠️ Potential BULLISH SWEEP detected — price pushed below multiple lows recently. "
                    "Watch for explosive reversal."
                )

        self.results["liquidity"] = {
            "recent_hunts": recent_hunts,
            "eq_highs": eq_highs,
            "eq_lows": eq_lows,
            "sweep_detected": sweep_detected,
        }

    # ──────────────────────────────────────────────
    # 5. SMC Summary — Combined Signal
    # ──────────────────────────────────────────────
    def _generate_smc_summary(self):
        iop = self.results.get("iop", {})
        sd = self.results.get("sd", {})
        fvg = self.results.get("fvg", {})
        liq = self.results.get("liquidity", {})
        cp = self.data["Close"].iloc[-1]

        bullish_signals = 0
        bearish_signals = 0
        signals = []

        power = iop.get("power", "")
        if "BULLISH" in power:
            bullish_signals += 2
            signals.append("✅ IOP: Bullish power on latest candle")
        elif "BEARISH" in power:
            bearish_signals += 2
            signals.append("❌ IOP: Bearish power on latest candle")

        if iop.get("liq_signal"):
            if "BULLISH" in iop["liq_signal"]:
                bullish_signals += 1
                signals.append("✅ Liquidity: Bullish stop-hunt detected")
            elif "BEARISH" in iop["liq_signal"]:
                bearish_signals += 1
                signals.append("❌ Liquidity: Bearish stop-hunt detected")

        nd = sd.get("nearest_demand")
        ns = sd.get("nearest_supply")
        if nd and cp <= nd["top"] * 1.02 and "Exhausted" not in nd["freshness"]:
            bullish_signals += 2
            signals.append(f"✅ S&D: Price near fresh DEMAND zone ({nd['pattern']})")
        if ns and cp >= ns["bottom"] * 0.98 and "Exhausted" not in ns["freshness"]:
            bearish_signals += 2
            signals.append(f"❌ S&D: Price near fresh SUPPLY zone ({ns['pattern']})")

        for g in fvg.get("nearby", []):
            if g["direction"] == "BULLISH" and not g["is_bag"]:
                bullish_signals += 1
                signals.append("✅ FVG: Unfilled bullish gap nearby — magnet above")
            elif g["direction"] == "BEARISH" and not g["is_bag"]:
                bearish_signals += 1
                signals.append("❌ FVG: Unfilled bearish gap nearby — magnet below")

        sw = liq.get("sweep_detected", "")
        if "BULLISH SWEEP" in sw:
            bullish_signals += 1
            signals.append("✅ Liquidity: Bullish sweep setup forming")
        elif "BEARISH SWEEP" in sw:
            bearish_signals += 1
            signals.append("❌ Liquidity: Bearish sweep setup forming")

        total = bullish_signals + bearish_signals
        if total == 0:
            verdict = "⚪ Neutral — No clear SMC signal"
            verdict_color = "yellow"
        elif bullish_signals > bearish_signals * 1.5:
            verdict = "🟢 SMC BULLISH BIAS — Smart money footprint favors LONG"
            verdict_color = "green"
        elif bearish_signals > bullish_signals * 1.5:
            verdict = "🔴 SMC BEARISH BIAS — Smart money footprint favors SHORT"
            verdict_color = "red"
        else:
            verdict = "🟡 SMC MIXED — Conflicting signals, wait for confirmation"
            verdict_color = "yellow"

        self.results["summary"] = {
            "verdict": verdict,
            "verdict_color": verdict_color,
            "signals": signals,
            "bullish_count": bullish_signals,
            "bearish_count": bearish_signals,
        }

    # ──────────────────────────────────────────────
    # SMC Chart Overlay
    # ──────────────────────────────────────────────
    def draw_smc_chart(self, ax, data: pd.DataFrame, asset_type: str = "stock", x_num: Optional[np.ndarray] = None):
        """FIX: Draw SMC overlays using the same numeric x-axis as all chart layers."""
        sd = self.results.get("sd", {})
        fvg = self.results.get("fvg", {})
        liq = self.results.get("liquidity", {})

        if x_num is None:
            try:
                x_num = mdates.date2num(pd.to_datetime(data.index).to_pydatetime())
            except Exception:
                x_num = np.arange(len(data), dtype=float)

        if len(x_num) == 0:
            return

        last_x = x_num[-1]

        for zone in sd.get("all_zones", []):
            color = "#22c55e" if zone["type"] == "DEMAND" else "#ef4444"
            alpha = 0.12 if "Fresh" in zone["freshness"] else 0.06
            ax.axhspan(zone["bottom"], zone["top"], alpha=alpha, color=color, linewidth=0)
            ax.axhline(zone["top"], color=color, linewidth=0.6, linestyle="--", alpha=0.5)
            ax.axhline(zone["bottom"], color=color, linewidth=0.6, linestyle="--", alpha=0.5)
            mid = (zone["top"] + zone["bottom"]) / 2
            label = f"{'D' if zone['type'] == 'DEMAND' else 'S'} ({zone['pattern']})"
            ax.annotate(label, xy=(last_x, mid), fontsize=6, color=color, alpha=0.8, ha="right", va="center")

        for gap in fvg.get("unfilled", [])[-4:]:
            ax.axhspan(gap["bottom"], gap["top"], alpha=0.10, color="#f59e0b", linewidth=0)
            mid = (gap["top"] + gap["bottom"]) / 2
            label = f"{'FVG' if not gap['is_bag'] else 'BAG'} {gap['direction'][:4]}"
            gap_idx = int(gap.get("idx", -1))
            gap_x = x_num[gap_idx] if 0 <= gap_idx < len(x_num) else last_x
            ax.annotate(label, xy=(gap_x, mid), fontsize=5.5, color="#b45309", alpha=0.85, ha="left", va="center")

        for eq in liq.get("eq_highs", []):
            ax.axhline(eq["level"], color="#8b5cf6", linewidth=0.8, linestyle=":", alpha=0.7)
            ax.annotate("EQH 💰", xy=(last_x, eq["level"]), fontsize=5.5, color="#8b5cf6", ha="right", va="bottom")

        for eq in liq.get("eq_lows", []):
            ax.axhline(eq["level"], color="#8b5cf6", linewidth=0.8, linestyle=":", alpha=0.7)
            ax.annotate("EQL 💰", xy=(last_x, eq["level"]), fontsize=5.5, color="#8b5cf6", ha="right", va="top")

        for hunt in liq.get("recent_hunts", [])[-3:]:
            idx = hunt["idx"]
            if 0 <= idx < len(x_num):
                color = "#22c55e" if "BULLISH" in hunt["type"] else "#ef4444"
                y = data["Low"].iloc[idx] if "BULLISH" in hunt["type"] else data["High"].iloc[idx]
                marker = "^" if "BULLISH" in hunt["type"] else "v"
                ax.scatter([x_num[idx]], [y], marker=marker, color=color, s=60, zorder=6, alpha=0.85)


# ============================================================
# IMPROVED: Market data cache for faster repeated requests
# ============================================================
class MarketDataCache:
    def __init__(self, ttl_seconds: int = 300, max_entries: int = 128):
        self.ttl_seconds = ttl_seconds
        self.max_entries = max_entries
        self._store: Dict[
            Tuple[str, str, str, str, str, str],
            Tuple[datetime.datetime, pd.DataFrame, Dict[str, Any], List[Dict[str, str]]],
        ] = {}

    def get(self, key: Tuple[str, str, str, str]):
        payload = self._store.get(key)
        if not payload:
            return None
        created_at, data, info, news = payload
        age = (datetime.datetime.now() - created_at).total_seconds()
        if age > self.ttl_seconds:
            self._store.pop(key, None)
            return None
        # FIX: return copies to avoid accidental mutation of cached objects.
        return data.copy(), dict(info), list(news)

    def set(self, key, data: pd.DataFrame, info: Dict[str, Any], news: List[Dict[str, str]]):
        if len(self._store) >= self.max_entries:
            oldest_key = min(self._store.keys(), key=lambda k: self._store[k][0])
            self._store.pop(oldest_key, None)
        self._store[key] = (datetime.datetime.now(), data.copy(), dict(info), list(news))


# ============================================================
# STYLED BUTTON HELPER
# ============================================================
def make_button(parent, text, command, bg=None, fg="white", width=None, height=None, font=None):
    btn = tk.Button(
        parent,
        text=text,
        command=command,
        bg=bg or ACCENT_COLOR,
        fg=fg,
        activebackground=CARD2_COLOR,
        activeforeground=TEXT_COLOR,
        font=font or FONT_BODY,
        relief="flat",
        cursor="hand2",
        bd=0,
        pady=6,
        padx=12,
    )
    if width:
        btn.config(width=width)
    if height:
        btn.config(height=height)
    return btn


# ============================================================
# MAIN APP
# ============================================================
class StockVisionApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("StockVision + SMC")
        self.root.geometry("1200x800")
        self.root.configure(bg=BG_COLOR)
        self.root.resizable(True, True)

        self.cache = MarketDataCache(ttl_seconds=300, max_entries=128)  # NEW: data caching
        self._smc_analyzer: Optional[SmartMoneyAnalyzer] = None
        self._about_url: str = ""
        self._active_canvas: Optional[FigureCanvasTkAgg] = None
        self._active_fig = None
        self._hover_payload: Optional[Dict[str, Any]] = None
        self._hover_cids: List[int] = []

        # NEW: Wishlist storage
        self.wishlist_path = Path(__file__).with_name("wishlist_symbols.json")
        self.wishlist_symbols = self._load_wishlist()

        self.show_home()

    def clear(self):
        self._disconnect_hover()
        for w in self.root.winfo_children():
            w.destroy()

    def make_card(self, parent, padx=16, pady=12, bg=None, **kwargs):
        outer = tk.Frame(parent, bg=BORDER_COLOR, padx=1, pady=1, **kwargs)
        inner = tk.Frame(outer, bg=bg or CARD_COLOR, padx=padx, pady=pady)
        inner.pack(fill="both", expand=True)
        return outer, inner

    # ============================================================
    # NEW: Wishlist helpers
    # ============================================================
    def _load_wishlist(self) -> List[str]:
        try:
            if self.wishlist_path.exists():
                data = json.loads(self.wishlist_path.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    clean: List[str] = []
                    for x in data:
                        sym = str(x).strip().upper()
                        if sym and sym not in clean:
                            clean.append(sym)
                    return clean[:50]
        except Exception:
            pass
        return []

    def _save_wishlist(self):
        try:
            self.wishlist_path.write_text(json.dumps(self.wishlist_symbols, indent=2), encoding="utf-8")
        except Exception as ex:
            messagebox.showwarning("Wishlist", f"Could not save wishlist: {ex}")

    def _refresh_wishlist_ui(self):
        if hasattr(self, "wishlist_combo"):
            self.wishlist_combo["values"] = self.wishlist_symbols
        self._render_wishlist_quick_buttons()

    def _render_wishlist_quick_buttons(self):
        if not hasattr(self, "wishlist_quick_frame"):
            return
        for w in self.wishlist_quick_frame.winfo_children():
            w.destroy()

        if not self.wishlist_symbols:
            tk.Label(
                self.wishlist_quick_frame,
                text="Quick Wishlist: add symbols to get 1-click buttons",
                font=FONT_TINY,
                bg=CARD_COLOR,
                fg=SUBTEXT_COLOR,
            ).pack(anchor="w")
            return

        tk.Label(self.wishlist_quick_frame, text="Quick Wishlist:", font=FONT_TINY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(side="left", padx=(0, 6))
        for sym in self.wishlist_symbols[:12]:
            tk.Button(
                self.wishlist_quick_frame,
                text=sym,
                font=FONT_TINY,
                bg=CARD2_COLOR,
                fg=TEXT_COLOR,
                relief="flat",
                cursor="hand2",
                padx=8,
                pady=2,
                command=lambda s=sym: self.open_wishlist_symbol_one_click(s),
            ).pack(side="left", padx=(0, 4))

        if len(self.wishlist_symbols) > 12:
            more = len(self.wishlist_symbols) - 12
            tk.Label(
                self.wishlist_quick_frame,
                text=f"+{more} more",
                font=FONT_TINY,
                bg=CARD_COLOR,
                fg=SUBTEXT_COLOR,
            ).pack(side="left", padx=(4, 0))

    def open_wishlist_symbol_one_click(self, symbol: str):
        if not symbol:
            return
        if hasattr(self, "wishlist_var"):
            self.wishlist_var.set(symbol)
        self.symbol_entry.delete(0, "end")
        self.symbol_entry.insert(0, symbol)
        self.run_analysis()

    def add_to_wishlist(self):
        # NEW: Wishlist
        raw = self.symbol_entry.get().strip().upper() if hasattr(self, "symbol_entry") else ""
        if not raw:
            messagebox.showwarning("Wishlist", "Enter a symbol first.")
            return
        if raw in self.wishlist_symbols:
            messagebox.showinfo("Wishlist", f"{raw} is already in wishlist.")
            return
        self.wishlist_symbols.append(raw)
        self.wishlist_symbols = sorted(set(self.wishlist_symbols))
        self._save_wishlist()
        self._refresh_wishlist_ui()
        self.wishlist_var.set(raw)

    def remove_from_wishlist(self):
        # NEW: Wishlist
        raw = self.wishlist_var.get().strip().upper()
        if not raw:
            messagebox.showwarning("Wishlist", "Select a symbol from wishlist.")
            return
        if raw in self.wishlist_symbols:
            self.wishlist_symbols.remove(raw)
            self._save_wishlist()
            self._refresh_wishlist_ui()
            self.wishlist_var.set("")

    def use_wishlist_symbol(self):
        # NEW: Wishlist
        raw = self.wishlist_var.get().strip().upper()
        if not raw:
            messagebox.showwarning("Wishlist", "Select a symbol from wishlist.")
            return
        self.open_wishlist_symbol_one_click(raw)

    # ============================================================
    # HOME SCREEN
    # ============================================================
    def show_home(self):
        self.clear()

        banner = tk.Frame(self.root, bg=CARD_COLOR, height=10)
        banner.pack(fill="x")
        tk.Frame(banner, bg=ACCENT_COLOR, height=3).pack(fill="x")

        center = tk.Frame(self.root, bg=BG_COLOR)
        center.pack(expand=True)

        logo_frame = tk.Frame(center, bg=BG_COLOR)
        logo_frame.pack(pady=(30, 5))
        tk.Label(logo_frame, text="📈", font=("Helvetica", 48), bg=BG_COLOR).pack()
        tk.Label(logo_frame, text="StockVision", font=("Helvetica", 36, "bold"), bg=BG_COLOR, fg=ACCENT_COLOR).pack()
        tk.Label(
            logo_frame,
            text="Stocks • Forex • Crypto • Indices — Smart Money Edition",
            font=FONT_BODY,
            bg=BG_COLOR,
            fg=SUBTEXT_COLOR,
        ).pack(pady=(4, 0))

        smc_badge = tk.Frame(center, bg="#1e293b", padx=14, pady=6)
        smc_badge.pack(pady=(8, 0))
        tk.Label(
            smc_badge,
            text="🧠  SMC Engine: IOP • Supply/Demand • FVG/BAG • Liquidity",
            font=FONT_SMALL,
            bg="#1e293b",
            fg="#94a3b8",
        ).pack()

        tk.Frame(center, bg=BORDER_COLOR, height=1, width=500).pack(pady=24)

        btn_frame = tk.Frame(center, bg=BG_COLOR)
        btn_frame.pack()

        a_card = tk.Frame(btn_frame, bg=CARD2_COLOR, padx=30, pady=20, cursor="hand2")
        a_card.grid(row=0, column=0, padx=15)
        tk.Label(a_card, text="📊", font=("Helvetica", 28), bg=CARD2_COLOR).pack()
        tk.Label(a_card, text="Stock Analyzer", font=FONT_HEADING, bg=CARD2_COLOR, fg=TEXT_COLOR).pack(pady=(4, 2))
        tk.Label(
            a_card,
            text="Stocks • Forex • Crypto\nIndices • SMC Analysis",
            font=FONT_TINY,
            bg=CARD2_COLOR,
            fg=SUBTEXT_COLOR,
            justify="center",
        ).pack()
        tk.Button(
            a_card,
            text="Open Analyzer →",
            font=FONT_SMALL,
            bg=ACCENT_COLOR,
            fg="white",
            relief="flat",
            cursor="hand2",
            command=self.show_analyzer,
        ).pack(pady=(12, 0))

        s_card = tk.Frame(btn_frame, bg=CARD2_COLOR, padx=30, pady=20, cursor="hand2")
        s_card.grid(row=0, column=1, padx=15)
        tk.Label(s_card, text="🎮", font=("Helvetica", 28), bg=CARD2_COLOR).pack()
        tk.Label(s_card, text="Trading Simulator", font=FONT_HEADING, bg=CARD2_COLOR, fg=TEXT_COLOR).pack(pady=(4, 2))
        tk.Label(s_card, text="Practice trading\nNo real money needed", font=FONT_TINY, bg=CARD2_COLOR, fg=SUBTEXT_COLOR, justify="center").pack()
        tk.Button(
            s_card,
            text="Open Simulator →",
            font=FONT_SMALL,
            bg=GREEN_COLOR,
            fg="white",
            relief="flat",
            cursor="hand2",
            command=self.show_simulator,
        ).pack(pady=(12, 0))

        hint_frame = tk.Frame(center, bg=BG_COLOR)
        hint_frame.pack(pady=(20, 0))
        tk.Label(
            hint_frame,
            text="Symbols: AAPL • EURUSD • BTC • NASDAQ • TCS.NS • NIFTY50",
            font=FONT_TINY,
            bg=BG_COLOR,
            fg=SUBTEXT_COLOR,
        ).pack()
        tk.Label(center, text="Real-time data powered by Yahoo Finance", font=FONT_TINY, bg=BG_COLOR, fg=SUBTEXT_COLOR).pack(pady=(10, 0))

    # ============================================================
    # ANALYZER SCREEN
    # ============================================================
    def show_analyzer(self):
        self.clear()
        self.make_topbar("📊 Stock Analyzer + Smart Money Concepts")

        search_bg = tk.Frame(self.root, bg=CARD_COLOR, pady=12)
        search_bg.pack(fill="x")

        search = tk.Frame(search_bg, bg=CARD_COLOR)
        search.pack()

        tk.Label(search, text="Symbol / Pair:", font=FONT_BODY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).grid(row=0, column=0, padx=(0, 6))

        self.symbol_entry = tk.Entry(
            search,
            font=("Helvetica", 13, "bold"),
            width=12,
            bg=BG_COLOR,
            fg=ACCENT_COLOR,
            insertbackground=ACCENT_COLOR,
            relief="flat",
            highlightthickness=1,
            highlightcolor=ACCENT_COLOR,
            highlightbackground=BORDER_COLOR,
        )
        self.symbol_entry.grid(row=0, column=1, padx=6, ipady=4)
        self.symbol_entry.insert(0, "AAPL")
        self.symbol_entry.bind("<Return>", lambda e: self.run_analysis())

        tk.Label(search, text="e.g. AAPL, EURUSD, BTC, NASDAQ, NIFTY50", font=FONT_TINY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).grid(
            row=1, column=1, sticky="w", pady=(2, 0)
        )

        tk.Label(search, text="Timeframe:", font=FONT_BODY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).grid(row=0, column=2, padx=(14, 6))

        self.period_var = tk.StringVar(value="3mo")
        period_cb = ttk.Combobox(search, textvariable=self.period_var, values=TIMEFRAME_OPTIONS, width=6, font=FONT_BODY, state="readonly")
        period_cb.grid(row=0, column=3, padx=6)

        self.smc_enabled = tk.BooleanVar(value=True)
        smc_chk = tk.Checkbutton(
            search,
            text="🧠 SMC Analysis",
            variable=self.smc_enabled,
            font=FONT_SMALL,
            bg=CARD_COLOR,
            fg=PURPLE_COLOR,
            selectcolor=CARD_COLOR,
            activebackground=CARD_COLOR,
            cursor="hand2",
        )
        smc_chk.grid(row=0, column=4, padx=10)

        tk.Button(
            search,
            text="  🔍  Analyze  ",
            font=FONT_HEADING,
            bg=ACCENT_COLOR,
            fg="white",
            activebackground=ACCENT2_COLOR,
            relief="flat",
            cursor="hand2",
            pady=4,
            command=self.run_analysis,
        ).grid(row=0, column=5, padx=14)

        # NEW: Wishlist
        tk.Label(search, text="Wishlist:", font=FONT_SMALL, bg=CARD_COLOR, fg=SUBTEXT_COLOR).grid(row=1, column=2, padx=(14, 4), sticky="e")
        self.wishlist_var = tk.StringVar()
        self.wishlist_combo = ttk.Combobox(search, textvariable=self.wishlist_var, values=self.wishlist_symbols, width=10, state="readonly", font=FONT_SMALL)
        self.wishlist_combo.grid(row=1, column=3, sticky="w")
        tk.Button(search, text="+ Save", font=FONT_TINY, bg=CARD2_COLOR, fg=TEXT_COLOR, relief="flat", cursor="hand2", command=self.add_to_wishlist).grid(
            row=1, column=4, padx=(10, 4), sticky="w"
        )
        tk.Button(search, text="Use", font=FONT_TINY, bg=ACCENT_COLOR, fg="white", relief="flat", cursor="hand2", command=self.use_wishlist_symbol).grid(
            row=1, column=5, padx=(0, 4), sticky="w"
        )
        tk.Button(search, text="Remove", font=FONT_TINY, bg="#fee2e2", fg="#b91c1c", relief="flat", cursor="hand2", command=self.remove_from_wishlist).grid(
            row=1, column=6, padx=(0, 4), sticky="w"
        )

        self.wishlist_quick_frame = tk.Frame(search, bg=CARD_COLOR)
        self.wishlist_quick_frame.grid(row=2, column=0, columnspan=8, sticky="w", pady=(8, 0))
        self._render_wishlist_quick_buttons()

        # NEW: Loading indicator
        self.analysis_loading_var = tk.StringVar(value="")
        self.analysis_loading_label = tk.Label(search, textvariable=self.analysis_loading_var, font=FONT_TINY, bg=CARD_COLOR, fg=SUBTEXT_COLOR)
        self.analysis_loading_label.grid(row=0, column=6, padx=8, sticky="w")
        self.analysis_progress = ttk.Progressbar(search, mode="indeterminate", length=100)
        self.analysis_progress.grid(row=0, column=7, padx=(0, 8), sticky="w")
        self.analysis_progress.grid_remove()

        main = tk.Frame(self.root, bg=BG_COLOR)
        main.pack(fill="both", expand=True, padx=14, pady=10)

        # Left panel
        left = tk.Frame(main, bg=CARD_COLOR, highlightthickness=1, highlightbackground=BORDER_COLOR)
        left.pack(side="left", fill="both", expand=False, padx=(0, 10))

        tab_bar = tk.Frame(left, bg=CARD2_COLOR)
        tab_bar.pack(fill="x")

        self._active_tab = tk.StringVar(value="stats")
        self._tab_btns: Dict[str, tk.Button] = {}

        def make_tab(label, key):
            btn = tk.Button(
                tab_bar,
                text=label,
                font=FONT_TINY,
                bg=ACCENT_COLOR if key == "stats" else CARD2_COLOR,
                fg="white" if key == "stats" else SUBTEXT_COLOR,
                relief="flat",
                cursor="hand2",
                pady=4,
                padx=8,
                command=lambda k=key: self.switch_tab(k),
            )
            btn.pack(side="left", padx=1, pady=2)
            self._tab_btns[key] = btn

        make_tab("📊 Stats", "stats")
        make_tab("🧠 SMC", "smc")

        content_frame = tk.Frame(left, bg=CARD_COLOR)
        content_frame.pack(fill="both", expand=True)

        self.result_text = tk.Text(
            content_frame,
            width=38,
            font=FONT_SMALL,
            bg=CARD_COLOR,
            fg=TEXT_COLOR,
            relief="flat",
            wrap="word",
            padx=14,
            pady=14,
            selectbackground=ACCENT2_COLOR,
            cursor="arrow",
        )
        scroll = ttk.Scrollbar(content_frame, command=self.result_text.yview)
        self.result_text.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        self.result_text.pack(fill="both", expand=True)

        self.more_about_btn = tk.Button(
            left,
            text="More About  →",
            font=FONT_SMALL,
            bg=CARD2_COLOR,
            fg=ACCENT_COLOR,
            activebackground=BORDER_COLOR,
            activeforeground=ACCENT_COLOR,
            relief="flat",
            cursor="hand2",
            pady=6,
            command=lambda: webbrowser.open(self._about_url) if self._about_url else None,
        )

        self.chart_frame = tk.Frame(main, bg=BG_COLOR)
        self.chart_frame.pack(side="right", fill="both", expand=True)

    def _set_analysis_loading(self, active: bool, text: str = ""):
        # NEW: Loading indicator
        if not hasattr(self, "analysis_progress"):
            return
        self.analysis_loading_var.set(text if active else "")
        if active:
            self.analysis_progress.grid()
            self.analysis_progress.start(10)
        else:
            self.analysis_progress.stop()
            self.analysis_progress.grid_remove()
        try:
            self.root.update_idletasks()
        except tk.TclError:
            pass

    def switch_tab(self, key):
        self._active_tab.set(key)
        for k, btn in self._tab_btns.items():
            if k == key:
                btn.config(bg=ACCENT_COLOR, fg="white")
            else:
                btn.config(bg=CARD2_COLOR, fg=SUBTEXT_COLOR)

        self.result_text.config(state="normal")
        self.result_text.delete("1.0", "end")
        if key == "stats" and hasattr(self, "_stats_content"):
            self._render_stats()
        elif key == "smc" and hasattr(self, "_smc_content"):
            self._render_smc()
        self.result_text.config(state="disabled")

    # ============================================================
    # Helpers for result text
    # ============================================================
    def _section(self, title):
        self.result_text.insert("end", "\n")
        self.result_text.insert("end", f"  {title}\n", "heading")
        self.result_text.insert("end", f"  {'─' * 34}\n", "sub")

    def _row(self, label, value, tag=None):
        self.result_text.insert("end", f"  {label:<22}", "sub")
        self.result_text.insert("end", f"{value}\n", tag)

    def _note(self, text, tag="sub"):
        self.result_text.insert("end", f"\n  💬 {text}\n", tag)

    def _setup_tags(self):
        self.result_text.tag_configure("accent", foreground=ACCENT_COLOR)
        self.result_text.tag_configure("green", foreground=GREEN_COLOR)
        self.result_text.tag_configure("red", foreground=RED_COLOR)
        self.result_text.tag_configure("yellow", foreground=YELLOW_COLOR)
        self.result_text.tag_configure("purple", foreground=PURPLE_COLOR)
        self.result_text.tag_configure("orange", foreground=ORANGE_COLOR)
        self.result_text.tag_configure("sub", foreground=SUBTEXT_COLOR)
        self.result_text.tag_configure("heading", foreground=ACCENT_COLOR, font=("Helvetica", 10, "bold"))
        self.result_text.tag_configure("smc_head", foreground=PURPLE_COLOR, font=("Helvetica", 10, "bold"))
        self.result_text.tag_configure("verdict_green", foreground=GREEN_COLOR, font=("Helvetica", 11, "bold"))
        self.result_text.tag_configure("verdict_red", foreground=RED_COLOR, font=("Helvetica", 11, "bold"))
        self.result_text.tag_configure("verdict_yellow", foreground=YELLOW_COLOR, font=("Helvetica", 11, "bold"))

    def _resolve_timeframe_request(self, timeframe: str) -> Dict[str, str]:
        key = str(timeframe).strip().lower()
        return dict(TIMEFRAME_FETCH_MAP.get(key, TIMEFRAME_FETCH_MAP["3mo"]))

    def _resample_ohlcv(self, data: pd.DataFrame, rule: str) -> pd.DataFrame:
        agg = {
            "Open": "first",
            "High": "max",
            "Low": "min",
            "Close": "last",
            "Volume": "sum",
        }
        use_agg = {k: v for k, v in agg.items() if k in data.columns}
        out = data.resample(rule, label="right", closed="right").agg(use_agg)
        out = out.dropna(subset=[c for c in ["Open", "High", "Low", "Close"] if c in out.columns])
        if "Volume" not in out.columns:
            out["Volume"] = 0.0
        else:
            out["Volume"] = out["Volume"].fillna(0.0)
        return out

    # ============================================================
    # IMPROVED: Data fetch with robust error handling + caching
    # ============================================================
    def _fetch_market_payload(
        self,
        symbol: str,
        period: Optional[str] = None,
        interval: Optional[str] = None,
        resample_rule: Optional[str] = None,
        start: Optional[datetime.date] = None,
        end: Optional[datetime.date] = None,
    ) -> Tuple[pd.DataFrame, Dict[str, Any], List[Dict[str, str]]]:
        cache_key = (
            symbol,
            period or "",
            interval or "",
            resample_rule or "",
            start.isoformat() if start else "",
            end.isoformat() if end else "",
        )
        cached = self.cache.get(cache_key)
        if cached is not None:
            return cached

        try:
            ticker = yf.Ticker(symbol)
            history_kwargs: Dict[str, Any] = {}
            if period:
                history_kwargs["period"] = period
            else:
                history_kwargs["start"] = start
                history_kwargs["end"] = end
            if interval:
                history_kwargs["interval"] = interval
            data = ticker.history(**history_kwargs)
        except Exception as ex:
            # FIX: clearer API/network error message
            raise RuntimeError(f"Yahoo Finance request failed for {symbol}: {ex}") from ex

        if data is None or data.empty:
            raise ValueError(f"No data found for '{symbol}'.")

        # FIX: standardize data frame shape and columns to avoid downstream crashes.
        data = data.copy().sort_index()
        data = data[~data.index.duplicated(keep="last")]
        if isinstance(data.columns, pd.MultiIndex):
            data.columns = [c[0] for c in data.columns]

        required = ["Open", "High", "Low", "Close"]
        missing = [col for col in required if col not in data.columns]
        if missing:
            raise ValueError(f"Incomplete market data for {symbol}. Missing columns: {missing}")

        for col in ["Open", "High", "Low", "Close", "Volume"]:
            if col in data.columns:
                data[col] = pd.to_numeric(data[col], errors="coerce")
        data = data.dropna(subset=["Open", "High", "Low", "Close"])
        if "Volume" not in data.columns:
            # FIX: avoid KeyError on assets where volume is missing
            data["Volume"] = 0.0
        else:
            data["Volume"] = data["Volume"].fillna(0.0)

        if resample_rule:
            data = self._resample_ohlcv(data, resample_rule)
            if data.empty:
                raise ValueError(f"No data available for {symbol} after applying {resample_rule} timeframe.")

        info: Dict[str, Any] = {}
        try:
            info = ticker.info or {}
        except Exception:
            info = {}

        news_items: List[Dict[str, str]] = []
        try:
            raw_news = ticker.news or []
            for item in raw_news[:4]:
                content = item.get("content", {}) if isinstance(item, dict) else {}
                title = str(content.get("title", "No title"))
                url = ""
                canonical = content.get("canonicalUrl", {})
                if isinstance(canonical, dict):
                    url = str(canonical.get("url", ""))
                news_items.append({"title": title, "url": url})
        except Exception:
            news_items = []

        self.cache.set(cache_key, data, info, news_items)
        return data, info, news_items

    def _prepare_indicators(self, data: pd.DataFrame) -> pd.DataFrame:
        # IMPROVED: single-pass indicator prep reused across analysis/rendering.
        out = data.copy()
        out["SMA_20"] = out["Close"].rolling(window=20, min_periods=20).mean()
        out["SMA_50"] = out["Close"].rolling(window=50, min_periods=50).mean()
        out["Daily_Change"] = out["Close"].pct_change() * 100

        delta = out["Close"].diff()
        gain = delta.clip(lower=0)
        loss = -delta.clip(upper=0)
        avg_gain = gain.rolling(window=14, min_periods=14).mean()
        avg_loss = loss.rolling(window=14, min_periods=14).mean()
        rs = avg_gain / avg_loss.replace(0, np.nan)
        out["RSI"] = 100 - (100 / (1 + rs))
        return out

    # ============================================================
    # RUN ANALYSIS
    # ============================================================
    def run_analysis(self):
        raw_input = self.symbol_entry.get().strip() if hasattr(self, "symbol_entry") else ""
        timeframe = self.period_var.get() if hasattr(self, "period_var") else "3mo"

        if not raw_input:
            messagebox.showwarning("Missing", "Please enter a symbol.")
            return

        symbol, asset_type = resolve_symbol(raw_input)
        tf_request = self._resolve_timeframe_request(timeframe)
        tf_label = tf_request.get("label", str(timeframe))

        self.result_text.config(state="normal")
        self.result_text.delete("1.0", "end")
        self.result_text.insert("end", f"\n  Loading data for {symbol} ({tf_label})...\n")
        self.result_text.config(state="disabled")
        self._set_analysis_loading(True, "Fetching market data...")

        try:
            data, info, news_items = self._fetch_market_payload(
                symbol=symbol,
                period=tf_request.get("period"),
                interval=tf_request.get("interval"),
                resample_rule=tf_request.get("resample"),
            )
            data = self._prepare_indicators(data)
        except Exception as ex:
            self._set_analysis_loading(False)
            messagebox.showerror("Error", str(ex))
            return

        # Standard calculations
        latest = float(data["Close"].iloc[-1])
        highest = float(data["High"].max())
        lowest = float(data["Low"].min())
        average = float(data["Close"].mean())
        open_p = float(data["Open"].iloc[-1])
        prev = float(data["Close"].iloc[-2]) if len(data) > 1 else latest
        change = latest - prev
        chg_pct = (change / prev) * 100 if prev != 0 else 0.0
        chg_sym = "▲" if change >= 0 else "▼"
        chg_col = "+" if change >= 0 else ""

        currency = get_asset_currency(info, asset_type)
        cur_sym = "₹" if currency == "INR" else "$" if currency == "USD" else f"{currency} "

        sma20 = data["SMA_20"].iloc[-1]
        sma50 = data["SMA_50"].iloc[-1]
        if pd.isna(sma20) or pd.isna(sma50):
            trend, trend_explain = "Insufficient data", "Not enough history for SMA trend."
        elif sma20 > sma50:
            trend, trend_explain = "Bullish (Uptrend)", "SMA 20 is above SMA 50."
        elif sma20 < sma50:
            trend, trend_explain = "Bearish (Downtrend)", "SMA 20 is below SMA 50."
        else:
            trend, trend_explain = "Neutral", "SMA lines are overlapping."

        volatility = float(data["Daily_Change"].std(skipna=True))
        if np.isnan(volatility):
            volatility = 0.0
        if volatility < 1.5:
            risk, risk_explain = "Low Risk", "Stable movement profile."
        elif volatility < 3:
            risk, risk_explain = "Medium Risk", "Moderate movement profile."
        else:
            risk, risk_explain = "High Risk", "Large movement profile."

        rsi = data["RSI"].iloc[-1]
        if pd.isna(rsi):
            rsi_status, rsi_explain = "N/A", "Not enough data."
        elif rsi > 70:
            rsi_status, rsi_explain = "Overbought", "Momentum is overheated."
        elif rsi < 30:
            rsi_status, rsi_explain = "Oversold", "Momentum may be exhausted downward."
        else:
            rsi_status, rsi_explain = "Normal", "Momentum is balanced."

        best_day = data["Daily_Change"].idxmax()
        worst_day = data["Daily_Change"].idxmin()
        best_val = float(data["Daily_Change"].max())
        worst_val = float(data["Daily_Change"].min())

        has_volume = bool("Volume" in data.columns and data["Volume"].fillna(0).sum() > 0)
        if has_volume:
            avg_vol = float(data["Volume"].mean())
            last_vol = float(data["Volume"].iloc[-1])
            if avg_vol <= 0:
                vol_status, vol_explain = "N/A", "Volume unavailable."
            elif last_vol > avg_vol * 1.5:
                vol_status, vol_explain = "Very High", "Heavy trading activity."
            elif last_vol < avg_vol * 0.5:
                vol_status, vol_explain = "Very Low", "Light trading activity."
            else:
                vol_status, vol_explain = "Normal", "Normal trading activity."
        else:
            vol_status, vol_explain = "N/A", "Volume not available for this asset."

        score = 0
        if not pd.isna(sma20) and not pd.isna(sma50) and sma20 > sma50:
            score += 1
        if not pd.isna(rsi) and rsi < 70:
            score += 1
        if not pd.isna(rsi) and rsi > 30:
            score += 1
        if volatility < 3:
            score += 1
        if change > 0:
            score += 1

        if score >= 4:
            rec, rec_explain = "Looks Positive", "Most signals align positively."
        elif score >= 2:
            rec, rec_explain = "Mixed Signals", "Wait for stronger confirmation."
        else:
            rec, rec_explain = "Looks Negative", "Most signals are weak or bearish."

        name = str(info.get("longName", info.get("shortName", symbol)))
        sector = str(info.get("sector", "N/A"))
        industry = str(info.get("industry", "N/A"))
        country = str(info.get("country", "N/A"))
        website = str(info.get("website", ""))
        mktcap = info.get("marketCap", None)
        pe = info.get("trailingPE", None)
        div = info.get("dividendYield", None)
        about = str(info.get("longBusinessSummary", ""))

        mktcap_str = f"${mktcap/1e9:.1f}B" if mktcap and mktcap >= 1e9 else f"${mktcap/1e6:.1f}M" if mktcap else "N/A"
        pe_str = f"{pe:.1f}x" if pe else "N/A"
        div_str = f"{div*100:.2f}%" if div else "None"

        # SMC analysis
        smc_results = None
        self._smc_analyzer = None
        if self.smc_enabled.get() and len(data) >= 20:
            self._set_analysis_loading(True, "Running SMC analysis...")
            try:
                analyzer = SmartMoneyAnalyzer(data)
                smc_results = analyzer.analyze_all()
                self._smc_analyzer = analyzer
            except Exception as ex:
                # FIX: isolate SMC failures so main app still works.
                smc_results = None
                print(f"SMC analysis error: {ex}")

        def fmt(val):
            return f"{cur_sym}{val:.5f}" if asset_type == "forex" else f"{cur_sym}{val:.2f}"

        self._stats_data = {
            "symbol": symbol,
            "asset_type": asset_type,
            "name": name,
            "cur_sym": cur_sym,
            "currency": currency,
            "latest": latest,
            "open_p": open_p,
            "highest": highest,
            "lowest": lowest,
            "average": average,
            "change": change,
            "chg_pct": chg_pct,
            "chg_sym": chg_sym,
            "chg_col": chg_col,
            "timeframe_label": tf_label,
            "trend": trend,
            "trend_explain": trend_explain,
            "risk": risk,
            "risk_explain": risk_explain,
            "rsi": rsi,
            "rsi_status": rsi_status,
            "rsi_explain": rsi_explain,
            "best_day": best_day,
            "worst_day": worst_day,
            "best_val": best_val,
            "worst_val": worst_val,
            "vol_status": vol_status,
            "vol_explain": vol_explain,
            "rec": rec,
            "rec_explain": rec_explain,
            "sector": sector,
            "industry": industry,
            "country": country,
            "website": website,
            "mktcap_str": mktcap_str,
            "pe_str": pe_str,
            "div_str": div_str,
            "about": about,
            "pe": pe,
            "div": div,
            "mktcap": mktcap,
            "news_items": news_items,
            "fmt": fmt,
        }
        self._smc_content = smc_results
        self._about_url = website or f"https://finance.yahoo.com/quote/{symbol}"
        self.more_about_btn.pack(fill="x", padx=14, pady=(0, 8))

        self.result_text.config(state="normal")
        self.result_text.delete("1.0", "end")
        self._setup_tags()
        self._stats_content = True
        self._render_stats()
        self.result_text.config(state="disabled")

        self._set_analysis_loading(True, "Rendering chart...")
        try:
            self._render_analysis_chart(
                symbol=symbol,
                name=name,
                timeframe_label=tf_label,
                data=data,
                asset_type=asset_type,
                has_volume=has_volume,
                smc_results=smc_results,
            )
        except Exception as ex:
            messagebox.showwarning("Chart", f"Could not render chart: {ex}")
        finally:
            self._set_analysis_loading(False)

    # ============================================================
    # NEW: Candlestick chart renderer + hover tooltip
    # ============================================================
    def _render_analysis_chart(
        self,
        symbol: str,
        name: str,
        timeframe_label: str,
        data: pd.DataFrame,
        asset_type: str,
        has_volume: bool,
        smc_results: Optional[Dict[str, Any]],
    ):
        # NEW: Candlestick Chart
        for w in self.chart_frame.winfo_children():
            w.destroy()
        self._disconnect_hover()

        # IMPROVED: keep full logic but render a bounded window for speed.
        chart_data = data.tail(300).copy()
        show_vol = has_volume and chart_data["Volume"].fillna(0).sum() > 0
        ratios = [3, 1] if show_vol else [1]
        n_plots = 2 if show_vol else 1

        fig, axes = plt.subplots(n_plots, 1, figsize=(7.8, 5.8), facecolor=BG_COLOR, gridspec_kw={"height_ratios": ratios})
        ax1 = axes[0] if show_vol else axes
        ax2 = axes[1] if show_vol else None

        x_num, candle_width = self._draw_candles(ax1, chart_data)

        ax1.plot(chart_data.index, chart_data["SMA_20"], color=YELLOW_COLOR, linewidth=1.1, linestyle="--", label="SMA 20", alpha=0.9, zorder=4)
        ax1.plot(chart_data.index, chart_data["SMA_50"], color=RED_COLOR, linewidth=1.1, linestyle="--", label="SMA 50", alpha=0.9, zorder=4)

        if smc_results and self._smc_analyzer:
            self._smc_analyzer.draw_smc_chart(ax1, chart_data, asset_type, x_num=x_num)
            demand_patch = mpatches.Patch(color=GREEN_COLOR, alpha=0.4, label="Demand Zone")
            supply_patch = mpatches.Patch(color=RED_COLOR, alpha=0.4, label="Supply Zone")
            fvg_patch = mpatches.Patch(color=YELLOW_COLOR, alpha=0.4, label="FVG/BAG")
            eqh_line = mpatches.Patch(color=PURPLE_COLOR, alpha=0.7, label="EQ High/Low")
            extra_handles = [demand_patch, supply_patch, fvg_patch, eqh_line]
        else:
            extra_handles = []

        ax1.set_facecolor(CARD_COLOR)
        title_suffix = " + SMC" if smc_results else ""
        ax1.set_title(f"{symbol} — {name} [{timeframe_label}]{title_suffix}", color=TEXT_COLOR, fontsize=10, pad=10)
        ax1.tick_params(colors=SUBTEXT_COLOR, labelsize=7)

        loc = mdates.AutoDateLocator(minticks=4, maxticks=10)
        ax1.xaxis.set_major_locator(loc)
        ax1.xaxis.set_major_formatter(mdates.ConciseDateFormatter(loc))

        handles, labels = ax1.get_legend_handles_labels()
        all_handles = handles + extra_handles
        ax1.legend(handles=all_handles, fontsize=6, facecolor=CARD_COLOR, labelcolor=TEXT_COLOR, loc="upper left", ncol=2 if extra_handles else 1)
        ax1.grid(True, color=BORDER_COLOR, linewidth=0.5)
        for spine in ax1.spines.values():
            spine.set_edgecolor(BORDER_COLOR)

        if show_vol and ax2 is not None:
            vol_colors = [GREEN_COLOR if c >= o else RED_COLOR for c, o in zip(chart_data["Close"], chart_data["Open"])]
            ax2.bar(chart_data.index, chart_data["Volume"], color=vol_colors, alpha=0.6, width=candle_width)
            ax2.set_facecolor(CARD_COLOR)
            ax2.set_title("Volume", color=TEXT_COLOR, fontsize=9, pad=6)
            ax2.tick_params(colors=SUBTEXT_COLOR, labelsize=7)
            ax2.grid(True, color=BORDER_COLOR, linewidth=0.5)
            for spine in ax2.spines.values():
                spine.set_edgecolor(BORDER_COLOR)

        plt.tight_layout(pad=1.5)

        # NEW: Hover Tooltip
        self._attach_hover_tooltip(fig=fig, ax=ax1, data=chart_data, asset_type=asset_type)

        canvas = FigureCanvasTkAgg(fig, master=self.chart_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill="both", expand=True)
        self._active_canvas = canvas
        self._active_fig = fig

    def _draw_candles(self, ax, data: pd.DataFrame) -> Tuple[np.ndarray, float]:
        # NEW: Candlestick Chart
        x = mdates.date2num(data.index.to_pydatetime())
        opens = data["Open"].to_numpy(dtype=float)
        highs = data["High"].to_numpy(dtype=float)
        lows = data["Low"].to_numpy(dtype=float)
        closes = data["Close"].to_numpy(dtype=float)

        up = closes >= opens
        colors = np.where(up, GREEN_COLOR, RED_COLOR)

        ax.vlines(x, lows, highs, color=colors, linewidth=0.7, zorder=2, alpha=0.9)

        if len(x) > 1:
            deltas = np.diff(x)
            deltas = deltas[deltas > 0]
            base_step = float(np.median(deltas)) if len(deltas) else 1.0
            width = max(base_step * 0.65, 1e-6)
        else:
            width = 0.6
        body = closes - opens
        ax.bar(x, body, width=width, bottom=opens, color=colors, edgecolor=colors, linewidth=0.2, align="center", zorder=3, alpha=0.95)
        return x, width

    def _disconnect_hover(self):
        if self._active_fig and self._hover_cids:
            for cid in self._hover_cids:
                try:
                    self._active_fig.canvas.mpl_disconnect(cid)
                except Exception:
                    pass
        self._hover_cids = []
        self._hover_payload = None

    def _attach_hover_tooltip(self, fig, ax, data: pd.DataFrame, asset_type: str):
        # NEW: Hover Tooltip
        self._disconnect_hover()
        x = mdates.date2num(data.index.to_pydatetime())
        precision = 5 if asset_type == "forex" else 2

        annot = ax.annotate(
            "",
            xy=(0, 0),
            xytext=(18, 18),
            textcoords="offset points",
            bbox=dict(boxstyle="round,pad=0.35", fc="#0f172a", ec="#334155", alpha=0.88),
            color="white",
            fontsize=8,
            ha="left",
            va="bottom",
        )
        annot.set_visible(False)

        self._hover_payload = {
            "fig": fig,
            "ax": ax,
            "x": x,
            "data": data,
            "annot": annot,
            "last_idx": None,
            "precision": precision,
        }

        self._hover_cids = [
            fig.canvas.mpl_connect("motion_notify_event", self._on_chart_hover),
            fig.canvas.mpl_connect("axes_leave_event", self._on_chart_leave),
        ]

    def _on_chart_leave(self, event):
        payload = self._hover_payload
        if not payload:
            return
        annot = payload["annot"]
        if annot.get_visible():
            annot.set_visible(False)
            payload["fig"].canvas.draw_idle()
        payload["last_idx"] = None

    def _on_chart_hover(self, event):
        payload = self._hover_payload
        if not payload:
            return
        ax = payload["ax"]
        annot = payload["annot"]
        xvals = payload["x"]
        data = payload["data"]
        fig = payload["fig"]

        if event.inaxes != ax or event.xdata is None:
            if annot.get_visible():
                annot.set_visible(False)
                fig.canvas.draw_idle()
            payload["last_idx"] = None
            return

        pos = np.searchsorted(xvals, event.xdata)
        if pos <= 0:
            idx = 0
        elif pos >= len(xvals):
            idx = len(xvals) - 1
        else:
            idx = pos if abs(xvals[pos] - event.xdata) < abs(xvals[pos - 1] - event.xdata) else pos - 1

        if payload["last_idx"] == idx and annot.get_visible():
            return
        payload["last_idx"] = idx

        row = data.iloc[idx]
        dt = data.index[idx]
        dt_str = dt.strftime("%Y-%m-%d %H:%M") if hasattr(dt, "strftime") else str(dt)
        p = payload["precision"]
        vol = float(row["Volume"]) if "Volume" in data.columns and pd.notna(row["Volume"]) else None
        vol_text = f"\nV: {vol:,.0f}" if vol is not None else ""

        text = (
            f"{dt_str}\n"
            f"O: {row['Open']:.{p}f}\n"
            f"H: {row['High']:.{p}f}\n"
            f"L: {row['Low']:.{p}f}\n"
            f"C: {row['Close']:.{p}f}{vol_text}"
        )
        annot.xy = (xvals[idx], float(row["High"]))
        annot.set_text(text)
        annot.set_visible(True)
        fig.canvas.draw_idle()

    # ============================================================
    # RENDER STATS TAB
    # ============================================================
    def _render_stats(self):
        if not hasattr(self, "_stats_data"):
            return
        d = self._stats_data
        fmt = d["fmt"]

        badge = ASSET_TYPE_LABELS.get(d["asset_type"], "Asset")
        self.result_text.insert("end", f"\n  [{badge}]  {d['name']}\n", "accent")

        chg_tag = "green" if d["change"] >= 0 else "red"
        price_str = f"{d['latest']:.5f}" if d["asset_type"] == "forex" else f"{d['latest']:.2f}"
        chg_str = f"{d['change']:.5f}" if d["asset_type"] == "forex" else f"{d['change']:.2f}"
        self.result_text.insert(
            "end",
            f"  {d['cur_sym']}{price_str}  {d['chg_sym']} {d['chg_col']}{chg_str} ({d['chg_col']}{d['chg_pct']:.2f}%)\n",
            chg_tag,
        )
        if d.get("timeframe_label"):
            self.result_text.insert("end", f"  Timeframe: {d['timeframe_label']}\n", "sub")

        if any(v != "N/A" for v in [d["sector"], d["industry"], d["country"]]) or d["mktcap"]:
            self._section("🏢 Info")
            if d["sector"] != "N/A":
                self._row("Sector:", d["sector"])
            if d["industry"] != "N/A":
                self._row("Industry:", d["industry"])
            if d["country"] != "N/A":
                self._row("Country:", d["country"])
            if d["mktcap"]:
                self._row("Market Cap:", d["mktcap_str"])
            if d["pe"]:
                self._row("P/E Ratio:", d["pe_str"])
            if d["div"]:
                self._row("Dividend:", d["div_str"])
            if d["website"]:
                self.result_text.insert("end", f"  🌐 {d['website']}\n", "sub")
            if d["about"]:
                dot = d["about"].find(". ")
                one = d["about"][: dot + 1] if dot != -1 else d["about"][:120]
                self.result_text.insert("end", f"\n  {one}\n", "sub")

        self._section("💹 Price Summary")
        self._row("Open:", fmt(d["open_p"]))
        self._row("Latest:", fmt(d["latest"]))
        self._row("Highest:", fmt(d["highest"]))
        self._row("Lowest:", fmt(d["lowest"]))
        self._row("Average:", fmt(d["average"]))

        self._section("📈 Trend")
        self._row("Signal:", d["trend"])
        self._note(d["trend_explain"])

        self._section("⚡ Risk Level")
        self._row("Risk:", d["risk"])
        self._note(d["risk_explain"])

        self._section("🔄 RSI Momentum")
        rsi_display = f"{d['rsi']:.1f}" if not pd.isna(d["rsi"]) else "N/A"
        self._row("RSI:", rsi_display)
        self._row("Status:", d["rsi_status"])
        self._note(d["rsi_explain"])

        self._section("📅 Best & Worst Days")
        best_day = d["best_day"].date() if hasattr(d["best_day"], "date") else d["best_day"]
        worst_day = d["worst_day"].date() if hasattr(d["worst_day"], "date") else d["worst_day"]
        self._row("Best Day:", f"{best_day} (+{d['best_val']:.2f}%)", "green")
        self._row("Worst Day:", f"{worst_day} ({d['worst_val']:.2f}%)", "red")

        self._section("📦 Volume")
        self._row("Activity:", d["vol_status"])
        self._note(d["vol_explain"])

        self._section("🧠 Recommendation")
        tag = "green" if "Positive" in d["rec"] else "red" if "Negative" in d["rec"] else "yellow"
        self._row("Signal:", d["rec"], tag)
        self._note(d["rec_explain"])
        self._note("Not financial advice. Always do your own research.")

        self._section("📰 Latest News")
        if d["news_items"]:
            for i, item in enumerate(d["news_items"]):
                title = item.get("title", "No title")
                url = item.get("url", "")
                if len(title) > 70:
                    cut = title[:70].rfind(" ")
                    title = title[:cut] + " ..." if cut > 0 else title[:70] + " ..."
                self.result_text.insert("end", f"\n  {i+1}. {title}\n")
                if url:
                    link_text = "     [ Read Article ]\n"
                    tag_name = f"news_link_{i}"
                    start = self.result_text.index("insert")
                    self.result_text.insert("end", link_text, "accent")
                    end = self.result_text.index("insert")
                    self.result_text.tag_add(tag_name, start, end)
                    self.result_text.tag_configure(tag_name, foreground=ACCENT_COLOR, underline=True)
                    self.result_text.tag_bind(tag_name, "<Button-1>", lambda e, link=url: webbrowser.open(link))
                    self.result_text.tag_bind(tag_name, "<Enter>", lambda e: self.result_text.config(cursor="hand2"))
                    self.result_text.tag_bind(tag_name, "<Leave>", lambda e: self.result_text.config(cursor="arrow"))
        else:
            self.result_text.insert("end", "  No news available.\n", "sub")

    # ============================================================
    # RENDER SMC TAB
    # ============================================================
    def _render_smc(self):
        if not self._smc_content:
            self.result_text.insert(
                "end",
                "\n  🧠 SMC Analysis\n"
                "  ─────────────────────────────────\n\n"
                "  SMC analysis unavailable.\n"
                "  Need at least 20 candles of data.\n"
                "  Try a longer period (3mo or 6mo).\n",
                "sub",
            )
            return

        r = self._smc_content
        self.result_text.insert("end", "\n  🧠 SMART MONEY CONCEPTS\n", "smc_head")
        self.result_text.insert("end", "  ─────────────────────────────────\n", "sub")
        self.result_text.insert("end", "  Institutional footprint analysis\n\n", "sub")

        summary = r.get("summary", {})
        verdict = summary.get("verdict", "")
        vc = summary.get("verdict_color", "yellow")
        vtag = f"verdict_{vc}"
        self.result_text.insert("end", f"  {verdict}\n\n", vtag)

        bull = summary.get("bullish_count", 0)
        bear = summary.get("bearish_count", 0)
        self.result_text.insert("end", f"  Bullish signals: {bull}  |  Bearish signals: {bear}\n\n", "sub")
        for sig in summary.get("signals", []):
            tag = "green" if "Bullish" in sig else "red" if "Bearish" in sig else "yellow"
            self.result_text.insert("end", f"  {sig}\n", tag)

        iop = r.get("iop", {})
        self.result_text.insert("end", "\n\n")
        self.result_text.insert("end", "  📊 IOP — Imbalance of Power\n", "smc_head")
        self.result_text.insert("end", "  ─────────────────────────────────\n", "sub")
        self.result_text.insert("end", f"  Candle Type:  {iop.get('candle_type', 'N/A')}\n")
        self.result_text.insert("end", "  True Power:   ", "sub")
        power = iop.get("power", "")
        ptag = "green" if "BULLISH" in power else "red" if "BEARISH" in power else "yellow"
        self.result_text.insert("end", f"{power}\n", ptag)
        close_pct = iop.get("close_pct", 0)
        self.result_text.insert("end", f"  Close %:      {close_pct:.1f}% of candle range\n", "sub")
        self.result_text.insert("end", f"\n  💬 {iop.get('power_note', '')}\n", "sub")

        liq_sig = iop.get("liq_signal", "")
        if liq_sig:
            tag = "green" if "BULLISH" in liq_sig else "red"
            self.result_text.insert("end", f"\n  {liq_sig}\n", tag)

        sd = r.get("sd", {})
        self.result_text.insert("end", "\n\n")
        self.result_text.insert("end", "  🏗️ Supply & Demand Zones\n", "smc_head")
        self.result_text.insert("end", "  ─────────────────────────────────\n", "sub")

        demand_zones = sd.get("demand_zones", [])
        supply_zones = sd.get("supply_zones", [])
        if demand_zones:
            self.result_text.insert("end", "  DEMAND ZONES (Support):\n", "green")
            for z in reversed(demand_zones):
                self.result_text.insert("end", f"  • {z['pattern']}  [{z['bottom']:.4f} – {z['top']:.4f}]  {z['freshness']}\n", "sub")
        else:
            self.result_text.insert("end", "  No demand zones found.\n", "sub")

        self.result_text.insert("end", "\n")
        if supply_zones:
            self.result_text.insert("end", "  SUPPLY ZONES (Resistance):\n", "red")
            for z in reversed(supply_zones):
                self.result_text.insert("end", f"  • {z['pattern']}  [{z['bottom']:.4f} – {z['top']:.4f}]  {z['freshness']}\n", "sub")
        else:
            self.result_text.insert("end", "  No supply zones found.\n", "sub")

        nd = sd.get("nearest_demand")
        ns = sd.get("nearest_supply")
        if nd and nd.get("near"):
            self.result_text.insert("end", f"\n  Price is NEAR demand zone ({nd['pattern']}) — watch for bounce.\n", "green")
        if ns and ns.get("near"):
            self.result_text.insert("end", f"\n  Price is NEAR supply zone ({ns['pattern']}) — watch for rejection.\n", "red")

        fvg = r.get("fvg", {})
        self.result_text.insert("end", "\n\n")
        self.result_text.insert("end", "  📐 FVG & BAG — Price Gaps\n", "smc_head")
        self.result_text.insert("end", "  ─────────────────────────────────\n", "sub")
        unfilled = fvg.get("unfilled", [])
        nearby = fvg.get("nearby", [])
        if unfilled:
            self.result_text.insert("end", f"  Unfilled gaps found: {len(unfilled)}\n", "sub")
            for g in unfilled[-4:]:
                color = "green" if g["direction"] == "BULLISH" else "red"
                gap_label = "BAG" if g["is_bag"] else "FVG"
                action = "Breakaway momentum (BAG)." if g["is_bag"] else "Acts as price magnet (FVG)."
                self.result_text.insert("end", f"  • {gap_label} {g['direction']}  [{g['bottom']:.4f} – {g['top']:.4f}]\n", color)
                self.result_text.insert("end", f"    -> {action}\n", "sub")
        else:
            self.result_text.insert("end", "  No significant gaps detected.\n", "sub")

        if nearby:
            self.result_text.insert("end", "\n  Nearby unfilled gaps (price magnets):\n", "yellow")
            for g in nearby:
                tag = "green" if g["direction"] == "BULLISH" else "red"
                self.result_text.insert("end", f"  -> {'FVG' if not g['is_bag'] else 'BAG'} @ {g['mid']:.4f}\n", tag)

        liq = r.get("liquidity", {})
        self.result_text.insert("end", "\n\n")
        self.result_text.insert("end", "  💧 Liquidity Analysis\n", "smc_head")
        self.result_text.insert("end", "  ─────────────────────────────────\n", "sub")
        sweep = liq.get("sweep_detected", "")
        if sweep:
            tag = "green" if "BULLISH" in sweep else "red"
            self.result_text.insert("end", f"  {sweep}\n\n", tag)

        hunts = liq.get("recent_hunts", [])
        if hunts:
            self.result_text.insert("end", "  Recent Stop Hunts:\n", "sub")
            for h in hunts[-3:]:
                tag = "green" if "BULLISH" in h["type"] else "red"
                self.result_text.insert("end", f"  • {h['type']} on {str(h['date'])[:10]}\n", tag)
                self.result_text.insert("end", f"    {h['note']}\n", "sub")
        else:
            self.result_text.insert("end", "  No recent stop hunts detected.\n", "sub")

        eq_highs = liq.get("eq_highs", [])
        eq_lows = liq.get("eq_lows", [])
        if eq_highs:
            self.result_text.insert("end", "\n  Equal Highs (liquidity above):\n", "purple")
            for eq in eq_highs:
                self.result_text.insert("end", f"  • EQH @ {eq['level']:.4f}\n", "sub")
        if eq_lows:
            self.result_text.insert("end", "\n  Equal Lows (liquidity below):\n", "purple")
            for eq in eq_lows:
                self.result_text.insert("end", f"  • EQL @ {eq['level']:.4f}\n", "sub")

        self.result_text.insert("end", "\n\n")
        self.result_text.insert("end", "  🎯 SMC Trade Idea\n", "smc_head")
        self.result_text.insert("end", "  ─────────────────────────────────\n", "sub")

        vc_str = summary.get("verdict_color", "yellow")
        nd = sd.get("nearest_demand")
        ns = sd.get("nearest_supply")
        if vc_str == "green" and nd:
            self.result_text.insert(
                "end",
                f"  LONG BIAS:\n"
                f"  Wait for price to pull back into demand [{nd['bottom']:.4f}–{nd['top']:.4f}]\n"
                f"  Confirm with bullish IOP candle.\n"
                f"  Stop below demand ({nd['bottom']:.4f}).\n"
                f"  Target next supply zone / highs.\n",
                "green",
            )
        elif vc_str == "red" and ns:
            self.result_text.insert(
                "end",
                f"  SHORT BIAS:\n"
                f"  Wait for price to push into supply [{ns['bottom']:.4f}–{ns['top']:.4f}]\n"
                f"  Confirm with bearish IOP candle.\n"
                f"  Stop above supply ({ns['top']:.4f}).\n"
                f"  Target next demand zone / lows.\n",
                "red",
            )
        else:
            self.result_text.insert(
                "end",
                "  No high-probability setup right now.\n"
                "  Wait for price to reach key zones and confirm with IOP.\n",
                "sub",
            )

        self.result_text.insert("end", "\n\n  SMC analysis is educational only. Always manage risk.\n", "sub")

    # ============================================================
    # SIMULATOR SCREEN
    # ============================================================
    def show_simulator(self):
        self.clear()
        self.make_topbar("🎮 Trading Simulator")

        tk.Label(
            self.root,
            text="Pick any asset & a past date — see if you'd have made profit or loss!",
            font=FONT_BODY,
            bg=BG_COLOR,
            fg=SUBTEXT_COLOR,
        ).pack(pady=(8, 14))

        outer, card = self.make_card(self.root, padx=30, pady=22, bg=CARD_COLOR)
        outer.pack(padx=80, fill="x")

        r1 = tk.Frame(card, bg=CARD_COLOR)
        r1.pack(fill="x", pady=4)

        tk.Label(r1, text="Symbol / Pair:", font=FONT_BODY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(side="left", padx=(0, 8))
        self.sim_symbol = tk.Entry(
            r1,
            font=FONT_HEADING,
            width=12,
            bg=BG_COLOR,
            fg=ACCENT_COLOR,
            insertbackground=ACCENT_COLOR,
            relief="flat",
            highlightthickness=1,
            highlightbackground=BORDER_COLOR,
            highlightcolor=ACCENT_COLOR,
        )
        self.sim_symbol.insert(0, "AAPL")
        self.sim_symbol.pack(side="left", ipady=4, padx=(0, 24))

        tk.Label(r1, text="Number of Units:", font=FONT_BODY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(side="left", padx=(0, 8))
        self.sim_shares = tk.Entry(
            r1,
            font=FONT_HEADING,
            width=8,
            bg=BG_COLOR,
            fg=ACCENT_COLOR,
            insertbackground=ACCENT_COLOR,
            relief="flat",
            highlightthickness=1,
            highlightbackground=BORDER_COLOR,
            highlightcolor=ACCENT_COLOR,
        )
        self.sim_shares.insert(0, "10")
        self.sim_shares.pack(side="left", ipady=4)

        tk.Label(
            card,
            text="Works with: stocks (AAPL), forex (EURUSD), crypto (BTC), indices (NASDAQ), Indian stocks (TCS.NS)",
            font=FONT_TINY,
            bg=CARD_COLOR,
            fg=SUBTEXT_COLOR,
        ).pack(anchor="w", pady=(4, 0))

        r2 = tk.Frame(card, bg=CARD_COLOR)
        r2.pack(fill="x", pady=(12, 4))

        tk.Label(r2, text="Date you 'bought':", font=FONT_BODY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(side="left", padx=(0, 12))
        today = datetime.date.today()
        start_year = 2010
        for label, attr, vals, default in [
            ("Year", "sim_year", [str(y) for y in range(start_year, today.year + 1)], str(max(today.year - 1, start_year))),
            ("Month", "sim_month", [f"{m:02d}" for m in range(1, 13)], f"{today.month:02d}"),
            ("Day", "sim_day", [f"{d:02d}" for d in range(1, 32)], f"{today.day:02d}"),
        ]:
            tk.Label(r2, text=f"{label}:", font=FONT_TINY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(side="left", padx=(8, 2))
            cb = ttk.Combobox(r2, width=6 if label == "Year" else 4, font=FONT_BODY, state="readonly", values=vals)
            cb.set(default)
            cb.pack(side="left", padx=2)
            setattr(self, attr, cb)

        tk.Button(
            card,
            text="  ▶  Simulate Trade  ",
            font=FONT_HEADING,
            bg=GREEN_COLOR,
            fg="white",
            activebackground="#16a34a",
            relief="flat",
            cursor="hand2",
            pady=8,
            command=self.run_simulator,
        ).pack(pady=(18, 0))

        # NEW: Loading indicator
        self.sim_loading_var = tk.StringVar(value="")
        tk.Label(card, textvariable=self.sim_loading_var, font=FONT_TINY, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(anchor="w", pady=(8, 0))
        self.sim_progress = ttk.Progressbar(card, mode="indeterminate", length=140)
        self.sim_progress.pack(anchor="w", pady=(4, 0))
        self.sim_progress.pack_forget()

        bottom = tk.Frame(self.root, bg=BG_COLOR)
        bottom.pack(fill="both", expand=True, padx=14, pady=10)

        self.sim_result = tk.Frame(bottom, bg=CARD_COLOR, highlightthickness=1, highlightbackground=BORDER_COLOR)
        self.sim_result.pack(side="left", fill="both", expand=False, padx=(0, 10))

        self.sim_chart_frame = tk.Frame(bottom, bg=BG_COLOR)
        self.sim_chart_frame.pack(side="right", fill="both", expand=True)

    def _set_sim_loading(self, active: bool, text: str = ""):
        if not hasattr(self, "sim_progress"):
            return
        self.sim_loading_var.set(text if active else "")
        if active:
            self.sim_progress.pack(anchor="w", pady=(4, 0))
            self.sim_progress.start(10)
        else:
            self.sim_progress.stop()
            self.sim_progress.pack_forget()
        try:
            self.root.update_idletasks()
        except tk.TclError:
            pass

    # ============================================================
    # RUN SIMULATOR
    # ============================================================
    def run_simulator(self):
        for w in self.sim_result.winfo_children():
            w.destroy()
        for w in self.sim_chart_frame.winfo_children():
            w.destroy()

        try:
            raw_input = self.sim_symbol.get().strip()
            shares = float(self.sim_shares.get())
            year = int(self.sim_year.get())
            month = int(self.sim_month.get())
            day = int(self.sim_day.get())
            buy_date = datetime.date(year, month, day)
        except ValueError:
            messagebox.showwarning("Invalid Input", "Please check all fields.")
            return

        # FIX: reject non-positive units
        if shares <= 0:
            messagebox.showwarning("Invalid Units", "Number of units must be greater than 0.")
            return

        symbol, asset_type = resolve_symbol(raw_input)
        today = datetime.date.today()
        if buy_date >= today:
            messagebox.showwarning("Invalid Date", "Buy date must be in the past.")
            return

        self._set_sim_loading(True, "Fetching historical data...")
        try:
            data, info, _ = self._fetch_market_payload(
                symbol=symbol,
                start=buy_date - datetime.timedelta(days=7),
                end=today + datetime.timedelta(days=1),
            )
        except Exception as ex:
            self._set_sim_loading(False)
            messagebox.showerror("Error", str(ex))
            return

        if data.empty:
            self._set_sim_loading(False)
            messagebox.showerror("No Data", f"No data found for '{symbol}'.")
            return

        trade_slice = data[data.index.date >= buy_date]
        if trade_slice.empty:
            self._set_sim_loading(False)
            messagebox.showerror("No Data", "Could not find a trading day near that date.")
            return

        buy_ts = trade_slice.index[0]
        buy_date_actual = buy_ts.date()
        buy_idx_candidates = np.where(data.index == buy_ts)[0]
        buy_idx = int(buy_idx_candidates[0]) if len(buy_idx_candidates) else 0

        buy_price = float(data.iloc[buy_idx]["Close"])
        sell_price = float(data.iloc[-1]["Close"])
        sell_date = data.index[-1].date()
        invested = buy_price * shares
        current_val = sell_price * shares
        profit_loss = current_val - invested
        percentage = (profit_loss / invested) * 100 if invested != 0 else 0
        days_held = (sell_date - buy_date_actual).days
        is_profit = profit_loss >= 0
        color = GREEN_COLOR if is_profit else RED_COLOR
        emoji = "✅ Profit" if is_profit else "❌ Loss"
        name = str(info.get("longName", info.get("shortName", symbol)))

        currency = get_asset_currency(info, asset_type)
        cur_sym = "₹" if currency == "INR" else "$" if currency == "USD" else f"{currency} "
        badge = ASSET_TYPE_LABELS.get(asset_type, "Asset")

        def fmt(val):
            return f"{cur_sym}{val:.5f}" if asset_type == "forex" else f"{cur_sym}{val:.2f}"

        unit_label = "Units" if asset_type in ("forex", "crypto", "index") else "Shares"

        pad = tk.Frame(self.sim_result, bg=CARD_COLOR, padx=18, pady=14)
        pad.pack(fill="both", expand=True)

        def section(title):
            tk.Label(pad, text=title, font=("Helvetica", 10, "bold"), bg=CARD_COLOR, fg=ACCENT_COLOR).pack(anchor="w", pady=(10, 0))
            tk.Frame(pad, bg=BORDER_COLOR, height=1).pack(fill="x", pady=(2, 4))

        def row(label, value, val_color=TEXT_COLOR):
            f = tk.Frame(pad, bg=CARD_COLOR)
            f.pack(anchor="w", pady=1)
            tk.Label(f, text=f"{label:<22}", font=FONT_SMALL, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(side="left")
            tk.Label(f, text=value, font=FONT_SMALL, bg=CARD_COLOR, fg=val_color).pack(side="left")

        tk.Label(pad, text=f"[{badge}]  {name}", font=FONT_HEADING, bg=CARD_COLOR, fg=TEXT_COLOR).pack(anchor="w", pady=(0, 2))
        tk.Label(pad, text=symbol, font=FONT_SMALL, bg=CARD_COLOR, fg=SUBTEXT_COLOR).pack(anchor="w")

        section("🧾 Trade Details")
        units_display = int(shares) if shares == int(shares) else shares
        row(f"{unit_label} Bought:", str(units_display))
        row("Buy Date:", str(buy_date_actual))
        row("Buy Price:", f"{fmt(buy_price)} / unit")
        row("Sell Date:", f"{sell_date}  (Today)")
        row("Sell Price:", f"{fmt(sell_price)} / unit")
        row("Days Held:", f"{days_held} days")

        section("💰 Result")
        row("Money Invested:", fmt(invested))
        row("Current Value:", fmt(current_val))
        row(f"{emoji}:", f"{fmt(abs(profit_loss))}  ({abs(percentage):.2f}%)", color)

        tk.Label(
            pad,
            text=f"{'▲' if is_profit else '▼'} {fmt(abs(profit_loss))}  ({abs(percentage):.1f}%)",
            font=("Helvetica", 14, "bold"),
            bg=CARD_COLOR,
            fg=color,
        ).pack(anchor="w", pady=(8, 2))

        if is_profit:
            explain = (
                f"You invested {fmt(invested)} and it grew\n"
                f"to {fmt(current_val)} in {days_held} days.\n"
                f"Each unit gained {fmt(sell_price - buy_price)}."
            )
        else:
            explain = (
                f"You invested {fmt(invested)} but it dropped\n"
                f"to {fmt(current_val)} in {days_held} days.\n"
                f"Each unit lost {fmt(buy_price - sell_price)}."
            )
        tk.Label(pad, text=f"💬 {explain}", font=FONT_SMALL, bg=CARD_COLOR, fg=SUBTEXT_COLOR, justify="left").pack(anchor="w", pady=(6, 0))

        chart_data = data.iloc[buy_idx:]["Close"]
        dates = list(chart_data.index)
        prices = list(chart_data.values)

        fig, ax = plt.subplots(figsize=(5.5, 4.2), facecolor=BG_COLOR)
        ax.plot(dates, prices, color=ACCENT_COLOR, linewidth=1.8, label="Price", zorder=3)
        ax.fill_between(dates, buy_price, prices, alpha=0.15, color=color, zorder=2)
        ax.axhline(y=buy_price, color=GREEN_COLOR, linestyle="--", linewidth=1, alpha=0.7, label=f"Buy @ {fmt(buy_price)}")
        ax.scatter([dates[0]], [buy_price], color=GREEN_COLOR, s=90, zorder=5, label="Buy Point")
        ax.scatter([dates[-1]], [sell_price], color=color, s=90, zorder=5, label=f"Today @ {fmt(sell_price)}")
        ax.set_facecolor(CARD_COLOR)
        ax.set_title(f"{symbol} — Buy to Today", color=TEXT_COLOR, fontsize=10, pad=8)
        ax.tick_params(colors=SUBTEXT_COLOR, labelsize=7)
        ax.legend(fontsize=7, facecolor=CARD_COLOR, labelcolor=TEXT_COLOR, loc="upper left")
        ax.grid(True, color=BORDER_COLOR, linewidth=0.5)
        for spine in ax.spines.values():
            spine.set_edgecolor(BORDER_COLOR)
        plt.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self.sim_chart_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill="both", expand=True)

        self._set_sim_loading(False)

    # ============================================================
    # TOP BAR
    # ============================================================
    def make_topbar(self, title):
        bar = tk.Frame(self.root, bg=CARD_COLOR, pady=0)
        bar.pack(fill="x")
        tk.Frame(bar, bg=ACCENT_COLOR, height=3).pack(fill="x")
        inner = tk.Frame(bar, bg=CARD_COLOR, pady=8)
        inner.pack(fill="x")
        tk.Button(
            inner,
            text="⬅ Home",
            font=FONT_SMALL,
            bg=CARD_COLOR,
            fg=SUBTEXT_COLOR,
            activebackground=CARD2_COLOR,
            relief="flat",
            cursor="hand2",
            command=self.show_home,
        ).pack(side="left", padx=15)
        tk.Label(inner, text=title, font=FONT_HEADING, bg=CARD_COLOR, fg=TEXT_COLOR).pack(side="left", padx=6)


# ============================================================
# RUN
# ============================================================
root = tk.Tk()
app = StockVisionApp(root)
root.mainloop()
