import os
import time
import csv
import logging
import threading
from uuid import uuid4
from datetime import datetime, timedelta, date, timezone
from datetime import time as time2
import pytz
import requests
import urllib.parse
import json
import ccxt
import talib
import pandas as pd
import numpy as np
from sqlalchemy import create_engine, Column, Integer, String, Float, text
from sqlalchemy.orm import sessionmaker, scoped_session, declarative_base
from sqlalchemy.exc import SQLAlchemyError
from requests.exceptions import HTTPError, ConnectionError, Timeout
from ratelimit import limits, sleep_and_retry
import traceback

# ANSI color codes for terminal output
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
BLUE = "\033[94m"
MAGENTA = "\033[95m"
CYAN = "\033[96m"
RESET = "\033[0m"

# Configuration flags
PRINT_ROBOT_STORED_BUY_AND_SELL_LIST_DATABASE = True  # Set to True to view database
PRINT_DATABASE = True  # Set to True to view positions to sell
DEBUG = False  # Set to False for faster execution
ALL_BUY_ORDERS_ARE_5_DOLLARS = False  # When True, every buy order is a $5.00 fractional share market day order
FRACTIONAL_BUY_ORDERS = True  # Enable fractional share orders
POINT_THRESHOLD = 100  # Threshold for buy/sell action
MIN_PRICE = 0.00000001  # Minimum price for comparisons to avoid zero

# Global variables
YOUR_SECRET_KEY = os.getenv("YOUR_SECRET_KEY")
CALLMEBOT_API_KEY = os.getenv("CALLMEBOT_API_KEY")
CALLMEBOT_PHONE = os.getenv("CALLMEBOT_PHONE")
secret = None
access_token = None
account_id = None
last_token_fetch_time = None
BASE_URL = "https://api.public.com/userapigateway"
HEADERS = None
risk_levels = {
    "BTC": "ultra-low"
}
allocation_per_risk = {
    "ultra-low": 10.0
}
symbol = {"BTC"}
symbols_to_sell_dict = {}
today_date = datetime.today().date()
today_datetime = datetime.now(pytz.timezone('US/Eastern'))
csv_filename = 'log-file-of-buy-and-sell-signals-btc.csv'
fieldnames = ['Date', 'Buy', 'Sell', 'Quantity', 'Symbol', 'Price Per Share']
price_changes = {}
current_price = 0
today_date_str = today_date.strftime("%Y-%m-%d")
qty = 0
price_history = {}  # BTC -> interval -> list of prices
last_stored = {}  # BTC -> interval -> last_timestamp
interval_map = {
    '1min': 60,
    '5min': 300,
    '10min': 600,
    '15min': 900,
    '30min': 1800,
    '45min': 2700,
    '60min': 3600
}
crypto_data = {}
previous_prices = {}
data_cache = {}
CACHE_EXPIRY = 120  # 2 minutes
CALLS = 10  # Max API calls per period
PERIOD = 1  # Period in seconds
RETRY_COUNT = 3  # Retry failed cancellations
task_running = {
    'buy_cryptos': False,
    'sell_cryptos': False,
    'check_price_moves': False,
    'check_stop_order_status': False,
    'monitor_stop_losses': False,
    'sync_db_with_api': False,
    'refresh_token_if_needed': False
}  # Task running flags

db_lock = threading.Lock()

# Symbol mapping for internal use vs API
CRYPTO_SYMBOL_MAP = {"BTC": "BTC-CRYPTO"}
INTERNAL_SYMBOL = "BTC"
TRADING_SYMBOL = CRYPTO_SYMBOL_MAP[INTERNAL_SYMBOL]

# Timezone
eastern = pytz.timezone('US/Eastern')

# Logging configuration
logging.basicConfig(filename='trading-bot-program-logging-messages-btc.txt', level=logging.INFO, 
                    format='%(asctime)s %(levelname)s:%(message)s')

# Initialize CSV file
def initialize_csv():
    with open(csv_filename, mode='w', newline='') as csv_file:
        csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
        csv_writer.writeheader()

def get_internal_symbol(api_symbol):
    for internal, api_sym in CRYPTO_SYMBOL_MAP.items():
        if api_sym == api_symbol:
            return internal
    return api_symbol

def get_trading_symbol(internal_symbol):
    return CRYPTO_SYMBOL_MAP.get(internal_symbol, internal_symbol)

# Database Models
Base = declarative_base()

class TradeHistory(Base):
    __tablename__ = 'trade_history'
    id = Column(Integer, primary_key=True)
    symbols = Column(String, nullable=False)
    action = Column(String, nullable=False)
    quantity = Column(Float, nullable=False)
    price = Column(Float, nullable=False)
    date = Column(String, nullable=False)

class Position(Base):
    __tablename__ = 'positions'
    symbols = Column(String, primary_key=True, nullable=False)
    quantity = Column(Float, nullable=False)
    avg_price = Column(Float, nullable=False)
    purchase_date = Column(String, nullable=False)
    stop_order_id = Column(String, nullable=True)
    stop_price = Column(Float, nullable=True)

# Initialize SQLAlchemy
def initialize_database():
    engine = create_engine('sqlite:///trading_bot_btc.db', connect_args={"check_same_thread": False})
    with engine.connect() as conn:
        conn.execute(text("PRAGMA journal_mode=WAL;"))
    SessionLocal = scoped_session(sessionmaker(bind=engine))
    Base.metadata.create_all(engine)
    return SessionLocal

SessionLocal = initialize_database()

# Rate limiting decorator
@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def get_cached_data(symbols, data_type, fetch_func, *args, **kwargs):
    print(f"Checking cache for {symbols} {data_type}...")
    key = (symbols, data_type)
    current_time = time.time()
    if key in data_cache and current_time - data_cache[key]['timestamp'] < CACHE_EXPIRY:
        data = data_cache[key]['data']
        if data is None or isinstance(data, (list, dict)) and not data:
            print(f"Invalid cached data for {symbols} {data_type}. Fetching new data...")
        else:
            print(f"Using cached {data_type} for {symbols}.")
            return data
    print(f"Fetching new {data_type} for {symbols}...")
    data = fetch_func(*args, **kwargs)
    data_cache[key] = {'timestamp': current_time, 'data': data}
    print(f"Cached {data_type} for {symbols}.")
    return data

def cleanup_invalid_positions():
    with SessionLocal() as session:
        invalid_positions = session.query(Position).filter((Position.avg_price < MIN_PRICE) | (Position.quantity <= 0)).all()
        for pos in invalid_positions:
            print(f"Deleting invalid position for {pos.symbols} with avg_price ${pos.avg_price:.8f} and quantity {pos.quantity:.8f}")
            logging.info(f"Deleting invalid position for {pos.symbols} with avg_price ${pos.avg_price:.8f} and quantity {pos.quantity:.8f}")
            if pos.stop_order_id:
                client_cancel_order({'orderId': pos.stop_order_id, 'instrument': {'symbol': get_trading_symbol(pos.symbols)}})
            session.delete(pos)
        session.commit()

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_get_quote(symbol):
    """Fetch current quote from Public.com API with fallback to CCXT."""
    if not account_id:
        logging.error("No BROKERAGE accountId for quote fetch")
        return None
    trading_symbol = get_trading_symbol(symbol)
    url = f"{BASE_URL}/trading/{account_id}/quote/{trading_symbol}"
    for attempt in range(3):
        try:
            resp = requests.get(url, headers=HEADERS, timeout=10)
            if resp.status_code >= 400:
                logging.warning(f"Quote fetch failed for {trading_symbol}: HTTP {resp.status_code} - {resp.text}")
                if attempt < 2:
                    time.sleep(2)
                continue
            resp.raise_for_status()
            quote_data = resp.json()
            last_price = float(quote_data.get('lastPrice', quote_data.get('price', 0)))
            if last_price < MIN_PRICE:
                logging.warning(f"Invalid quote price for {trading_symbol}: {last_price}. Setting to {MIN_PRICE}")
                last_price = MIN_PRICE
            print(f"Public.com quote for {symbol}: ${last_price:.8f}")
            logging.info(f"Public.com quote for {symbol}: ${last_price:.8f}")
            return round(last_price, 8)
        except Exception as e:
            logging.error(f"Attempt {attempt + 1}/3: Error fetching quote from Public.com for {symbol}: {e}")
            if attempt < 2:
                time.sleep(2)
    # Fallback to CCXT
    logging.info(f"Falling back to CCXT for {symbol} price")
    return _fetch_current_price_ccxt(symbol)

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def _fetch_current_price_ccxt(symbol):
    exchange = ccxt.coinbase()
    symbol_usd = f"{symbol}/USD"
    try:
        ticker = exchange.fetch_ticker(symbol_usd)
        last_price = float(ticker.get('last', 0))
        if last_price < MIN_PRICE:
            logging.warning(f"Invalid CCXT price for {symbol}: {last_price}. Setting to {MIN_PRICE}")
            last_price = MIN_PRICE
        price_color = GREEN if last_price >= MIN_PRICE else RED
        print(f"Coinbase last price for {symbol}: {price_color}${last_price:.8f}{RESET}")
        return round(last_price, 8)
    except Exception as e:
        logging.error(f"Error fetching price for {symbol} from Coinbase: {e}")
        print(f"Error fetching price for {symbol} from Coinbase: {e}")
        return None

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def place_market_order(symbol, side, fractional=False, amount=None, quantity=None):
    """Place MARKET order (fractional or full-share)"""
    url = f"{BASE_URL}/trading/{account_id}/order"
    order_id = str(uuid4())
    is_fractional = fractional or (amount is not None) or (quantity is not None and quantity % 1 != 0)
    expiration = {"timeInForce": "DAY"}  # All market orders are DAY
    payload = {
        "orderId": order_id,
        "instrument": {"symbol": symbol, "type": "CRYPTO"},
        "orderSide": side.upper(),
        "orderType": "MARKET",
        "expiration": expiration,
        "openCloseIndicator": "OPEN"
    }
    if amount is not None:
        payload["amount"] = f"{amount:.2f}"
    elif quantity is not None:
        if not is_fractional:
            quantity = int(quantity)
            payload["quantity"] = str(quantity)
        else:
            payload["quantity"] = f"{quantity:.8f}"
    else:
        raise ValueError("Must provide 'amount' for fractional orders or 'quantity' for full-share orders")
    try:
        response = requests.post(url, headers=HEADERS, json=payload, timeout=10)
        if response.status_code >= 400:
            print(f"HTTP Error Response for {symbol}: {response.status_code} {response.text}")
            logging.error(f"HTTP Error Response for {symbol}: {response.status_code} {response.text}")
            return {"error": f"HTTP {response.status_code}: {response.text}"}
        response.raise_for_status()
        logging.info(f"Order placed successfully for {symbol}: {response.json()}")
        return response.json()
    except Exception as e:
        print(f"ERROR placing order for {symbol}:")
        logging.error(f"Error placing order for {symbol}: {e}")
        traceback.print_exc()
        return {"error": str(e)}

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_place_order(symbol, side, amount=None, quantity=None, order_type="MARKET", limit_price=None, stop_price=None):
    try:
        if not account_id:
            logging.error("No BROKERAGE accountId")
            return None
        if order_type == "MARKET":
            order_response = place_market_order(
                symbol=symbol,
                side=side,
                fractional=FRACTIONAL_BUY_ORDERS if amount is not None else False,
                amount=amount,
                quantity=quantity
            )
        else:  # STOP - Note: Stop orders may not be supported for crypto on Public.com
            logging.warning(f"Stop orders may not be supported for crypto. Skipping for {symbol}.")
            return None
        if order_response.get('error'):
            logging.error(f"Order placement error for {symbol}: {order_response['error']}")
            return None
        order_id = order_response.get('orderId')
        if amount is not None:
            logging.info(f"Order placed: {side} ${amount:.2f} of {symbol}, Order ID: {order_id}")
        else:
            logging.info(f"Order placed: {side} {quantity:.8f} of {symbol}, Order ID: {order_id}")
        return order_id
    except Exception as e:
        logging.error(f"Order placement error for {symbol}: {e}")
        return None

def get_expiration():
    """Return expirationTime string for GTD orders (full-share), skip weekends"""
    exp = datetime.now(timezone.utc) + timedelta(days=30)
    if exp.weekday() == 5:
        exp += timedelta(days=2)
    elif exp.weekday() == 6:
        exp += timedelta(days=1)
    return exp.isoformat(timespec='milliseconds').replace('+00:00', 'Z')

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_get_order_status(order_id):
    try:
        if not account_id or not order_id:
            logging.error("No account_id or order_id")
            return None
        url = f"{BASE_URL}/trading/{account_id}/order/{order_id}"
        resp = requests.get(url, headers=HEADERS, timeout=10)
        resp.raise_for_status()
        order_data = resp.json()
        status = order_data.get("status")
        filled_qty = float(order_data.get("filledQuantity", 0))
        avg_price = float(order_data.get("averagePrice", 0)) if order_data.get("averagePrice") else None
        if avg_price is not None and avg_price < MIN_PRICE:
            avg_price = MIN_PRICE
            logging.warning(f"Order {order_id} avg_price adjusted to ${MIN_PRICE:.8f}")
        price_color = GREEN if avg_price and avg_price >= MIN_PRICE else RED
        print(f"Order {order_id} status: {status}, filled: {filled_qty:.8f}, avg price: {price_color}${avg_price:.8f}{RESET}")
        logging.info(f"Order {order_id} status: {status}, filled: {filled_qty:.8f}, avg price: {avg_price:.8f}")
        return {
            "status": status,
            "filled_qty": filled_qty,
            "avg_price": avg_price
        }
    except Exception as e:
        logging.error(f"Order status fetch error for {order_id}: {e}")
        return None

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_list_all_orders():
    """List all orders and print full details for debugging."""
    try:
        if not account_id:
            logging.error("No BROKERAGE accountId")
            return []
        url = f"{BASE_URL}/trading/{account_id}/portfolio/v2"
        resp = requests.get(url, headers=HEADERS, timeout=10)
        resp.raise_for_status()
        data = resp.json()
        all_orders = data.get('orders', [])
        print(f"Retrieved {len(all_orders)} total orders.")
        for i, o in enumerate(all_orders, 1):
            print(f"\n--- Order {i} ---")
            print(json.dumps(o, indent=2))
        return all_orders
    except Exception as e:
        logging.error(f"Error listing orders: {e}")
        return []

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_cancel_order(order):
    """Cancel a single order using DELETE endpoint with accountId/orderId."""
    order_id = order.get('orderId') or order.get('id')
    symbol = order.get('instrument', {}).get('symbol')
    cancel_url = f"{BASE_URL}/trading/{account_id}/order/{order_id}"
    for attempt in range(1, RETRY_COUNT + 1):
        try:
            resp = requests.delete(cancel_url, headers=HEADERS, timeout=10)
            resp.raise_for_status()
            print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] Cancelled order {order_id} ({symbol})")
            if resp.content:
                try:
                    print("  Response:", json.dumps(resp.json(), indent=2))
                except Exception:
                    print("  Response text:", resp.text)
            return True
        except Exception as e:
            print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] Attempt {attempt} failed to cancel order {order_id} ({symbol}): {e}")
            if hasattr(e, 'response') and e.response is not None:
                try:
                    print("  Response:", e.response.json())
                except:
                    print("  Response text:", e.response.text)
            if attempt < RETRY_COUNT:
                time.sleep(2)
            else:
                print(f"Giving up on order {order_id} after {RETRY_COUNT} attempts.")
                return False

def ensure_no_open_orders(symbol):
    """Ensure no non-final orders exist for a symbol before placing new orders."""
    trading_symbol = get_trading_symbol(symbol)
    print(f"Checking for open orders for {trading_symbol} before placing new order...")
    logging.info(f"Checking for open orders for {trading_symbol}")
    all_orders = client_list_all_orders()
    open_orders = [o for o in all_orders if o.get('instrument', {}).get('symbol') == trading_symbol and o.get('status') not in ['FILLED', 'CANCELLED', 'REJECTED']]
    if not open_orders:
        print(f"No open orders found for {trading_symbol}.")
        logging.info(f"No open orders found for {trading_symbol}")
        return True
    print(f"Found {len(open_orders)} open orders for {trading_symbol}. Initiating cancellation process...")
    logging.info(f"Found {len(open_orders)} open orders for {trading_symbol}")
    for order in open_orders:
        if client_cancel_order(order):
            print(f"Cancelled order {order.get('orderId') or order.get('id')} for {trading_symbol}.")
            logging.info(f"Cancelled order {order.get('orderId') or order.get('id')} for {trading_symbol}")
        else:
            print(f"Failed to cancel order {order.get('orderId') or order.get('id')} for {trading_symbol}.")
            logging.error(f"Failed to cancel order {order.get('orderId') or order.get('id')} for {trading_symbol}")
    print("Waiting 30 seconds for cancellations to process...")
    time.sleep(30)
    all_orders = client_list_all_orders()
    open_orders = [o for o in all_orders if o.get('instrument', {}).get('symbol') == trading_symbol and o.get('status') not in ['FILLED', 'CANCELLED', 'REJECTED']]
    if open_orders:
        print(f"Warning: Still {len(open_orders)} open orders for {trading_symbol} after final check.")
        logging.warning(f"Still {len(open_orders)} open orders for {trading_symbol} after final check")
        return False
    print(f"Confirmed: No open orders for {trading_symbol}.")
    logging.info(f"Confirmed: No open orders for {trading_symbol}")
    return True

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def fetch_token_and_account():
    """Fetch new access token and brokerage account ID using YOUR_SECRET_KEY."""
    global access_token, account_id, HEADERS, last_token_fetch_time
    try:
        resp = requests.post(
            "https://api.public.com/userapiauthservice/personal/access-tokens",
            headers={"Content-Type": "application/json"},
            json={"secret": YOUR_SECRET_KEY, "validityInMinutes": 1440},
            timeout=10
        )
        print("Token endpoint response:", resp.status_code, resp.text)
        resp.raise_for_status()
        access_token = resp.json().get("accessToken")
        if not access_token:
            raise ValueError("No access token returned")
        resp = requests.get(
            f"{BASE_URL}/trading/account",
            headers={"Authorization": f"Bearer {access_token}", "Content-Type": "application/json"},
            timeout=10
        )
        print("Account endpoint response:", resp.status_code, resp.text)
        resp.raise_for_status()
        accounts = resp.json().get("accounts", [])
        brokerage = next((a for a in accounts if a.get("accountType") == "BROKERAGE"), None)
        if not brokerage:
            raise ValueError("No BROKERAGE account found")
        account_id = brokerage["accountId"]
        HEADERS = {"Authorization": f"Bearer {access_token}", "Content-Type": "application/json"}
        last_token_fetch_time = datetime.now()
        print(f"Access token and brokerage account fetched: {account_id}")
        logging.info(f"Access token and brokerage account fetched: {account_id}")
        return True
    except Exception as e:
        print("Error fetching token/account:", e)
        logging.error("Error fetching token/account:")
        traceback.print_exc()
        return False

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def refresh_token_if_needed():
    """Refresh token if older than 23 hours."""
    if task_running['refresh_token_if_needed']:
        print("refresh_token_if_needed already running. Skipping.")
        return False
    task_running['refresh_token_if_needed'] = True
    try:
        global last_token_fetch_time
        if not last_token_fetch_time or (datetime.now() - last_token_fetch_time) > timedelta(hours=23):
            print("Refreshing access token...")
            return fetch_token_and_account()
        return True
    finally:
        task_running['refresh_token_if_needed'] = False

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_get_account():
    try:
        if not account_id:
            logging.error("No BROKERAGE accountId")
            return {'equity': 0.0, 'buying_power_cash': 0.0, 'cash_only_buying_power': 0.0, 'cash_on_hand': 0.0, 'accountId': None}
        resp = requests.get(f"{BASE_URL}/trading/{account_id}/portfolio/v2", headers=HEADERS, timeout=10)
        resp.raise_for_status()
        account = resp.json()
        equity_list = account.get('equity', [])
        total_equity = round(sum(float(e.get('value', 0)) for e in equity_list), 2)
        cash_on_hand = round(sum(float(e.get('value', 0)) for e in equity_list if e.get('type') == 'CASH'), 2)
        buying_power_dict = account.get('buyingPower', {})
        buying_power_cash = round(float(buying_power_dict.get('buyingPower', 0)), 2)
        cash_only_buying_power = round(float(buying_power_dict.get('cashOnlyBuyingPower', 0)), 2)
        print(f"Account equity: ${total_equity:.2f}, Buying power cash: ${buying_power_cash:.2f}")
        return {
            'equity': total_equity,
            'buying_power_cash': buying_power_cash,
            'cash_only_buying_power': cash_only_buying_power,
            'cash_on_hand': cash_on_hand,
            'accountId': account_id
        }
    except Exception as e:
        logging.error(f"Account fetch error: {e}")
        return {'equity': 0.0, 'buying_power_cash': 0.0, 'cash_only_buying_power': 0.0, 'cash_on_hand': 0.0, 'accountId': account_id}

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_list_positions():
    """Fetch current positions from public.com API, with real-time prices from Public.com."""
    try:
        if not account_id:
            logging.error("No BROKERAGE accountId")
            return []
        resp = requests.get(f"{BASE_URL}/trading/{account_id}/portfolio/v2", headers=HEADERS, timeout=10)
        if resp.status_code >= 400:
            logging.error(f"Positions fetch failed: HTTP {resp.status_code} - {resp.text}")
            print(f"Positions fetch failed: HTTP {resp.status_code} - {resp.text}")
            return []
        resp.raise_for_status()
        data = resp.json()
        logging.info(f"Raw API response for positions: {json.dumps(data, indent=2)}")
        pos_list = data.get('positions', [])
        if not pos_list:
            logging.info("API returned empty positions list")
            print("API returned empty positions list")
            return []
        out = []
        for p in pos_list:
            try:
                if not isinstance(p, dict):
                    logging.warning(f"Skipping invalid position entry: {p}")
                    continue
                instrument = p.get('instrument', {})
                if not isinstance(instrument, dict):
                    logging.warning(f"Skipping position with invalid instrument: {p}")
                    continue
                api_sym = instrument.get('symbol')
                sym = get_internal_symbol(api_sym)
                asset_type = instrument.get('type', 'CRYPTO')
                try:
                    qty = float(p.get('quantity', 0))
                except (ValueError, TypeError):
                    logging.warning(f"Skipping position with invalid quantity: {p}")
                    continue
                cost_basis = p.get('costBasis', {})
                if not isinstance(cost_basis, dict):
                    logging.warning(f"Skipping position with invalid costBasis: {p}")
                    cost_basis = {}
                try:
                    avg = round(float(cost_basis.get('unitCost', 0)), 8)
                    if avg < MIN_PRICE:
                        avg = MIN_PRICE
                        logging.warning(f"Position avg_entry_price adjusted to ${MIN_PRICE:.8f} for {sym}")
                except (ValueError, TypeError):
                    logging.warning(f"Skipping position with invalid unitCost: {p}")
                    avg = MIN_PRICE
                last_price_dict = p.get('lastPrice', {})
                embedded_last_price = round(float(last_price_dict.get('lastPrice', 0)), 8) if last_price_dict.get('lastPrice') else None
                if embedded_last_price is None or embedded_last_price < MIN_PRICE:
                    last_price = client_get_quote(sym)
                else:
                    last_price = max(embedded_last_price, MIN_PRICE)
                if last_price is None:
                    logging.warning(f"No valid last price for {sym}. Setting to {MIN_PRICE}.")
                    last_price = MIN_PRICE
                instrument_gain = p.get('instrumentGain', {})
                try:
                    gain_percentage = float(instrument_gain.get('gainPercentage', 0))
                except (ValueError, TypeError):
                    gain_percentage = None
                    logging.warning(f"Invalid gain percentage for {sym}: {instrument_gain}")
                opened_at = p.get('openedAt', datetime.now(eastern).strftime("%Y-%m-%d"))
                try:
                    date_str = datetime.fromisoformat(opened_at.replace('Z', '+00:00')).astimezone(eastern).strftime("%Y-%m-%d")
                except ValueError:
                    date_str = datetime.now(eastern).strftime("%Y-%m-%d")
                if sym and qty > 0:
                    out.append({
                        'symbol': sym,
                        'qty': qty,
                        'avg_entry_price': avg,
                        'purchase_date': date_str,
                        'type': asset_type,
                        'last_price': last_price,
                        'gain_percentage': gain_percentage
                    })
            except Exception as e:
                logging.error(f"Error processing position: {p}, Error: {e}")
                print(f"Error processing position: {p}, Error: {e}")
                continue
        logging.info(f"Found {len(out)} valid positions")
        print(f"Found {len(out)} valid positions")
        return out
    except Exception as e:
        logging.error(f"Positions fetch error: {e}")
        print(f"Positions fetch error: {e}")
        return []

def list_owned_positions():
    """List owned equity and crypto positions."""
    api_positions = client_list_positions()
    if not api_positions:
        print("No positions found via API.")
        logging.info("No positions found via API.")
        return []

    position_list = []
    for pos in api_positions:
        sym = pos['symbol']
        qty = pos['qty']
        avg_price = pos['avg_entry_price']
        asset_type = pos['type']
        last_price = pos['last_price']
        gain_percentage = pos['gain_percentage']
        if qty > 0:
            current_price = client_get_quote(sym)
            if current_price is None:
                current_price = MIN_PRICE
            position_list.append({
                'symbol': sym,
                'qty': qty,
                'avg_price': avg_price,
                'current_price': current_price,
                'type': asset_type,
                'gain_percentage': gain_percentage
            })

    if not position_list:
        print("No valid positions to display.")
        logging.info("No valid positions to display")
        return []

    crypto_positions = [pos for pos in position_list if pos['type'] == 'CRYPTO']

    print("\nCrypto Owned Positions:")
    if crypto_positions:
        for i, pos in enumerate(crypto_positions, 1):
            sym = pos['symbol']
            qty = pos['qty']
            avg_price = pos['avg_price']
            current_price = pos['current_price']
            gain_percentage = pos['gain_percentage']
            price_display = f"{current_price:.8f}" if current_price >= MIN_PRICE else f"{MIN_PRICE:.8f}"
            gain_color = GREEN if gain_percentage and gain_percentage >= 0 else RED
            gain_display = f"{gain_percentage:.2f}%" if gain_percentage is not None else 'N/A'
            print(f"{i}. {sym} - {qty:.8f} units at avg price ${avg_price:.8f}, "
                  f"Current price: ${price_display}, Gain: {gain_color}{gain_display}{RESET}")
    else:
        print("No crypto positions.")

    return position_list

def sync_db_with_api():
    if task_running['sync_db_with_api']:
        print("sync_db_with_api already running. Skipping.")
        return
    task_running['sync_db_with_api'] = True
    try:
        session = SessionLocal()
        try:
            for attempt in range(3):
                try:
                    api_positions = client_list_positions()
                    break
                except Exception as e:
                    logging.error(f"Retry {attempt + 1}/3: Error syncing DB with API: {e}")
                    time.sleep(2 ** attempt)
                    if attempt == 2:
                        logging.error("All retries failed for syncing DB with API.")
                        return
            api_symbols = {pos['symbol'] for pos in api_positions}
            positions_to_delete = []
            for pos in api_positions:
                symbol = pos['symbol']
                if symbol != 'BTC':
                    continue  # Only sync BTC
                qty = pos['qty']
                avg_price = pos['avg_entry_price']
                purchase_date = pos['purchase_date']
                if avg_price < MIN_PRICE or qty <= 0:
                    logging.warning(f"Skipping DB update for {symbol}: Invalid avg_price (${avg_price:.8f}) or quantity ({qty:.8f})")
                    continue
                db_pos = session.query(Position).filter_by(symbols=symbol).first()
                if db_pos:
                    db_pos.quantity = qty
                    db_pos.avg_price = avg_price
                    db_pos.purchase_date = purchase_date
                else:
                    db_pos = Position(
                        symbols=symbol,
                        quantity=qty,
                        avg_price=avg_price,
                        purchase_date=purchase_date
                    )
                    session.add(db_pos)
            for db_pos in session.query(Position).all():
                if db_pos.symbols not in api_symbols or db_pos.quantity <= 0 or db_pos.avg_price < MIN_PRICE:
                    positions_to_delete.append(db_pos)
            for db_pos in positions_to_delete:
                if db_pos.stop_order_id:
                    client_cancel_order({'orderId': db_pos.stop_order_id, 'instrument': {'symbol': get_trading_symbol(db_pos.symbols)}})
                logging.info(f"Deleting position for {db_pos.symbols} with quantity {db_pos.quantity:.8f} and avg_price ${db_pos.avg_price:.8f}")
                session.delete(db_pos)
            session.commit()
            print("Database synced with API for BTC.")
            logging.info("Database synced with API for BTC")
        except Exception as e:
            session.rollback()
            logging.error(f"Error syncing DB with API: {e}")
            print(f"Error syncing DB with API: {e}")
        finally:
            session.close()
    finally:
        task_running['sync_db_with_api'] = False

def load_positions_from_database():
    print("Loading BTC position from database...")
    with db_lock:
        session = SessionLocal()
        try:
            positions = session.query(Position).filter(Position.symbols == 'BTC').all()
            symbols_to_sell_dict = {}
            for position in positions:
                symbols_to_sell = position.symbols
                avg_price = max(position.avg_price, MIN_PRICE)
                purchase_date = position.purchase_date
                symbols_to_sell_dict[symbols_to_sell] = (avg_price, purchase_date)
            print(f"Loaded {len(symbols_to_sell_dict)} BTC position from database.")
            return symbols_to_sell_dict
        finally:
            session.close()

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def calculate_technical_indicators(symbol, lookback_days=200):
    print(f"Calculating technical indicators for {symbol} using ccxt...")
    logging.info(f"Calculating technical indicators for {symbol}")
    exchange = ccxt.coinbase()
    symbol_usd = f"{symbol}/USD"
    try:
        data = exchange.fetch_ohlcv(symbol_usd, timeframe='1d', limit=lookback_days)
        historical_data = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        historical_data['timestamp'] = pd.to_datetime(historical_data['timestamp'], unit='ms')
        historical_data.set_index('timestamp', inplace=True)
        if historical_data.empty or len(historical_data) < lookback_days:
            logging.error(f"Insufficient data for {symbol} (rows: {len(historical_data)})")
            print(f"Insufficient data for {symbol} (rows: {len(historical_data)}).")
            return None
        historical_data = historical_data.dropna(subset=['open', 'high', 'low', 'close'])
        if len(historical_data) < 35:
            logging.error(f"After cleaning, insufficient data for {symbol} (rows: {len(historical_data)})")
            print(f"After cleaning, insufficient data for {symbol} (rows: {len(historical_data)}).")
            return None
        short_window = 12
        long_window = 26
        signal_window = 9
        try:
            macd, signal, _ = talib.MACD(historical_data['close'].values,
                                         fastperiod=short_window,
                                         slowperiod=long_window,
                                         signalperiod=signal_window)
            historical_data['macd'] = macd
            historical_data['signal'] = signal
        except Exception as e:
            print(f"Error calculating MACD for {symbol}: {e}")
            logging.error(f"Error calculating MACD for {symbol}: {e}")
            historical_data['macd'] = np.nan
            historical_data['signal'] = np.nan
        try:
            rsi = talib.RSI(historical_data['close'].values, timeperiod=14)
            historical_data['rsi'] = rsi
        except Exception as e:
            print(f"Error calculating RSI for {symbol}: {e}")
            logging.error(f"Error calculating RSI for {symbol}: {e}")
            historical_data['rsi'] = np.nan
        try:
            upper, middle, lower = talib.BBANDS(historical_data['close'].values, timeperiod=20, nbdevup=2, nbdevdn=2)
            historical_data['upper_bb'] = upper
            historical_data['middle_bb'] = middle
            historical_data['lower_bb'] = lower
        except Exception as e:
            print(f"Error calculating BB for {symbol}: {e}")
            logging.error(f"Error calculating BB for {symbol}: {e}")
            historical_data['upper_bb'] = np.nan
            historical_data['middle_bb'] = np.nan
            historical_data['lower_bb'] = np.nan
        try:
            historical_data['sma_200'] = talib.SMA(historical_data['close'].values, timeperiod=200)
        except Exception as e:
            print(f"Error calculating SMA for {symbol}: {e}")
            logging.error(f"Error calculating SMA for {symbol}: {e}")
            historical_data['sma_200'] = np.nan
        try:
            historical_data['typical_price'] = (historical_data['high'] + historical_data['low'] + historical_data['close']) / 3
            historical_data['vwap'] = (historical_data['typical_price'] * historical_data['volume']).cumsum() / historical_data['volume'].cumsum()
        except Exception as e:
            print(f"Error calculating VWAP for {symbol}: {e}")
            logging.error(f"Error calculating VWAP for {symbol}: {e}")
            historical_data['vwap'] = np.nan
        try:
            historical_data['adx'] = talib.ADX(historical_data['high'].values, historical_data['low'].values, historical_data['close'].values, timeperiod=14)
            historical_data['plus_di'] = talib.PLUS_DI(historical_data['high'].values, historical_data['low'].values, historical_data['close'].values, timeperiod=14)
            historical_data['minus_di'] = talib.MINUS_DI(historical_data['high'].values, historical_data['low'].values, historical_data['close'].values, timeperiod=14)
        except Exception as e:
            print(f"Error calculating ADX for {symbol}: {e}")
            logging.error(f"Error calculating ADX for {symbol}: {e}")
            historical_data['adx'] = np.nan
            historical_data['plus_di'] = np.nan
            historical_data['minus_di'] = np.nan
        try:
            slowk, slowd = talib.STOCH(historical_data['high'].values, historical_data['low'].values, historical_data['close'].values, fastk_period=14, slowk_period=3, slowd_period=3)
            historical_data['slowk'] = slowk
            historical_data['slowd'] = slowd
        except Exception as e:
            print(f"Error calculating Stochastic for {symbol}: {e}")
            logging.error(f"Error calculating Stochastic for {symbol}: {e}")
            historical_data['slowk'] = np.nan
            historical_data['slowd'] = np.nan
        historical_data['volume'] = historical_data['volume']
        print(f"Technical indicators calculated for {symbol}.")
        logging.info(f"Technical indicators calculated for {symbol}")
        print_technical_indicators(symbol, historical_data)
        return historical_data
    except Exception as e:
        logging.error(f"Error fetching OHLCV for {symbol}: {e}")
        print(f"Error fetching OHLCV for {symbol}: {e}")
        return None

def print_technical_indicators(symbol, historical_data):
    print(f"\nTechnical Indicators for {symbol}:\n")
    tail_data = historical_data[['close', 'macd', 'signal', 'rsi', 'upper_bb', 'middle_bb', 'lower_bb', 'sma_200', 'vwap', 'adx', 'plus_di', 'minus_di', 'volume', 'slowk', 'slowd']].tail()
    for idx, row in tail_data.iterrows():
        close_color = GREEN if row['close'] >= MIN_PRICE else RED
        macd_value = row['macd']
        signal_value = row['signal']
        if np.isnan(macd_value) or np.isnan(signal_value):
            macd_display = "N/A"
            signal_display = "N/A"
            macd_color = YELLOW
        else:
            macd_display = f"{macd_value:.4f}"
            signal_display = f"{signal_value:.4f}"
            macd_color = GREEN if macd_value >= signal_value else RED
        rsi_value = row['rsi']
        rsi_display = f"{rsi_value:.2f}" if not np.isnan(rsi_value) else "50.00"
        upper_bb = row['upper_bb']
        middle_bb = row['middle_bb']
        lower_bb = row['lower_bb']
        upper_display = f"{upper_bb:.8f}" if not np.isnan(upper_bb) else "N/A"
        middle_display = f"{middle_bb:.8f}" if not np.isnan(middle_bb) else "N/A"
        lower_display = f"{lower_bb:.8f}" if not np.isnan(lower_bb) else "N/A"
        sma_200 = row['sma_200']
        sma_display = f"{sma_200:.8f}" if not np.isnan(sma_200) else "N/A"
        vwap = row['vwap']
        vwap_display = f"{vwap:.8f}" if not np.isnan(vwap) else "N/A"
        adx = row['adx']
        plus_di = row['plus_di']
        minus_di = row['minus_di']
        adx_display = f"{adx:.2f}" if not np.isnan(adx) else "N/A"
        plus_di_display = f"{plus_di:.2f}" if not np.isnan(plus_di) else "N/A"
        minus_di_display = f"{minus_di:.2f}" if not np.isnan(minus_di) else "N/A"
        slowk = row['slowk']
        slowd = row['slowd']
        slowk_display = f"{slowk:.2f}" if not np.isnan(slowk) else "N/A"
        slowd_display = f"{slowd:.2f}" if not np.isnan(slowd) else "N/A"
        print(f"Time: {idx} | Close: {close_color}${row['close']:.8f}{RESET} | "
              f"MACD: {macd_color}{macd_display}{RESET} (Signal: {signal_display}) | "
              f"RSI: {rsi_display} | Upper BB: {upper_display} | Middle BB: {middle_display} | Lower BB: {lower_display} | "
              f"SMA200: {sma_display} | VWAP: {vwap_display} | ADX: {adx_display} | +DI: {plus_di_display} | -DI: {minus_di_display} | Volume: {row['volume']:.0f} | "
              f"SlowK: {slowk_display} | SlowD: {slowd_display}")
    print("")

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def get_average_true_range(symbol):
    print(f"Calculating ATR for {symbol} using ccxt...")
    logging.info(f"Calculating ATR for {symbol}")
    def _fetch_atr(symbol):
        exchange = ccxt.coinbase()
        symbol_usd = f"{symbol}/USD"
        try:
            data = exchange.fetch_ohlcv(symbol_usd, timeframe='1d', limit=30)
            df = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
            atr = talib.ATR(df['high'].values, df['low'].values, df['close'].values, timeperiod=22)
            atr_value = atr[-1]
            print(f"ATR value for {symbol}: {atr_value:.8f}")
            logging.info(f"ATR value for {symbol}: {atr_value:.8f}")
            return atr_value
        except Exception as e:
            logging.error(f"Error calculating ATR for {symbol}: {e}")
            print(f"Error calculating ATR for {symbol}: {e}")
            return None
    return get_cached_data(symbol, 'atr', _fetch_atr, symbol)

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def get_14_day_avg_range(symbol):
    print(f"Calculating 14-day average price range for {symbol}...")
    logging.info(f"Calculating 14-day average price range for {symbol}")
    exchange = ccxt.coinbase()
    symbol_usd = f"{symbol}/USD"
    try:
        data = exchange.fetch_ohlcv(symbol_usd, timeframe='1d', limit=14)
        df = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        avg_high = df['high'].mean()
        avg_low = df['low'].mean()
        print(f"14-day avg high for {symbol}: {avg_high:.8f}, avg low: {avg_low:.8f}")
        logging.info(f"14-day avg high for {symbol}: {avg_high:.8f}, avg low: {avg_low:.8f}")
        return avg_high, avg_low
    except Exception as e:
        logging.error(f"Error calculating 14-day avg range for {symbol}: {e}")
        print(f"Error calculating 14-day avg range for {symbol}: {e}")
        return None, None

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def calculate_buy_points(symbol):
    points = 0
    current_price = client_get_quote(symbol)
    if current_price is None:
        return 0
    avg_high, avg_low = get_14_day_avg_range(symbol)
    if avg_low is not None and current_price <= avg_low:
        return 100

    historical_data = calculate_technical_indicators(symbol)
    if historical_data is None:
        return 0

    previous_close = historical_data['close'].iloc[-1]

    # RSI (daily)
    rsi = historical_data['rsi'].iloc[-1]
    if not np.isnan(rsi) and rsi < 30:
        points += 25

    # MACD crossover
    macd = historical_data['macd']
    signal = historical_data['signal']
    if len(macd) >= 2 and not np.isnan(macd.iloc[-1]) and not np.isnan(signal.iloc[-1]) and not np.isnan(macd.iloc[-2]) and not np.isnan(signal.iloc[-2]):
        if macd.iloc[-1] > signal.iloc[-1] and macd.iloc[-2] < signal.iloc[-2]:
            points += 25

    # Volume
    volume = historical_data['volume']
    if volume.iloc[-1] > volume.mean():
        points += 25

    # Bollinger Bands
    lower_bb = historical_data['lower_bb'].iloc[-1]
    if not np.isnan(lower_bb) and current_price < lower_bb:
        points += 25

    atr = get_average_true_range(symbol)
    if atr is not None:
        atr_low = previous_close - 0.10 * atr
        if current_price < atr_low:
            points += 25

    # VWAP
    vwap = historical_data['vwap'].iloc[-1]
    if not np.isnan(vwap) and current_price > vwap:
        points += 25

    # SMA
    sma_200 = historical_data['sma_200'].iloc[-1]
    if not np.isnan(sma_200) and current_price > sma_200:
        points += 25

    # Trending momentum (ADX)
    adx = historical_data['adx'].iloc[-1]
    plus_di = historical_data['plus_di'].iloc[-1]
    minus_di = historical_data['minus_di'].iloc[-1]
    if not np.isnan(adx) and adx > 25 and not np.isnan(plus_di) and not np.isnan(minus_di) and plus_di > minus_di:
        points += 25

    # Stochastic
    slowk = historical_data['slowk'].iloc[-1]
    slowd = historical_data['slowd'].iloc[-1]
    if not np.isnan(slowk) and slowk < 20:
        points += 25
    if len(historical_data) >= 2:
        prev_slowk = historical_data['slowk'].iloc[-2]
        prev_slowd = historical_data['slowd'].iloc[-2]
        if not np.isnan(slowk) and not np.isnan(slowd) and not np.isnan(prev_slowk) and not np.isnan(prev_slowd):
            if slowk > slowd and prev_slowk < prev_slowd:
                points += 25

    # Bullish candlestick patterns
    points += get_candlestick_points(symbol, 'buy')

    print(f"Buy points for {symbol}: {points}")
    logging.info(f"Buy points for {symbol}: {points}")
    return points

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def calculate_sell_points(symbol):
    points = 0
    current_price = client_get_quote(symbol)
    if current_price is None:
        return 0
    avg_high, avg_low = get_14_day_avg_range(symbol)
    if avg_high is not None and current_price >= avg_high:
        return 100

    historical_data = calculate_technical_indicators(symbol)
    if historical_data is None:
        return 0

    previous_close = historical_data['close'].iloc[-1]

    # RSI (daily)
    rsi = historical_data['rsi'].iloc[-1]
    if not np.isnan(rsi) and rsi > 70:
        points += 25

    # MACD crossover
    macd = historical_data['macd']
    signal = historical_data['signal']
    if len(macd) >= 2 and not np.isnan(macd.iloc[-1]) and not np.isnan(signal.iloc[-1]) and not np.isnan(macd.iloc[-2]) and not np.isnan(signal.iloc[-2]):
        if macd.iloc[-1] < signal.iloc[-1] and macd.iloc[-2] > signal.iloc[-2]:
            points += 25

    # Volume
    volume = historical_data['volume']
    if volume.iloc[-1] > volume.mean():
        points += 25

    # Bollinger Bands
    upper_bb = historical_data['upper_bb'].iloc[-1]
    if not np.isnan(upper_bb) and current_price > upper_bb:
        points += 25

    atr = get_average_true_range(symbol)
    if atr is not None:
        atr_high = previous_close + 0.40 * atr
        if current_price > atr_high:
            points += 25

    # VWAP
    vwap = historical_data['vwap'].iloc[-1]
    if not np.isnan(vwap) and current_price < vwap:
        points += 25

    # SMA
    sma_200 = historical_data['sma_200'].iloc[-1]
    if not np.isnan(sma_200) and current_price < sma_200:
        points += 25

    # Trending momentum (ADX)
    adx = historical_data['adx'].iloc[-1]
    plus_di = historical_data['plus_di'].iloc[-1]
    minus_di = historical_data['minus_di'].iloc[-1]
    if not np.isnan(adx) and adx > 25 and not np.isnan(plus_di) and not np.isnan(minus_di) and plus_di < minus_di:
        points += 25

    # Stochastic
    slowk = historical_data['slowk'].iloc[-1]
    slowd = historical_data['slowd'].iloc[-1]
    if not np.isnan(slowk) and slowk > 80:
        points += 25
    if len(historical_data) >= 2:
        prev_slowk = historical_data['slowk'].iloc[-2]
        prev_slowd = historical_data['slowd'].iloc[-2]
        if not np.isnan(slowk) and not np.isnan(slowd) and not np.isnan(prev_slowk) and not np.isnan(prev_slowd):
            if slowk < slowd and prev_slowk > prev_slowd:
                points += 25

    # Bearish candlestick patterns
    points += get_candlestick_points(symbol, 'sell')

    print(f"Sell points for {symbol}: {points}")
    logging.info(f"Sell points for {symbol}: {points}")
    return points

def get_candlestick_points(symbol, side):
    exchange = ccxt.coinbase()
    symbol_usd = f"{symbol}/USD"
    try:
        data = exchange.fetch_ohlcv(symbol_usd, timeframe='5m', limit=20)
        df = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
        df.set_index('timestamp', inplace=True)
        if df.empty or len(df) < 3:
            return 0
        df = df.dropna(subset=['open', 'high', 'low', 'close'])
        if len(df) < 3:
            return 0
        open_ = df['open'].values
        high = df['high'].values
        low = df['low'].values
        close = df['close'].values
        lookback_candles = min(20, len(close))
        detected = False
        if side == 'buy':
            patterns = {
                'Hammer': talib.CDLHAMMER,
                'Bullish Engulfing': talib.CDLENGULFING,
                'Morning Star': talib.CDLMORNINGSTAR,
                'Piercing Line': talib.CDLPIERCING,
                'Three White Soldiers': talib.CDL3WHITESOLDIERS,
                'Dragonfly Doji': talib.CDLDRAGONFLYDOJI,
                'Inverted Hammer': talib.CDLINVERTEDHAMMER,
                'Tweezer Bottom': talib.CDLMATCHINGLOW
            }
            for name, func in patterns.items():
                res = func(open_, high, low, close)
                if res[-1] > 0:
                    detected = True
                    break
        elif side == 'sell':
            patterns = {
                'Bearish Engulfing': talib.CDLENGULFING,
                'Evening Star': talib.CDLEVENINGSTAR,
                'Dark Cloud Cover': talib.CDLDARKCLOUDCOVER,
                'Shooting Star': talib.CDLSHOOTINGSTAR,
                'Hanging Man': talib.CDLHANGINGMAN
            }
            for name, func in patterns.items():
                res = func(open_, high, low, close)
                if res[-1] < 0:
                    detected = True
                    break
        return 25 if detected else 0
    except Exception as e:
        logging.error(f"Error in candlestick detection for {symbol}: {e}")
        return 0

def get_previous_price(symbol):
    return previous_prices.get(symbol, client_get_quote(symbol) or MIN_PRICE)

def update_previous_price(symbol, current_price):
    previous_prices[symbol] = max(current_price, MIN_PRICE)

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def track_price_changes(symbol):
    """Track price changes for a given symbol, skipping equities and handling None prices."""
    api_positions = client_list_positions()
    api_positions_dict = {p['symbol']: p for p in api_positions}
    api_pos = api_positions_dict.get(symbol, {})
    asset_type = api_pos.get('type', 'CRYPTO')
    if asset_type == 'EQUITY':
        print(f"Skipping price tracking for {symbol}: Position type is EQUITY, not CRYPTO.")
        logging.info(f"Skipping price tracking for {symbol}: Position type is EQUITY, not CRYPTO")
        return
    
    print(f"Tracking price changes for {symbol}...")
    logging.info(f"Tracking price changes for {symbol}")
    
    current_price = client_get_quote(symbol)
    if current_price is None:
        current_price = MIN_PRICE
        print(f"No valid price data for {symbol} from Public.com. Using minimum price ${MIN_PRICE:.8f}.")
        logging.warning(f"No valid price data for {symbol} from Public.com. Using minimum price ${MIN_PRICE:.8f}")
    
    current_color = GREEN if current_price >= MIN_PRICE else RED
    print(f"{symbol}: Current price: {current_color}${current_price:.8f}{RESET}")
    logging.info(f"{symbol}: Current price: ${current_price:.8f}")
    
    try:
        price_history = data_cache.get(f"{symbol}_price_history", [])
        price_history.append({'price': current_price, 'timestamp': time.time()})
        if len(price_history) > 100:
            price_history = price_history[-100:]
        data_cache[f"{symbol}_price_history"] = price_history
        
        if len(price_history) > 1:
            previous_price = price_history[-2]['price']
            price_change = ((current_price - previous_price) / previous_price * 100) if previous_price >= MIN_PRICE else 0
            change_color = GREEN if price_change >= 0 else RED
            print(f"{symbol}: Price change: {change_color}{price_change:.2f}%{RESET}")
            logging.info(f"{symbol}: Price change: {price_change:.2f}%")
    except Exception as e:
        logging.error(f"Error tracking price changes for {symbol}: {e}")
        print(f"Error tracking price changes for {symbol}: {e}")

def check_price_moves():
    """Check price movements for crypto positions only."""
    print("Checking price movements...")
    logging.info("Checking price movements")
    api_positions = client_list_positions()
    crypto_symbols = [p['symbol'] for p in api_positions if p.get('type', 'CRYPTO') == 'CRYPTO']
    
    if 'BTC' not in crypto_symbols:
        print("BTC not found in crypto positions. Skipping price check.")
        logging.info("BTC not found in crypto positions. Skipping price check")
        return
    
    try:
        track_price_changes('BTC')
    except Exception as e:
        logging.error(f"Error checking price moves for BTC: {e}")
        print(f"Error checking price moves for BTC: {e}")

def print_database_tables():
    if PRINT_DATABASE:
        session = SessionLocal()
        try:
            print("\nTrade History In This Robot's Database:")
            print("\nCrypto | Buy or Sell | Quantity | Avg. Price | Date")
            for record in session.query(TradeHistory).filter(TradeHistory.symbols == 'BTC').all():
                print(f"{record.symbols} | {record.action} | {record.quantity:.8f} | ${record.price:.8f} | {record.date}")
            print("\nBTC Position in the Database To Sell:")
            print("\nCrypto | Quantity | Avg. Price | Date | Current Price | % Change")
            for record in session.query(Position).filter(Position.symbols == 'BTC').all():
                current_price = client_get_quote(record.symbols)
                if current_price is None:
                    current_price = MIN_PRICE
                percentage_change = ((current_price - record.avg_price) / record.avg_price * 100) if record.avg_price >= MIN_PRICE else 0
                color = GREEN if percentage_change >= 0 else RED
                price_color = GREEN if current_price >= MIN_PRICE else RED
                print(f"{record.symbols} | {record.quantity:.8f} | ${record.avg_price:.8f} | {record.purchase_date} | {price_color}${current_price:.8f}{RESET} | {color}{percentage_change:.2f}%{RESET}")
        except Exception as e:
            logging.error(f"Error printing database: {e}")
            print(f"Error printing database: {e}")
        finally:
            session.close()

def get_symbols_to_buy():
    print("Setting BTC as the only symbol to analyze...")
    logging.info("Setting BTC as the only symbol to analyze")
    return ['BTC']

def monitor_stop_losses():
    # Disabled for crypto
    pass

def check_stop_order_status():
    # Disabled for crypto
    pass

def poll_order_status(order_id, timeout=300):
    start_time = time.time()
    while time.time() - start_time < timeout:
        status_info = client_get_order_status(order_id)
        if status_info and status_info["status"] in ["FILLED", 'CANCELLED', 'REJECTED']:
            return status_info
        time.sleep(5)
    logging.warning(f"Order {order_id} status check timed out after {timeout} seconds.")
    print(f"Order {order_id} status check timed out after {timeout} seconds.")
    return None

def send_alert(message, subject="Trading Bot Alert"):
    if not CALLMEBOT_API_KEY or not CALLMEBOT_PHONE:
        logging.error("Missing CALLMEBOT_API_KEY or CALLMEBOT_PHONE environment variable.")
        print("Missing CALLMEBOT_API_KEY or CALLMEBOT_PHONE environment variable.")
        return
    full_message = f"{subject}: {message}"
    encoded_message = urllib.parse.quote_plus(full_message)
    url = f"https://api.callmebot.com/whatsapp.php?phone={CALLMEBOT_PHONE}&text={encoded_message}&apikey={CALLMEBOT_API_KEY}"
    try:
        response = requests.get(url, timeout=10)
        if response.status_code == 200:
            print(f"WhatsApp alert sent: {subject}")
            logging.info(f"WhatsApp alert sent: {subject}")
        else:
            print(f"Failed to send WhatsApp alert: {response.text}")
            logging.error(f"Failed to send WhatsApp alert: {response.text}")
    except Exception as e:
        logging.error(f"Error sending WhatsApp alert: {e}")
        print(f"Error sending WhatsApp alert: {e}")

YF_CALLS_PER_MINUTE = 60
CLIENT_CALLS_PER_MINUTE = 100
ONE_MINUTE = 60

@sleep_and_retry
@limits(calls=CLIENT_CALLS_PER_MINUTE, period=ONE_MINUTE)
def rate_limited_get_quote(sym):
    return client_get_quote(sym)

@sleep_and_retry
@limits(calls=YF_CALLS_PER_MINUTE, period=ONE_MINUTE)
def rate_limited_fetch_ohlcv(sym, timeframe, limit):
    exchange = ccxt.coinbase()
    symbol_usd = f"{sym}/USD"
    try:
        return exchange.fetch_ohlcv(symbol_usd, timeframe=timeframe, limit=limit)
    except Exception as e:
        logging.error(f"Error fetching OHLCV for {sym}: {e}")
        print(f"Error fetching OHLCV for {sym}: {e}")
        return []

def buy_cryptos(symbols_to_sell_dict):
    if task_running['buy_cryptos']:
        print("buy_cryptos already running. Skipping.")
        logging.info("buy_cryptos already running. Skipping")
        return
    task_running['buy_cryptos'] = True
    try:
        print("Starting buy_cryptos function...")
        logging.info("Starting buy_cryptos function")
        global price_history, last_stored
        sym = 'BTC'
        trading_sym = get_trading_symbol(sym)
        acc = client_get_account()
        total_equity = acc['equity']
        buying_power = float(acc['buying_power_cash'])
        print(f"Total account equity: ${total_equity:.2f}, Buying power: ${buying_power:.2f}")
        logging.info(f"Total account equity: ${total_equity:.2f}, Buying power: ${buying_power:.2f}")
        if buying_power < 10.00:
            print("Buying power < $10.00. Skipping all buys to maintain minimum balance.")
            logging.info("Buying power < $10.00. Skipping all buys to maintain minimum balance.")
            return
        positions = client_list_positions()
        current_exposure = sum(float(p['qty'] * (rate_limited_get_quote(p['symbol']) or p['avg_entry_price'])) for p in positions)
        max_new_exposure = total_equity * 0.98 - current_exposure
        exposure_color = GREEN if max_new_exposure >= 0 else RED
        print(f"Current exposure: ${current_exposure:.2f}, Max new exposure: {exposure_color}${max_new_exposure:.2f}{RESET}")
        logging.info(f"Current exposure: ${current_exposure:.2f}, Max new exposure: ${max_new_exposure:.2f}")
        if max_new_exposure <= 0:
            print("Portfolio exposure limit reached. No new buys.")
            logging.info("Portfolio exposure limit reached.")
            return
        current_price = rate_limited_get_quote(sym)
        if current_price is None:
            current_price = MIN_PRICE
            print(f"No valid price data for {sym}. Using minimum price ${MIN_PRICE:.8f}.")
            logging.info(f"No valid price data for {sym}. Using minimum price ${MIN_PRICE:.8f}")
        data = rate_limited_fetch_ohlcv(sym, '1d', 200)
        df = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        if df.empty or len(df) < 20:
            print(f"Insufficient historical data for {sym} (daily rows: {len(df)}). Skipping.")
            logging.info(f"Insufficient historical data for {sym} (daily rows: {len(df)}). Skipping")
            return
        points = calculate_buy_points(sym)
        if points >= POINT_THRESHOLD:
            print(f"{sym}: Buy signal detected (Points: {points})")
            logging.info(f"{sym}: Buy signal detected (Points: {points})")
        else:
            print(f"{sym}: No buy signal (Points: {points})")
            logging.info(f"{sym}: No buy signal (Points: {points})")
            return
        session = SessionLocal()
        try:
            print(f"\n{'='*60}")
            print(f"Processing buy for {sym}...")
            print(f"{'='*60}")
            logging.info(f"Processing buy for {sym}")
            today_date = datetime.today().date()
            today_date_str = today_date.strftime("%Y-%m-%d")
            current_datetime = datetime.now(eastern)
            current_time_str = current_datetime.strftime("Eastern Time | %I:%M:%S %p | %m-%d-%Y |")
            print(f"Analysis time: {current_time_str}")
            logging.info(f"Analysis time: {current_time_str}")
            if not ensure_no_open_orders(sym):
                print(f"Cannot buy {sym}: Open orders still exist after cancellation attempt.")
                logging.info(f"Cannot buy {sym}: Open orders still exist after cancellation attempt.")
                return
            acc = client_get_account()
            buying_power = float(acc['buying_power_cash'])
            print(f"Current buying power before buying {sym}: ${buying_power:.2f}")
            logging.info(f"Current buying power before buying {sym}: ${buying_power:.2f}")
            if buying_power < 10.00:
                print(f"Buying power < $10.00. Stopping buy orders.")
                logging.info(f"Buying power < $10.00. Stopping buy orders.")
                return
            dollar_amount = allocation_per_risk.get(risk_levels.get(sym, "ultra-low"), 10.0)
            if ALL_BUY_ORDERS_ARE_5_DOLLARS:
                dollar_amount = 5.00
            if dollar_amount > buying_power - 5.00:
                dollar_amount = max(buying_power - 5.00, 0.0)
            if dollar_amount < 1.00:
                print(f"Insufficient buying power for {sym}. Stopping.")
                logging.info(f"Insufficient buying power for {sym}. Stopping.")
                return
            qty = dollar_amount / current_price if current_price >= MIN_PRICE else 0
            if qty <= 0:
                print(f"Invalid quantity for {sym}. Skipping.")
                logging.info(f"Invalid quantity for {sym}. Skipping.")
                return
            print(f"Attempting to buy ${dollar_amount:.2f} ({qty:.8f} of {sym})...")
            logging.info(f"Attempting to buy ${dollar_amount:.2f} ({qty:.8f} of {sym})")
            order_id = client_place_order(trading_sym, "BUY", amount=dollar_amount)
            if order_id:
                print(f"Buy order placed for ${dollar_amount:.2f} of {sym}, Order ID: {order_id}")
                logging.info(f"Buy order placed for ${dollar_amount:.2f} of {sym}, Order ID: {order_id}")
                status_info = poll_order_status(order_id)
                if status_info and status_info["status"] == "FILLED":
                    filled_qty = status_info["filled_qty"]
                    filled_price = status_info["avg_price"]
                    if filled_price is None or filled_price < MIN_PRICE:
                        filled_price = current_price
                        logging.warning(f"Invalid filled_price for {sym} order {order_id}. Using current_price ${current_price:.8f}.")
                    if filled_price < MIN_PRICE:
                        logging.error(f"Cannot record trade for {sym}: Filled price is invalid (${filled_price:.8f}). Using ${MIN_PRICE:.8f}.")
                        filled_price = MIN_PRICE
                    trade = TradeHistory(
                        symbols=sym,
                        action='buy',
                        quantity=filled_qty,
                        price=filled_price,
                        date=today_date_str
                    )
                    session.add(trade)
                    position = session.query(Position).filter_by(symbols=sym).first()
                    if position:
                        if position.avg_price < MIN_PRICE:
                            position.avg_price = filled_price
                            logging.warning(f"Corrected invalid avg_price for {sym} in database to ${filled_price:.8f}.")
                        total_qty = position.quantity + filled_qty
                        total_cost = (position.quantity * position.avg_price) + (filled_qty * filled_price)
                        position.avg_price = total_cost / total_qty if total_qty else filled_price
                        position.quantity = total_qty
                    else:
                        position = Position(
                            symbols=sym,
                            quantity=filled_qty,
                            avg_price=filled_price,
                            purchase_date=today_date_str
                        )
                        session.add(position)
                    session.commit()
                    with open(csv_filename, mode='a', newline='') as csv_file:
                        csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
                        csv_writer.writerow({
                            'Date': today_date_str,
                            'Buy': 'Buy',
                            'Sell': ' ',
                            'Quantity': filled_qty,
                            'Symbol': sym,
                            'Price Per Share': filled_price
                        })
                    send_alert(
                        f"Bought {filled_qty:.8f} of {sym} at ${filled_price:.8f}",
                        subject=f"Trade Executed: Bought {sym}"
                    )
                    acc = client_get_account()
                    buying_power = float(acc['buying_power_cash'])
                    print(f"Updated buying power after buying {sym}: ${buying_power:.2f}")
                    logging.info(f"Updated buying power after buying {sym}: ${buying_power:.2f}")
                else:
                    print(f"Buy order for {sym} not filled or failed (Status: {status_info['status'] if status_info else 'Unknown'}).")
                    logging.info(f"Buy order for {sym} not filled or failed (Status: {status_info['status'] if status_info else 'Unknown'}).")
            else:
                print(f"Failed to place buy order for {sym}.")
                logging.info(f"Failed to place buy order for {sym}.")
        except Exception as e:
            session.rollback()
            logging.error(f"Error in buy_cryptos: {e}")
            print(f"Error in buy_cryptos: {e}")
        finally:
            session.close()
    finally:
        task_running['buy_cryptos'] = False


def sell_cryptos():
    if task_running['sell_cryptos']:
        print("sell_cryptos already running. Skipping.")
        logging.info("sell_cryptos already running. Skipping")
        return
    task_running['sell_cryptos'] = True
    try:
        print("\nStarting sell_cryptos function...")
        logging.info("Starting sell_cryptos function")
        sync_db_with_api()
        list_owned_positions()
        session = SessionLocal()
        try:
            api_positions = client_list_positions()
            api_positions_dict = {p['symbol']: p for p in api_positions}
            positions = session.query(Position).filter(Position.quantity > 0.000000001, Position.symbols == 'BTC').all()
            if not positions:
                print("No BTC positions to sell.")
                logging.info("No BTC positions to sell")
                return
            for pos in positions:
                sym = pos.symbols
                trading_sym = get_trading_symbol(sym)
                api_pos = api_positions_dict.get(sym, {})
                asset_type = api_pos.get('type', 'CRYPTO')
                if asset_type == 'EQUITY':
                    print(f"Skipping {sym}: Position type is EQUITY, not CRYPTO.")
                    logging.info(f"Skipping {sym}: Position type is EQUITY, not CRYPTO")
                    continue
                print(f"\n{'='*60}")
                print(f"Evaluating {sym} for sell signal...")
                print(f"{'='*60}")
                logging.info(f"Evaluating {sym} for sell signal")
                current_price = client_get_quote(sym)
                if current_price is None:
                    current_price = MIN_PRICE
                    print(f"No valid price data for {sym} from Public.com. Using minimum price ${MIN_PRICE:.8f}.")
                    logging.info(f"No valid price data for {sym} from Public.com. Using minimum price ${MIN_PRICE:.8f}")
                api_avg_price = api_pos.get('avg_entry_price', MIN_PRICE)
                db_avg_price = max(pos.avg_price, MIN_PRICE)
                if api_avg_price >= MIN_PRICE:
                    avg_price = api_avg_price
                    logging.info(f"Using API avg_price for {sym}: ${api_avg_price:.8f}")
                else:
                    avg_price = db_avg_price
                    logging.info(f"Falling back to DB avg_price for {sym}: ${db_avg_price:.8f}")
                profit_pct = api_pos.get('gain_percentage')
                if profit_pct is None:
                    profit_pct = ((current_price - avg_price) / avg_price * 100) if avg_price >= MIN_PRICE else 0
                profit_color = GREEN if profit_pct >= 0 else RED
                print(f"{sym}: Current price: {profit_color}${current_price:.8f}{RESET}, "
                      f"Avg price: ${avg_price:.8f} (API: ${api_avg_price:.8f}, DB: ${db_avg_price:.8f}), "
                      f"Profit: {profit_color}{profit_pct:.2f}%{RESET}")
                qty_to_sell = pos.quantity
                if qty_to_sell <= 0.000000001:
                    print(f"Invalid quantity {qty_to_sell:.8f} for {sym}. Skipping.")
                    logging.info(f"Invalid quantity {qty_to_sell:.8f} for {sym}. Skipping")
                    continue
                points = calculate_sell_points(sym)
                print(f"Sell points for {sym}: {points}")
                logging.info(f"Sell points for {sym}: {points}")
                profit_threshold = 10.0  # Profit percentage to trigger sell
                loss_threshold = -10.0  # Loss percentage to trigger sell
                if points >= POINT_THRESHOLD or profit_pct >= profit_threshold or profit_pct <= loss_threshold:
                    print(f"{sym}: Sell signal detected (Points: {points}, Profit: {profit_pct:.2f}%)")
                    logging.info(f"{sym}: Sell signal detected (Points: {points}, Profit: {profit_pct:.2f}%)")
                    if not ensure_no_open_orders(sym):
                        print(f"Cannot sell {sym}: Open orders still exist after cancellation attempt.")
                        logging.info(f"Cannot sell {sym}: Open orders still exist after cancellation attempt.")
                        continue
                    print(f"Attempting to sell {qty_to_sell:.8f} of {sym} at market price...")
                    logging.info(f"Attempting to sell {qty_to_sell:.8f} of {sym} at market price")
                    order_id = client_place_order(trading_sym, "SELL", quantity=qty_to_sell)
                    if order_id:
                        print(f"Sell order placed for {qty_to_sell:.8f} of {sym}, Order ID: {order_id}")
                        logging.info(f"Sell order placed for {qty_to_sell:.8f} of {sym}, Order ID: {order_id}")
                        status_info = poll_order_status(order_id)
                        if status_info and status_info["status"] == "FILLED":
                            filled_qty = status_info["filled_qty"]
                            filled_price = status_info["avg_price"]
                            if filled_price is None or filled_price < MIN_PRICE:
                                filled_price = current_price
                                logging.warning(f"Invalid filled_price for {sym} order {order_id}. Using current_price ${current_price:.8f}.")
                            if filled_price < MIN_PRICE:
                                logging.error(f"Cannot record trade for {sym}: Filled price is invalid (${filled_price:.8f}). Using ${MIN_PRICE:.8f}.")
                                filled_price = MIN_PRICE
                            trade = TradeHistory(
                                symbols=sym,
                                action='sell',
                                quantity=filled_qty,
                                price=filled_price,
                                date=today_date_str
                            )
                            session.add(trade)
                            position = session.query(Position).filter_by(symbols=sym).first()
                            if position:
                                position.quantity -= filled_qty
                                if position.quantity <= 0.000000001:
                                    if position.stop_order_id:
                                        client_cancel_order({'orderId': position.stop_order_id, 'instrument': {'symbol': trading_sym}})
                                    session.delete(position)
                            session.commit()
                            with open(csv_filename, mode='a', newline='') as csv_file:
                                csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
                                csv_writer.writerow({
                                    'Date': today_date_str,
                                    'Buy': ' ',
                                    'Sell': 'Sell',
                                    'Quantity': filled_qty,
                                    'Symbol': sym,
                                    'Price Per Share': filled_price
                                })
                            profit = (filled_price - avg_price) * filled_qty
                            profit_color = GREEN if profit >= 0 else RED
                            print(f"Sold {filled_qty:.8f} of {sym} at {profit_color}${filled_price:.8f}{RESET}, Profit: {profit_color}${profit:.2f}{RESET}")
                            logging.info(f"Sold {filled_qty:.8f} of {sym} at ${filled_price:.8f}, Profit: ${profit:.2f}")
                            send_alert(
                                f"Sold {filled_qty:.8f} of {sym} at ${filled_price:.8f}, Profit: ${profit:.2f}",
                                subject=f"Trade Executed: Sold {sym}"
                            )
                        else:
                            print(f"Sell order for {sym} not filled or failed (Status: {status_info['status'] if status_info else 'Unknown'}).")
                            logging.info(f"Sell order for {sym} not filled or failed (Status: {status_info['status'] if status_info else 'Unknown'}).")
                    else:
                        print(f"Failed to place sell order for {sym}.")
                        logging.info(f"Failed to place sell order for {sym}.")
                else:
                    print(f"{sym}: No sell signal (Points: {points}, Profit: {profit_pct:.2f}%)")
                    logging.info(f"{sym}: No sell signal (Points: {points}, Profit: {profit_pct:.2f}%)")
        except Exception as e:
            session.rollback()
            logging.error(f"Error in sell_cryptos: {e}")
            print(f"Error in sell_cryptos: {e}")
        finally:
            session.close()
    finally:
        task_running['sell_cryptos'] = False


def check_for_signals():
    """Check for buy/sell signals and execute trades."""
    print("\nChecking for trading signals...")
    logging.info("Checking for trading signals")
    try:
        refresh_token_if_needed()
        cleanup_invalid_positions()
        sync_db_with_api()
        symbols_to_sell_dict = load_positions_from_database()
        print_database_tables()
        buy_cryptos(symbols_to_sell_dict)
        sell_cryptos()
        check_price_moves()
        list_owned_positions()
        print("\nFinished checking for signals.")
        logging.info("Finished checking for signals")
    except Exception as e:
        logging.error(f"Error in check_for_signals: {e}")
        print(f"Error in check_for_signals: {e}")

def is_trading_hours():
    """Check if current time is within trading hours (24/7 for crypto)."""
    return True  # Crypto markets are 24/7

def main_loop():
    """Main loop to run the trading bot."""
    print(f"Starting trading bot at {datetime.now(eastern).strftime('%Y-%m-%d %H:%M:%S %Z')}...")
    logging.info(f"Starting trading bot at {datetime.now(eastern).strftime('%Y-%m-%d %H:%M:%S %Z')}")
    if not fetch_token_and_account():
        print("Failed to initialize token and account. Exiting.")
        logging.error("Failed to initialize token and account. Exiting.")
        return
    initialize_csv()
    cleanup_invalid_positions()
    while True:
        try:
            if is_trading_hours():
                check_for_signals()
            else:
                print("Outside trading hours. Waiting...")
                logging.info("Outside trading hours. Waiting")
            print(f"Waiting 5 minutes before next check at {datetime.now(eastern).strftime('%Y-%m-%d %H:%M:%S %Z')}...")
            time.sleep(300)  # Wait 5 minutes
        except KeyboardInterrupt:
            print("\nTrading bot stopped by user.")
            logging.info("Trading bot stopped by user")
            break
        except Exception as e:
            logging.error(f"Error in main loop: {e}")
            print(f"Error in main loop: {e}")
            time.sleep(60)  # Wait 1 minute before retrying

if __name__ == "__main__":
    main_loop()
