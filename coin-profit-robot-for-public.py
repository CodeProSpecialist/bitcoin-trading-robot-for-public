import os
import time
import csv
import logging
import threading
from uuid import uuid4
from datetime import datetime, timedelta, timezone
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

# ANSI color codes
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
BLUE = "\033[94m"
MAGENTA = "\033[95m"
CYAN = "\033[96m"
RESET = "\033[0m"

# Configuration flags
PRINT_ROBOT_STORED_BUY_AND_SELL_LIST_DATABASE = True
PRINT_DATABASE = True
DEBUG = False
ALL_BUY_ORDERS_ARE_5_DOLLARS = False
FRACTIONAL_BUY_ORDERS = True
ENABLE_AUTOMATIC_STOP_LOSS_ORDERS = False
STOP_LOSS_PERCENTAGE = 0.05
POINT_THRESHOLD = 100

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
risk_levels = {"BTC": "ultra-low"}
allocation_per_risk = {"ultra-low": 10.0}
symbols_to_sell_dict = {}
today_date = datetime.today().date()
today_datetime = datetime.now(pytz.timezone('US/Eastern'))
csv_filename = 'log-file-of-buy-and-sell-signals-btc.csv'
fieldnames = ['Date', 'Buy', 'Sell', 'Quantity', 'Symbol', 'Price Per Share']
price_changes = {}
current_price = 0
today_date_str = today_date.strftime("%Y-%m-%d")
qty = 0
price_history = {}
last_stored = {}
interval_map = {
    '1min': 60, '5min': 300, '10min': 600, '15min': 900,
    '30min': 1800, '45min': 2700, '60min': 3600
}
crypto_data = {}
previous_prices = {}
data_cache = {}
CACHE_EXPIRY = 120
CALLS = 10
PERIOD = 1
RETRY_COUNT = 3
task_running = {
    'buy_cryptos': False, 'sell_cryptos': False, 'check_price_moves': False,
    'check_stop_order_status': False, 'monitor_stop_losses': False,
    'sync_db_with_api': False, 'refresh_token_if_needed': False
}
db_lock = threading.Lock()
eastern = pytz.timezone('US/Eastern')

# Logging configuration
logging.basicConfig(
    filename='trading-bot-program-logging-messages-btc.txt',
    level=logging.INFO,
    format='%(asctime)s %(levelname)s:%(message)s'
)

# Initialize CSV
def initialize_csv():
    with open(csv_filename, mode='w', newline='') as csv_file:
        csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
        csv_writer.writeheader()

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

# Initialize Database
def initialize_database():
    engine = create_engine('sqlite:///trading_bot_btc.db', connect_args={"check_same_thread": False})
    with engine.connect() as conn:
        conn.execute(text("PRAGMA journal_mode=WAL;"))
    SessionLocal = scoped_session(sessionmaker(bind=engine))
    Base.metadata.create_all(engine)
    return SessionLocal

SessionLocal = initialize_database()

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
        invalid_positions = session.query(Position).filter(Position.avg_price <= 0).all()
        for pos in invalid_positions:
            print(f"Deleting invalid position for {pos.symbols} with avg_price ${pos.avg_price:.2f}")
            logging.info(f"Deleting invalid position for {pos.symbols} with avg_price ${pos.avg_price:.2f}")
            if pos.stop_order_id:
                client_cancel_order({'orderId': pos.stop_order_id, 'instrument': {'symbol': pos.symbols}})
            session.delete(pos)
        session.commit()

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_get_quote(symbol, retries=3):
    for attempt in range(retries):
        try:
            return get_cached_data(symbol, 'current_price_ccxt', _fetch_current_price_ccxt, symbol)
        except Exception as e:
            if attempt == retries - 1:
                logging.error(f"All retries failed for {symbol}: {e}")
                return None
            time.sleep(2 ** attempt)
    return None

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def _fetch_current_price_ccxt(symbol):
    exchange = ccxt.coinbase()
    symbol_usd = f"{symbol}/USD"
    try:
        ticker = exchange.fetch_ticker(symbol_usd)
        last_price = float(ticker.get('last', 0))
        price_color = GREEN if last_price >= 0 else RED
        print(f"Coinbase last price for {symbol}: {price_color}${last_price:.4f}{RESET}")
        return round(last_price, 4)
    except Exception as e:
        logging.error(f"Error fetching price for {symbol} from Coinbase: {e}")
        print(f"Error fetching price for {symbol} from Coinbase: {e}")
        return None

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def place_market_order(symbol, side, fractional=False, amount=None, quantity=None):
    url = f"{BASE_URL}/trading/{account_id}/order"
    order_id = str(uuid4())
    is_fractional = fractional or (amount is not None) or (quantity is not None and quantity % 1 != 0)
    expiration = {"timeInForce": "DAY"}
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
            payload["quantity"] = f"{quantity:.5f}"
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
        else:
            order_response = place_stop_order(symbol, side, quantity, stop_price)
        if order_response.get('error'):
            logging.error(f"Order placement error for {symbol}: {order_response['error']}")
            return None
        order_id = order_response.get('orderId')
        if amount is not None:
            logging.info(f"Order placed: {side} ${amount:.2f} of {symbol}, Order ID: {order_id}")
        else:
            logging.info(f"Order placed: {side} {quantity} of {symbol}, Order ID: {order_id}")
        return order_id
    except Exception as e:
        logging.error(f"Order placement error for {symbol}: {e}")
        return None

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def place_stop_order(symbol, side, quantity, stop_price):
    url = f"{BASE_URL}/trading/{account_id}/order"
    order_id = str(uuid4())
    expiration = {"timeInForce": "GTD", "expirationTime": get_expiration()}
    payload = {
        "orderId": order_id,
        "instrument": {"symbol": symbol, "type": "CRYPTO"},
        "orderSide": side.upper(),
        "orderType": "STOP",
        "stopPrice": f"{stop_price:.2f}",
        "quantity": f"{quantity:.5f}",
        "expiration": expiration,
        "openCloseIndicator": "OPEN"
    }
    try:
        response = requests.post(url, headers=HEADERS, json=payload, timeout=10)
        response.raise_for_status()
        logging.info(f"Stop order placed successfully for {symbol}: {response.json()}")
        return response.json()
    except Exception as e:
        print(f"ERROR placing stop order for {symbol}:")
        logging.error(f"Error placing stop order for {symbol}: {e}")
        traceback.print_exc()
        return {"error": str(e)}

def get_expiration():
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
        price_color = GREEN if avg_price and avg_price >= 0 else RED
        print(f"Order {order_id} status: {status}, filled: {filled_qty}, avg price: {price_color}${avg_price:.2f}{RESET}")
        logging.info(f"Order {order_id} status: {status}, filled: {filled_qty}, avg price: {avg_price}")
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
    try:
        if not account_id:
            logging.error("No BROKERAGE accountId")
            return []
        url = f"{BASE_URL}/trading/{account_id}/portfolio/v2"
        resp = requests.get(url, headers=HEADERS, timeout=10)
        resp.raise_for_status()
        data = resp.json()
        all_orders = data.get('orders', [])
        return all_orders
    except Exception as e:
        logging.error(f"Error listing orders: {e}")
        return []

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def client_cancel_order(order):
    order_id = order.get('orderId') or order.get('id')
    symbol = order.get('instrument', {}).get('symbol')
    cancel_url = f"{BASE_URL}/trading/{account_id}/order/{order_id}"
    for attempt in range(1, RETRY_COUNT + 1):
        try:
            resp = requests.delete(cancel_url, headers=HEADERS, timeout=10)
            resp.raise_for_status()
            print(f"Cancelled order {order_id} ({symbol})")
            logging.info(f"Cancelled order {order_id} ({symbol})")
            return True
        except Exception as e:
            print(f"Attempt {attempt} failed to cancel order {order_id} ({symbol}): {e}")
            logging.error(f"Attempt {attempt} failed to cancel order {order_id} ({symbol}): {e}")
            if attempt < RETRY_COUNT:
                time.sleep(2)
            else:
                print(f"Giving up on order {order_id} after {RETRY_COUNT} attempts.")
                logging.error(f"Giving up on order {order_id} after {RETRY_COUNT} attempts")
                return False

def ensure_no_open_orders(symbol):
    print(f"Checking for open orders for {symbol}...")
    logging.info(f"Checking for open orders for {symbol}")
    all_orders = client_list_all_orders()
    open_orders = [o for o in all_orders if o.get('instrument', {}).get('symbol') == symbol and o.get('status') not in ['FILLED', 'CANCELLED', 'REJECTED']]
    if not open_orders:
        print(f"No open orders found for {symbol}.")
        logging.info(f"No open orders found for {symbol}")
        return True
    print(f"Found {len(open_orders)} open orders for {symbol}. Cancelling...")
    logging.info(f"Found {len(open_orders)} open orders for {symbol}")
    for order in open_orders:
        if client_cancel_order(order):
            print(f"Cancelled order {order.get('orderId') or order.get('id')} for {symbol}.")
            logging.info(f"Cancelled order {order.get('orderId') or order.get('id')} for {symbol}")
        else:
            print(f"Failed to cancel order {order.get('orderId') or order.get('id')} for {symbol}.")
            logging.error(f"Failed to cancel order {order.get('orderId') or order.get('id')} for {symbol}")
    print("Waiting 30 seconds for cancellations to process...")
    time.sleep(30)
    all_orders = client_list_all_orders()
    open_orders = [o for o in all_orders if o.get('instrument', {}).get('symbol') == symbol and o.get('status') not in ['FILLED', 'CANCELLED', 'REJECTED']]
    if open_orders:
        print(f"Warning: Still {len(open_orders)} open orders for {symbol}.")
        logging.warning(f"Still {len(open_orders)} open orders for {symbol}")
        return False
    print(f"Confirmed: No open orders for {symbol}.")
    logging.info(f"Confirmed: No open orders for {symbol}")
    return True

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def fetch_token_and_account():
    global access_token, account_id, HEADERS, last_token_fetch_time
    try:
        resp = requests.post(
            "https://api.public.com/userapiauthservice/personal/access-tokens",
            headers={"Content-Type": "application/json"},
            json={"secret": YOUR_SECRET_KEY, "validityInMinutes": 1440},
            timeout=10
        )
        resp.raise_for_status()
        access_token = resp.json().get("accessToken")
        if not access_token:
            raise ValueError("No access token returned")
        resp = requests.get(
            f"{BASE_URL}/trading/account",
            headers={"Authorization": f"Bearer {access_token}", "Content-Type": "application/json"},
            timeout=10
        )
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
        print(f"Error fetching token/account: {e}")
        logging.error(f"Error fetching token/account: {e}")
        traceback.print_exc()
        return False

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def refresh_token_if_needed():
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
    try:
        if not account_id:
            logging.error("No BROKERAGE accountId")
            return []
        url = f"{BASE_URL}/trading/{account_id}/portfolio/v2"
        resp = requests.get(url, headers=HEADERS, timeout=10)
        print(f"Raw API response for positions: {resp.status_code} {resp.text}")
        logging.info(f"Raw API response for positions: {resp.status_code} {resp.text}")
        resp.raise_for_status()
        data = resp.json() or {}
        pos_list = data.get('positions', [])
        out = []
        for p in pos_list:
            sym = p.get('instrument', {}).get('symbol')
            instr_type = p.get('instrument', {}).get('type')
            if instr_type != 'CRYPTO':
                continue
            qty = float(p.get('quantity', 0))
            qty = round(qty, 5)
            avg = round(float(p.get('costBasis', {}).get('unitCost', 0)), 2)
            opened_at = p.get('openedAt', datetime.now(eastern).strftime("%Y-%m-%d"))
            try:
                date_str = datetime.fromisoformat(opened_at.replace('Z', '+00:00')).astimezone(eastern).strftime("%Y-%m-%d")
            except ValueError:
                date_str = datetime.now(eastern).strftime("%Y-%m-%d")
            if sym and qty > 0:
                current_price = client_get_quote(sym)
                price_color = GREEN if current_price >= 0 else RED
                print(f"Position: {sym} | Type: CRYPTO | Qty: {qty:.5f} | Avg Price: ${avg:.2f} | Current Price: {price_color}${current_price:.2f}{RESET} | Purchase Date: {date_str}")
                logging.info(f"Position: {sym} | Type: CRYPTO | Qty: {qty:.5f} | Avg Price: ${avg:.2f} | Current Price: ${current_price:.2f} | Purchase Date: {date_str}")
                out.append({
                    'symbol': sym,
                    'qty': qty,
                    'avg_entry_price': avg,
                    'purchase_date': date_str,
                    'instrument_type': instr_type
                })
        if not out:
            print("No CRYPTO positions found.")
            logging.info("No CRYPTO positions found.")
        return out
    except Exception as e:
        logging.error(f"Positions fetch error: {e}")
        print(f"Positions fetch error: {e}")
        return []

def sync_db_with_api():
    if task_running['sync_db_with_api']:
        print("sync_db_with_api already running. Skipping.")
        logging.info("sync_db_with_api already running. Skipping")
        return
    task_running['sync_db_with_api'] = True
    try:
        session = SessionLocal()
        try:
            api_positions = []
            for attempt in range(3):
                try:
                    api_positions = client_list_positions()
                    print(f"API positions retrieved: {api_positions}")
                    logging.info(f"API positions retrieved: {api_positions}")
                    break
                except Exception as e:
                    logging.error(f"Retry {attempt + 1}/3: Error fetching positions from API: {e}")
                    print(f"Retry {attempt + 1}/3: Error fetching positions from API: {e}")
                    time.sleep(2 ** attempt)
                    if attempt == 2:
                        logging.error("All retries failed for syncing DB with API. Using database positions.")
                        print("All retries failed for syncing DB with API. Using database positions.")
                        return
            api_symbols = {pos['symbol'] for pos in api_positions}
            for pos in api_positions:
                symbol = pos['symbol']
                if symbol != 'BTC':
                    continue
                qty = pos['qty']
                avg_price = pos['avg_entry_price']
                purchase_date = pos['purchase_date']
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
            for db_pos in session.query(Position).filter(Position.quantity <= 0).all():
                if db_pos.symbols not in api_symbols:
                    if db_pos.stop_order_id:
                        client_cancel_order({'orderId': db_pos.stop_order_id, 'instrument': {'symbol': db_pos.symbols}})
                    session.delete(db_pos)
            session.commit()
            print("Database synced with API for CRYPTO positions.")
            logging.info("Database synced with API for CRYPTO positions")
        except Exception as e:
            session.rollback()
            logging.error(f"Error syncing DB with API: {e}")
            print(f"Error syncing DB with API: {e}")
        finally:
            session.close()
    finally:
        task_running['sync_db_with_api'] = False

def load_positions_from_database():
    print("Loading CRYPTO positions from database...")
    logging.info("Loading CRYPTO positions from database")
    with db_lock:
        session = SessionLocal()
        try:
            positions = session.query(Position).filter(Position.quantity > 0, Position.symbols == 'BTC').all()
            symbols_to_sell_dict = {}
            for position in positions:
                symbols_to_sell_dict[position.symbols] = (position.avg_price, position.purchase_date)
            print(f"Loaded {len(symbols_to_sell_dict)} CRYPTO positions from database.")
            logging.info(f"Loaded {len(symbols_to_sell_dict)} CRYPTO positions from database")
            return symbols_to_sell_dict
        except Exception as e:
            logging.error(f"Error loading positions from database: {e}")
            print(f"Error loading positions from database: {e}")
            return {}
        finally:
            session.close()

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def calculate_technical_indicators(symbol, lookback_days=200):
    print(f"Calculating technical indicators for {symbol}...")
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
            return None
        historical_data = historical_data.dropna(subset=['open', 'high', 'low', 'close'])
        if len(historical_data) < 35:
            logging.error(f"After cleaning, insufficient data for {symbol} (rows: {len(historical_data)})")
            return None
        short_window = 12
        long_window = 26
        signal_window = 9
        try:
            macd, signal, _ = talib.MACD(historical_data['close'].values, fastperiod=short_window, slowperiod=long_window, signalperiod=signal_window)
            historical_data['macd'] = macd
            historical_data['signal'] = signal
        except Exception as e:
            print(f"Error calculating MACD for {symbol}: {e}")
            historical_data['macd'] = np.nan
            historical_data['signal'] = np.nan
        try:
            rsi = talib.RSI(historical_data['close'].values, timeperiod=14)
            historical_data['rsi'] = rsi
        except Exception as e:
            print(f"Error calculating RSI for {symbol}: {e}")
            historical_data['rsi'] = np.nan
        try:
            upper, middle, lower = talib.BBANDS(historical_data['close'].values, timeperiod=20, nbdevup=2, nbdevdn=2)
            historical_data['upper_bb'] = upper
            historical_data['middle_bb'] = middle
            historical_data['lower_bb'] = lower
        except Exception as e:
            print(f"Error calculating BB for {symbol}: {e}")
            historical_data['upper_bb'] = np.nan
            historical_data['middle_bb'] = np.nan
            historical_data['lower_bb'] = np.nan
        try:
            historical_data['sma_200'] = talib.SMA(historical_data['close'].values, timeperiod=200)
        except Exception as e:
            print(f"Error calculating SMA for {symbol}: {e}")
            historical_data['sma_200'] = np.nan
        try:
            historical_data['typical_price'] = (historical_data['high'] + historical_data['low'] + historical_data['close']) / 3
            historical_data['vwap'] = (historical_data['typical_price'] * historical_data['volume']).cumsum() / historical_data['volume'].cumsum()
        except Exception as e:
            print(f"Error calculating VWAP for {symbol}: {e}")
            historical_data['vwap'] = np.nan
        try:
            historical_data['adx'] = talib.ADX(historical_data['high'].values, historical_data['low'].values, historical_data['close'].values, timeperiod=14)
            historical_data['plus_di'] = talib.PLUS_DI(historical_data['high'].values, historical_data['low'].values, historical_data['close'].values, timeperiod=14)
            historical_data['minus_di'] = talib.MINUS_DI(historical_data['high'].values, historical_data['low'].values, historical_data['close'].values, timeperiod=14)
        except Exception as e:
            print(f"Error calculating ADX for {symbol}: {e}")
            historical_data['adx'] = np.nan
            historical_data['plus_di'] = np.nan
            historical_data['minus_di'] = np.nan
        print(f"Technical indicators calculated for {symbol}.")
        logging.info(f"Technical indicators calculated for {symbol}")
        return historical_data
    except Exception as e:
        logging.error(f"Error fetching OHLCV for {symbol}: {e}")
        return None

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def get_daily_rsi(symbol):
    print(f"Calculating daily RSI for {symbol}...")
    logging.info(f"Calculating daily RSI for {symbol}")
    exchange = ccxt.coinbase()
    symbol_usd = f"{symbol}/USD"
    try:
        data = exchange.fetch_ohlcv(symbol_usd, timeframe='1d', limit=30)
        historical_data = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        if historical_data.empty or len(historical_data['close']) < 14:
            print(f"Insufficient daily data for {symbol} (rows: {len(historical_data)}).")
            return 50.00
        rsi = talib.RSI(historical_data['close'], timeperiod=14)[-1]
        rsi_value = round(rsi, 2) if not np.isnan(rsi) else 50.00
        print(f"Daily RSI for {symbol}: {rsi_value}")
        return rsi_value
    except Exception as e:
        print(f"Error calculating daily RSI for {symbol}: {e}")
        return 50.00

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def get_average_true_range(symbol):
    print(f"Calculating ATR for {symbol}...")
    logging.info(f"Calculating ATR for {symbol}")
    def _fetch_atr(symbol):
        exchange = ccxt.coinbase()
        symbol_usd = f"{symbol}/USD"
        try:
            data = exchange.fetch_ohlcv(symbol_usd, timeframe='1d', limit=30)
            df = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
            atr = talib.ATR(df['high'].values, df['low'].values, df['close'].values, timeperiod=22)
            atr_value = atr[-1]
            print(f"ATR value for {symbol}: {atr_value:.4f}")
            return atr_value
        except Exception as e:
            logging.error(f"Error calculating ATR for {symbol}: {e}")
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
        print(f"14-day avg high for {symbol}: {avg_high:.4f}, avg low: {avg_low:.4f}")
        return avg_high, avg_low
    except Exception as e:
        logging.error(f"Error calculating 14-day avg range for {symbol}: {e}")
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
    rsi = historical_data['rsi'].iloc[-1]
    if not np.isnan(rsi) and rsi < 30:
        points += 10
    daily_rsi = get_daily_rsi(symbol)
    if daily_rsi < 30:
        points += 10
    macd = historical_data['macd']
    signal = historical_data['signal']
    if len(macd) >= 2 and not np.isnan(macd.iloc[-1]) and not np.isnan(signal.iloc[-1]) and not np.isnan(macd.iloc[-2]) and not np.isnan(signal.iloc[-2]):
        if macd.iloc[-1] > signal.iloc[-1] and macd.iloc[-2] < signal.iloc[-2]:
            points += 10
    volume = historical_data['volume']
    if volume.iloc[-1] > volume.mean():
        points += 10
    lower_bb = historical_data['lower_bb'].iloc[-1]
    if not np.isnan(lower_bb) and current_price < lower_bb:
        points += 10
    atr_low = get_atr_low_price(symbol)
    if atr_low is not None and current_price < atr_low:
        points += 10
    vwap = historical_data['vwap'].iloc[-1]
    if not np.isnan(vwap) and current_price > vwap:
        points += 10
    sma_200 = historical_data['sma_200'].iloc[-1]
    if not np.isnan(sma_200) and current_price > sma_200:
        points += 10
    adx = historical_data['adx'].iloc[-1]
    plus_di = historical_data['plus_di'].iloc[-1]
    minus_di = historical_data['minus_di'].iloc[-1]
    if not np.isnan(adx) and adx > 25 and not np.isnan(plus_di) and not np.isnan(minus_di) and plus_di > minus_di:
        points += 10
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
    rsi = historical_data['rsi'].iloc[-1]
    if not np.isnan(rsi) and rsi > 70:
        points += 10
    daily_rsi = get_daily_rsi(symbol)
    if daily_rsi > 70:
        points += 10
    macd = historical_data['macd']
    signal = historical_data['signal']
    if len(macd) >= 2 and not np.isnan(macd.iloc[-1]) and not np.isnan(signal.iloc[-1]) and not np.isnan(macd.iloc[-2]) and not np.isnan(signal.iloc[-2]):
        if macd.iloc[-1] < signal.iloc[-1] and macd.iloc[-2] > signal.iloc[-2]:
            points += 10
    volume = historical_data['volume']
    if volume.iloc[-1] > volume.mean():
        points += 10
    upper_bb = historical_data['upper_bb'].iloc[-1]
    if not np.isnan(upper_bb) and current_price > upper_bb:
        points += 10
    atr_high = get_atr_high_price(symbol)
    if atr_high is not None and current_price > atr_high:
        points += 10
    vwap = historical_data['vwap'].iloc[-1]
    if not np.isnan(vwap) and current_price < vwap:
        points += 10
    sma_200 = historical_data['sma_200'].iloc[-1]
    if not np.isnan(sma_200) and current_price < sma_200:
        points += 10
    adx = historical_data['adx'].iloc[-1]
    plus_di = historical_data['plus_di'].iloc[-1]
    minus_di = historical_data['minus_di'].iloc[-1]
    if not np.isnan(adx) and adx > 25 and not np.isnan(plus_di) and not np.isnan(minus_di) and plus_di < minus_di:
        points += 10
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
        return 10 if detected else 0
    except Exception as e:
        logging.error(f"Error in candlestick detection for {symbol}: {e}")
        return 0

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def get_atr_high_price(symbol):
    print(f"Calculating ATR high price for {symbol}...")
    atr_value = get_average_true_range(symbol)
    current_price = client_get_quote(symbol)
    atr_high = round(current_price + 0.40 * atr_value, 4) if current_price and atr_value else None
    price_color = GREEN if atr_high and atr_high >= 0 else RED
    print(f"ATR high price for {symbol}: {price_color}${atr_high:.4f}{RESET}" if atr_high else f"Failed to calculate ATR high price for {symbol}.")
    return atr_high

@sleep_and_retry
@limits(calls=CALLS, period=PERIOD)
def get_atr_low_price(symbol):
    print(f"Calculating ATR low price for {symbol}...")
    atr_value = get_average_true_range(symbol)
    current_price = client_get_quote(symbol)
    atr_low = round(current_price - 0.10 * atr_value, 4) if current_price and atr_value else None
    price_color = GREEN if atr_low and atr_low >= 0 else RED
    print(f"ATR low price for {symbol}: {price_color}${atr_low:.4f}{RESET}" if atr_low else f"Failed to calculate ATR low price for {symbol}.")
    return atr_low

def get_previous_price(symbol):
    return previous_prices.get(symbol, client_get_quote(symbol) or 0.0)

def update_previous_price(symbol, current_price):
    previous_prices[symbol] = current_price

def track_price_changes(symbol):
    current_price = client_get_quote(symbol)
    previous_price = get_previous_price(symbol)
    price_change = current_price - previous_price if current_price and previous_price else 0
    change_color = GREEN if price_change >= 0 else RED
    current_color = GREEN if current_price >= 0 else RED
    price_changes[symbol] = price_changes.get(symbol, {'increased': 0, 'decreased': 0})
    if current_price > previous_price:
        price_changes[symbol]['increased'] += 1
        print(f"{symbol} price increased | current price: {current_color}${current_price:.2f}{RESET} (change: {change_color}${price_change:.2f}{RESET})")
    elif current_price < previous_price:
        price_changes[symbol]['decreased'] += 1
        print(f"{symbol} price decreased | current price: {current_color}${current_price:.2f}{RESET} (change: {change_color}${price_change:.2f}{RESET})")
    else:
        print(f"{symbol} price unchanged | current price: {current_color}${current_price:.2f}{RESET}")
    update_previous_price(symbol, current_price)

def check_price_moves():
    track_price_changes('BTC')

def update_stop_losses():
    if not ENABLE_AUTOMATIC_STOP_LOSS_ORDERS:
        return
    print("Updating stop-loss orders...")
    logging.info("Updating stop-loss orders")
    session = SessionLocal()
    try:
        positions = session.query(Position).filter(Position.quantity > 0, Position.symbols == 'BTC').all()
        for pos in positions:
            sym = pos.symbols
            current_price = client_get_quote(sym)
            if current_price is None:
                continue
            new_stop_price = current_price * (1 - STOP_LOSS_PERCENTAGE)
            if pos.stop_price and abs(new_stop_price - pos.stop_price) / pos.stop_price < 0.01:
                continue
            if pos.stop_order_id:
                client_cancel_order({'orderId': pos.stop_order_id, 'instrument': {'symbol': sym}})
            stop_order_id = client_place_order(sym, "SELL", quantity=pos.quantity, order_type="STOP", stop_price=new_stop_price)
            if stop_order_id:
                pos.stop_order_id = stop_order_id
                pos.stop_price = new_stop_price
                print(f"Updated stop-loss for {sym}: ${new_stop_price:.2f}")
                logging.info(f"Updated stop-loss for {sym}: ${new_stop_price:.2f}")
        session.commit()
    except Exception as e:
        session.rollback()
        logging.error(f"Error updating stop-loss orders: {e}")
        print(f"Error updating stop-loss orders: {e}")
    finally:
        session.close()

def monitor_stop_losses():
    if not ENABLE_AUTOMATIC_STOP_LOSS_ORDERS:
        return
    print("Monitoring stop-loss orders...")
    logging.info("Monitoring stop-loss orders")
    session = SessionLocal()
    try:
        positions = session.query(Position).filter(Position.stop_order_id.isnot(None), Position.symbols == 'BTC').all()
        for pos in positions:
            sym = pos.symbols
            status_info = client_get_order_status(pos.stop_order_id)
            if status_info and status_info["status"] == "FILLED":
                filled_qty = status_info["filled_qty"]
                filled_price = status_info["avg_price"] or client_get_quote(sym) or pos.avg_price
                trade = TradeHistory(
                    symbols=sym,
                    action='sell',
                    quantity=filled_qty,
                    price=filled_price,
                    date=datetime.now(eastern).strftime("%Y-%m-%d")
                )
                session.add(trade)
                pos.quantity -= filled_qty
                pos.stop_order_id = None
                pos.stop_price = None
                if pos.quantity <= 0:
                    session.delete(pos)
                else:
                    new_stop_price = filled_price * (1 - STOP_LOSS_PERCENTAGE)
                    stop_order_id = client_place_order(sym, "SELL", quantity=pos.quantity, order_type="STOP", stop_price=new_stop_price)
                    if stop_order_id:
                        pos.stop_order_id = stop_order_id
                        pos.stop_price = new_stop_price
                session.commit()
                with open(csv_filename, mode='a', newline='') as csv_file:
                    csv_writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
                    csv_writer.writerow({
                        'Date': datetime.now(eastern).strftime("%Y-%m-%d"),
                        'Buy': ' ',
                        'Sell': 'Sell',
                        'Quantity': filled_qty,
                        'Symbol': sym,
                        'Price Per Share': filled_price
                    })
                send_alert(
                    f"Stop-loss triggered: Sold {filled_qty:.5f} of {sym} at ${filled_price:.2f}",
                    subject=f"Stop-Loss Executed: {sym}"
                )
    except Exception as e:
        session.rollback()
        logging.error(f"Error monitoring stop-loss orders: {e}")
        print(f"Error monitoring stop-loss orders: {e}")
    finally:
        session.close()

def print_database_tables():
    if not PRINT_DATABASE:
        return
    session = SessionLocal()
    try:
        print("\nTrade History:")
        print("Crypto | Action | Qty | Price | Date")
        for record in session.query(TradeHistory).filter(TradeHistory.symbols == 'BTC').all():
            print(f"{record.symbols:<6} | {record.action:<6} | {record.quantity:.5f} | ${record.price:.2f} | {record.date}")
    except Exception as e:
        logging.error(f"Error printing database: {e}")
        print(f"Error printing database: {e}")
    finally:
        session.close()

def list_crypto_positions():
    if not PRINT_DATABASE:
        return
    print("\nCRYPTO Positions:")
    logging.info("Listing owned CRYPTO positions")
    try:
        session = SessionLocal()
        crypto_positions = session.query(Position).filter(Position.quantity > 0, Position.symbols == 'BTC').all()
        if not crypto_positions:
            print("None")
            logging.info("No CRYPTO positions currently owned in database.")
            return
        print("Symbol | Qty      | Avg Price | Date       | Curr Price | % Change | Stop Price")
        print("-" * 70)
        for pos in crypto_positions:
            current_price = client_get_quote(pos.symbols)
            percentage_change = ((current_price - pos.avg_price) / pos.avg_price * 100) if current_price and pos.avg_price else 0
            color = GREEN if percentage_change >= 0 else RED
            price_color = GREEN if current_price >= 0 else RED
            stop_price_display = f"${pos.stop_price:.2f}" if pos.stop_price else "N/A"
            print(f"{pos.symbols:<6} | {pos.quantity:>7.5f} | ${pos.avg_price:>8.2f} | {pos.purchase_date:<10} | {price_color}${current_price:>9.2f}{RESET} | {color}{percentage_change:>7.2f}%{RESET} | {stop_price_display}")
            logging.info(f"CRYPTO Position: {pos.symbols} | Qty: {pos.quantity:.5f} | Avg Price: ${pos.avg_price:.2f} | Date: {pos.purchase_date} | Current Price: ${current_price:.2f} | Change: {percentage_change:.2f}% | Stop Price: {stop_price_display}")
        print("-" * 70)
    except Exception as e:
        logging.error(f"Error listing CRYPTO positions: {e}")
        print(f"Error listing CRYPTO positions: {e}")
    finally:
        session.close()

def get_symbols_to_buy():
    print("Setting BTC as the only symbol to analyze...")
    logging.info("Setting BTC as the only symbol to analyze")
    return ['BTC']

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
        acc = client_get_account()
        total_equity = acc['equity']
        buying_power = float(acc['buying_power_cash'])
        print(f"Total account equity: ${total_equity:.2f}, Buying power: ${buying_power:.2f}")
        logging.info(f"Total account equity: ${total_equity:.2f}, Buying power: ${buying_power:.2f}")
        if buying_power <= 10.00:
            print("Buying power <= $10.00. Skipping all buys to maintain minimum balance.")
            logging.info("Buying power <= $10.00. Skipping all buys to maintain minimum balance.")
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
            print(f"No valid price data for {sym}. Skipping.")
            logging.info(f"No valid price data for {sym}. Skipping")
            return
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
            if buying_power <= 10.00:
                print(f"Buying power <= $10.00. Stopping buy orders.")
                logging.info(f"Buying power <= $10.00. Stopping buy orders.")
                return
            dollar_amount = allocation_per_risk.get(risk_levels.get(sym, "ultra-low"), 10.0)
            if ALL_BUY_ORDERS_ARE_5_DOLLARS:
                dollar_amount = 5.00
            dollar_amount = min(dollar_amount, buying_power - 10.00)
            if dollar_amount < 1.00:
                print(f"Insufficient buying power for {sym} after reserving $10. Stopping.")
                logging.info(f"Insufficient buying power for {sym} after reserving $10. Stopping.")
                return
            qty = dollar_amount / current_price if current_price else 0
            qty = round(qty, 5)
            if qty <= 0:
                print(f"Invalid quantity for {sym}. Skipping.")
                logging.info(f"Invalid quantity for {sym}. Skipping.")
                return
            print(f"Attempting to buy ${dollar_amount:.2f} ({qty:.5f} of {sym})...")
            logging.info(f"Attempting to buy ${dollar_amount:.2f} ({qty:.5f} of {sym})")
            order_id = client_place_order(sym, "BUY", amount=dollar_amount)
            if order_id:
                print(f"Buy order placed for ${dollar_amount:.2f} of {sym}, Order ID: {order_id}")
                logging.info(f"Buy order placed for ${dollar_amount:.2f} of {sym}, Order ID: {order_id}")
                status_info = poll_order_status(order_id)
                if status_info and status_info["status"] == "FILLED":
                    filled_qty = status_info["filled_qty"]
                    filled_price = status_info["avg_price"] or current_price
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
                        total_qty = position.quantity + filled_qty
                        total_cost = (position.quantity * position.avg_price) + (filled_qty * filled_price)
                        position.avg_price = total_cost / total_qty if total_qty else filled_price
                        position.quantity = total_qty
                        if ENABLE_AUTOMATIC_STOP_LOSS_ORDERS:
                            stop_price = filled_price * (1 - STOP_LOSS_PERCENTAGE)
                            if position.stop_order_id:
                                client_cancel_order({'orderId': position.stop_order_id, 'instrument': {'symbol': sym}})
                            stop_order_id = client_place_order(sym, "SELL", quantity=total_qty, order_type="STOP", stop_price=stop_price)
                            if stop_order_id:
                                position.stop_order_id = stop_order_id
                                position.stop_price = stop_price
                    else:
                        stop_price = filled_price * (1 - STOP_LOSS_PERCENTAGE) if ENABLE_AUTOMATIC_STOP_LOSS_ORDERS else None
                        stop_order_id = client_place_order(sym, "SELL", quantity=filled_qty, order_type="STOP", stop_price=stop_price) if ENABLE_AUTOMATIC_STOP_LOSS_ORDERS else None
                        position = Position(
                            symbols=sym,
                            quantity=filled_qty,
                            avg_price=filled_price,
                            purchase_date=today_date_str,
                            stop_order_id=stop_order_id,
                            stop_price=stop_price if stop_order_id else None
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
                        f"Bought {filled_qty:.5f} of {sym} at ${filled_price:.2f}",
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
        session = SessionLocal()
        try:
            symbols_to_sell_dict = load_positions_from_database()
            if not symbols_to_sell_dict:
                print("No CRYPTO positions to sell.")
                logging.info("No CRYPTO positions to sell")
                return
            for sym in symbols_to_sell_dict:
                points = calculate_sell_points(sym)
                if points < POINT_THRESHOLD:
                    print(f"{sym}: No sell signal (Points: {points})")
                    logging.info(f"{sym}: No sell signal (Points: {points})")
                    continue
                print(f"{sym}: Sell signal detected (Points: {points})")
                logging.info(f"{sym}: Sell signal detected (Points: {points})")
                current_price = rate_limited_get_quote(sym)
                if current_price is None:
                    print(f"No valid price data for {sym}. Skipping sell.")
                    logging.info(f"No valid price data for {sym}. Skipping sell")
                    continue
                position = session.query(Position).filter_by(symbols=sym).first()
                if not position or position.quantity <= 0:
                    print(f"No valid position for {sym} in database. Skipping.")
                    logging.info(f"No valid position for {sym} in database. Skipping")
                    continue
                qty = position.quantity
                today_date = datetime.today().date()
                today_date_str = today_date.strftime("%Y-%m-%d")
                current_datetime = datetime.now(eastern)
                current_time_str = current_datetime.strftime("Eastern Time | %I:%M:%S %p | %m-%d-%Y |")
                print(f"\n{'='*60}")
                print(f"Processing sell for {sym}...")
                print(f"{'='*60}")
                print(f"Analysis time: {current_time_str}")
                logging.info(f"Analysis time: {current_time_str}")
                if not ensure_no_open_orders(sym):
                    print(f"Cannot sell {sym}: Open orders still exist after cancellation attempt.")
                    logging.info(f"Cannot sell {sym}: Open orders still exist after cancellation attempt.")
                    continue
                print(f"Attempting to sell {qty:.5f} of {sym} at market price ${current_price:.2f}...")
                logging.info(f"Attempting to sell {qty:.5f} of {sym} at market price ${current_price:.2f}")
                if position.stop_order_id and ENABLE_AUTOMATIC_STOP_LOSS_ORDERS:
                    client_cancel_order({'orderId': position.stop_order_id, 'instrument': {'symbol': sym}})
                    print(f"Cancelled stop-loss order {position.stop_order_id} for {sym} before selling")
                    logging.info(f"Cancelled stop-loss order {position.stop_order_id} for {sym} before selling")
                    position.stop_order_id = None
                    position.stop_price = None
                    session.commit()
                order_id = client_place_order(sym, "SELL", quantity=qty)
                if order_id:
                    print(f"Sell order placed for {qty:.5f} of {sym}, Order ID: {order_id}")
                    logging.info(f"Sell order placed for {qty:.5f} of {sym}, Order ID: {order_id}")
                    status_info = poll_order_status(order_id)
                    if status_info and status_info["status"] == "FILLED":
                        filled_qty = status_info["filled_qty"]
                        filled_price = status_info["avg_price"] or current_price
                        trade = TradeHistory(
                            symbols=sym,
                            action='sell',
                            quantity=filled_qty,
                            price=filled_price,
                            date=today_date_str
                        )
                        session.add(trade)
                        position.quantity -= filled_qty
                        if position.quantity <= 0:
                            session.delete(position)
                        else:
                            if ENABLE_AUTOMATIC_STOP_LOSS_ORDERS:
                                stop_price = filled_price * (1 - STOP_LOSS_PERCENTAGE)
                                stop_order_id = client_place_order(sym, "SELL", quantity=position.quantity, order_type="STOP", stop_price=stop_price)
                                if stop_order_id:
                                    position.stop_order_id = stop_order_id
                                    position.stop_price = stop_price
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
                        send_alert(
                            f"Sold {filled_qty:.5f} of {sym} at ${filled_price:.2f}",
                            subject=f"Trade Executed: Sold {sym}"
                        )
                        acc = client_get_account()
                        buying_power = float(acc['buying_power_cash'])
                        print(f"Updated buying power after selling {sym}: ${buying_power:.2f}")
                        logging.info(f"Updated buying power after selling {sym}: ${buying_power:.2f}")
                    else:
                        print(f"Sell order for {sym} not filled or failed (Status: {status_info['status'] if status_info else 'Unknown'}).")
                        logging.info(f"Sell order for {sym} not filled or failed (Status: {status_info['status'] if status_info else 'Unknown'}).")
                else:
                    print(f"Failed to place sell order for {sym}.")
                    logging.info(f"Failed to place sell order for {sym}.")
        except Exception as e:
            session.rollback()
            logging.error(f"Error in sell_cryptos: {e}")
            print(f"Error in sell_cryptos: {e}")
        finally:
            session.close()
    finally:
        task_running['sell_cryptos'] = False

def main():
    initialize_csv()
    cleanup_invalid_positions()
    if not fetch_token_and_account():
        print("Failed to initialize token and account. Exiting.")
        logging.error("Failed to initialize token and account. Exiting.")
        return
    symbols_to_sell_dict = load_positions_from_database()
    try:
        while True:
            if not refresh_token_if_needed():
                print("Token refresh failed. Exiting.")
                logging.error("Token refresh failed. Exiting.")
                break
            print(f"\n{'='*60}")
            print(f"Starting new cycle at {datetime.now(eastern).strftime('%Y-%m-%d %H:%M:%S')}")
            print(f"{'='*60}")
            logging.info(f"Starting new cycle at {datetime.now(eastern).strftime('%Y-%m-%d %H:%M:%S')}")
            list_crypto_positions()
            print_database_tables()
            check_price_moves()
            buy_cryptos(symbols_to_sell_dict)
            sell_cryptos()
            if ENABLE_AUTOMATIC_STOP_LOSS_ORDERS:
                monitor_stop_losses()
                update_stop_losses()
            sync_db_with_api()
            time.sleep(300)
    except KeyboardInterrupt:
        print("\nTrading bot stopped by user.")
        logging.info("Trading bot stopped by user.")
    except Exception as e:
        logging.error(f"Unexpected error in main loop: {e}")
        print(f"Unexpected error in main loop: {e}")
        traceback.print_exc()

if __name__ == "__main__":
    main()
