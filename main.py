import asyncio
import aiohttp
import json
import os
import re
import base64
import shutil
import ipaddress
import socket
import sys
import logging
from typing import List, Dict, Optional, Set, Tuple, Any
from urllib.parse import urlparse, parse_qs, urlencode, unquote, quote
from datetime import datetime, timezone
from collections import defaultdict
import geoip2.database

# --- Configuration & Logging ---
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
PATHS = {
    'INPUT': os.path.join(BASE_DIR, 'channelsData', 'channelsAssets.json'),
    'TEMP': os.path.join(BASE_DIR, 'temp_build'),
    'FINAL_ASSETS': os.path.join(BASE_DIR, 'channelsData'),
    'GEOIP': os.path.join(BASE_DIR, 'Country.mmdb'),
    'API': os.path.join(BASE_DIR, 'api'),
    'OUTPUT_SUBS': os.path.join(BASE_DIR, 'subscriptions'),
    'OUTPUT_LITE': os.path.join(BASE_DIR, 'lite', 'subscriptions'),
    'CONFIG_TXT': os.path.join(BASE_DIR, 'config.txt')
}

URLS = {
    'GEOIP': "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb",
    'PRIVATE': 'https://raw.githubusercontent.com/itsyebekhe/PSGP/main/private_configs.json',
    'GITHUB_LOGO': 'https://raw.githubusercontent.com/itsyebekhe/PSG/main/channelsData/logos'
}

CONSTANTS = {
    'LITE_LIMIT': 3,
    'TIMEOUT': 15,
    'DNS_WORKERS': 50,
    'TCP_WORKERS': 100,  # New: Concurrent TCP check limit
    'TCP_TIMEOUT': 3, 
    'FAKE_NAMES': ['#همکاری_ملی', '#جاویدشاه', '#KingRezaPahlavi'],
    'CLOUDFLARE_CIDRS': [
        "173.245.48.0/20", "103.21.244.0/22", "103.22.200.0/22", "103.31.4.0/22",
        "141.101.64.0/18", "108.162.192.0/18", "190.93.240.0/20", "188.114.96.0/20",
        "197.234.240.0/22", "198.41.128.0/17", "162.158.0.0/15", "104.16.0.0/13",
        "104.24.0.0/14", "172.64.0.0/13", "131.0.72.0/22", "2400:cb00::/32",
        "2606:4700::/32", "2803:f800::/32", "2405:b500::/32", "2405:8100::/32",
        "2a06:98c0::/29", "2c0f:f248::/32"
    ]
}

# Pre-compile Regex and Networks
PROTOCOL_REGEX = re.compile(r'(?:vmess|vless|trojan|ss|tuic|hy2|hysteria2?):\/\/[^\s"\']+(?=\s|<|>|$)', re.IGNORECASE)
CLOUDFLARE_NETWORKS = [ipaddress.ip_network(cidr) for cidr in CONSTANTS['CLOUDFLARE_CIDRS']]

# --- Fixed ConfigUtils & ConfigParser ---

class ConfigUtils:
    @staticmethod
    def decode_base64(s: str) -> str:
        """Robust Base64 decoder."""
        if not s: return ""
        s = s.strip().replace(' ', '+')
        s = s.replace('-', '+').replace('_', '/')
        padding = len(s) % 4
        if padding:
            s += '=' * (4 - padding)
        try:
            return base64.b64decode(s).decode('utf-8', errors='ignore')
        except Exception:
            return ""

    @staticmethod
    def detect_type(config: str) -> Optional[str]:
        # FIX: Case insensitive check
        lower = config[:20].lower()
        if lower.startswith('vmess://'): return 'vmess'
        if lower.startswith('vless://'): return 'vless'
        if lower.startswith('trojan://'): return 'trojan'
        if lower.startswith('ss://'): return 'ss'
        if lower.startswith('tuic://'): return 'tuic'
        if lower.startswith(('hy2://', 'hysteria2://')): return 'hy2'
        if lower.startswith('hysteria://'): return 'hysteria'
        return None

    @staticmethod
    def is_ipv6(host: str) -> bool:
        host = host.strip('[]')
        try:
            return isinstance(ipaddress.ip_address(host), ipaddress.IPv6Address)
        except ValueError:
            return False

    @staticmethod
    def get_address_type(host: str) -> str:
        host = host.strip('[]')
        try:
            ip = ipaddress.ip_address(host)
            return 'ipv6' if isinstance(ip, ipaddress.IPv6Address) else 'ipv4'
        except ValueError:
            return 'domain'

    @staticmethod
    def is_cloudflare(ip_str: str) -> bool:
        if not ip_str: return False
        try:
            clean_ip = ip_str.strip('[]')
            ip_obj = ipaddress.ip_address(clean_ip)
            return any(ip_obj in net for net in CLOUDFLARE_NETWORKS)
        except ValueError:
            return False

    @staticmethod
    def is_reality(config: str) -> bool:
        return 'security=reality' in config and config.lower().startswith('vless://')

    @staticmethod
    def is_xhttp(config: str) -> bool:
        return 'type=xhttp' in config

    @staticmethod
    def create_fake_config(name: str) -> str:
        encoded_name = quote(name.lstrip('#'))
        return f"vless://00000000-0000-0000-0000-000000000000@127.0.0.1:443?security=none&type=ws&path=/#{encoded_name}"
    
    @staticmethod
    def generate_header(title: str) -> str:
        b64_title = base64.b64encode(title.encode()).decode()
        return (
            f"#profile-title: base64:{b64_title}\n"
            "#profile-update-interval: 1\n"
            "#subscription-userinfo: upload=0; download=0; total=10737418240000000; expire=2546249531\n"
            "#support-url: https://t.me/yebekhe\n"
            "#profile-web-page-url: https://github.com/itsyebekhe/PSG\n\n"
        )


class ConfigParser:
    @staticmethod
    def parse(config_str: str) -> Optional[Dict[str, Any]]:
        ctype = ConfigUtils.detect_type(config_str)
        if not ctype: return None
        
        try:
            if ctype == 'vmess':
                return ConfigParser._parse_vmess(config_str)
            elif ctype == 'ss':
                return ConfigParser._parse_ss(config_str)
            else:
                return ConfigParser._parse_generic(config_str, ctype)
        except Exception:
            return None

    @staticmethod
    def _parse_vmess(config_str: str) -> Optional[Dict]:
        try:
            # FIX: Handle "VMESS://" vs "vmess://" string slicing
            prefix_len = 8 # vmess://
            b64 = config_str[prefix_len:]
            json_str = ConfigUtils.decode_base64(b64)
            if not json_str: return None
            
            data = json.loads(json_str)
            
            return {
                'type': 'vmess',
                'ps': data.get('ps', ''),
                'add': data.get('add', ''),
                'port': str(data.get('port', '')),
                'id': data.get('id', ''),
                'net': data.get('net', 'tcp'),
                'type_transport': data.get('type', 'none'),
                'host': data.get('host', ''),
                'path': data.get('path', ''),
                'tls': data.get('tls', ''),
                'sni': data.get('sni', ''),
                'full_data': data
            }
        except json.JSONDecodeError:
            return None

    @staticmethod
    def _parse_ss(config_str: str) -> Optional[Dict]:
        parsed = urlparse(config_str)
        user_info = parsed.netloc
        host_port = ""
        
        # Handle ss://BASE64@host:port
        if '@' in user_info:
            user_pass_b64, host_port = user_info.rsplit('@', 1)
            try:
                decoded = ConfigUtils.decode_base64(user_pass_b64)
                if ':' in decoded:
                    method, password = decoded.split(':', 1)
                else:
                    method = "auto"
                    password = decoded
            except:
                # Fallback: maybe it wasn't base64?
                if ':' in user_pass_b64:
                    method, password = user_pass_b64.split(':', 1)
                else:
                    return None
        else:
            # Handle ss://BASE64_FULL_LINK
            decoded_full = ConfigUtils.decode_base64(user_info)
            if '@' in decoded_full:
                method_pass, host_port = decoded_full.rsplit('@', 1)
                if ':' in method_pass:
                    method, password = method_pass.split(':', 1)
                else:
                    return None
            else:
                return None

        # Parse Host and Port
        host = ""
        port = ""
        if ']:' in host_port:
            host_part, port_part = host_port.rsplit(':', 1)
            host = host_part.strip('[]')
            port = port_part
        elif ':' in host_port:
            host, port = host_port.rsplit(':', 1)
        else:
            host = host_port

        return {
            'type': 'ss',
            'name': unquote(parsed.fragment),
            'host': host,
            'port': port,
            'method': method,
            'password': password
        }

    @staticmethod
    def _parse_generic(config_str: str, ctype: str) -> Dict:
        parsed = urlparse(config_str)
        params = parse_qs(parsed.query)
        clean_params = {k: v[0] for k, v in params.items() if v}

        return {
            'type': ctype,
            'hash': unquote(parsed.fragment),
            'user': unquote(parsed.username) if parsed.username else '',
            'password': unquote(parsed.password) if parsed.password else '',
            'host': parsed.hostname if parsed.hostname else '',
            'port': str(parsed.port) if parsed.port else '',
            'params': clean_params,
            'path': parsed.path
        }

    @staticmethod
    def reassemble(parsed: Dict, new_tag: str = None) -> Optional[str]:
        if not parsed: return None
        ctype = parsed.get('type')

        if ctype == 'vmess':
            data = parsed.get('full_data', {}).copy()
            if new_tag: data['ps'] = new_tag
            if not data.get('add'): data['add'] = '127.0.0.1'
            if not data.get('port'): data['port'] = 443
            if not data.get('id'): data['id'] = 'uuid'
            json_str = json.dumps(data, separators=(',', ':'), ensure_ascii=False)
            return 'vmess://' + base64.b64encode(json_str.encode()).decode()

        elif ctype == 'ss':
            method = parsed.get('method', 'chacha20-ietf-poly1305')
            password = parsed.get('password', '')
            user_pass = f"{method}:{password}"
            b64_user = base64.b64encode(user_pass.encode()).decode()
            
            host = parsed.get('host', '')
            if ConfigUtils.is_ipv6(host): host = f"[{host}]"
            
            uri = f"ss://{b64_user}@{host}:{parsed.get('port', '')}"
            name = new_tag if new_tag else parsed.get('name', '')
            return f"{uri}#{quote(name)}"

        else:
            user = parsed.get('user', '')
            password = parsed.get('password', '') 
            userinfo = quote(user)
            if password: userinfo += f":{quote(password)}"
            
            host = parsed.get('host', '')
            if ConfigUtils.is_ipv6(host): host = f"[{host}]"
            
            netloc = f"{userinfo}@{host}:{parsed.get('port', '')}"
            query_params = parsed.get('params', {}).copy()
            path = parsed.get('path', '')
            
            full_path_str = ""
            if ctype in ['vless', 'trojan']:
                 full_path_str = path
                 if query_params: full_path_str += "?" + urlencode(query_params, doseq=True, safe='/')
            else:
                 if path and path != '/': query_params['path'] = path
                 if query_params: full_path_str = "?" + urlencode(query_params, doseq=True, safe='/')

            name = new_tag if new_tag else parsed.get('hash', '')
            return f"{ctype}://{netloc}{full_path_str}#{quote(name)}"

    @staticmethod
    def get_fingerprint(parsed: Dict) -> str:
        ctype = parsed['type']
        def norm(s): return str(s).strip().lower()

        components = [ctype]
        if ctype == 'vmess':
            keys = ['add', 'port', 'id', 'net', 'path', 'host', 'sni']
            components.extend(norm(parsed.get(k, '')) for k in keys)
        elif ctype == 'ss':
            keys = ['host', 'port', 'method', 'password']
            components.extend(norm(parsed.get(k, '')) for k in keys)
        else:
            params = parsed.get('params', {})
            # We must ignore the 'name' or 'fp' if we want real duplicates
            param_str = "&".join(f"{k}={v}" for k, v in sorted(params.items()) if k not in ['remarks', 'name'])
            components.extend([
                norm(parsed.get('user', '')),
                norm(parsed.get('host', '')),
                norm(parsed.get('port', '')),
                norm(parsed.get('path', '')),
                norm(param_str)
            ])
        return "|".join(components)

# --- Main Processor ---

class SubscriptionProcessor:
    def __init__(self):
        self.session = None
        self.dns_cache = {}
        self.geo_reader = None
        self.channel_assets = {}
        self.all_configs = []
        # Semaphore to prevent "Too many open files" during DNS resolution
        self.dns_semaphore = asyncio.Semaphore(CONSTANTS['DNS_WORKERS'])
        self.tcp_semaphore = asyncio.Semaphore(CONSTANTS['TCP_WORKERS'])

    async def initialize(self):
        self.session = aiohttp.ClientSession()
        
        # --- FIX: CLEANUP OLD ARTIFACTS ---
        # We must remove the old output directories because the structure might have changed
        # (e.g., 'normal' changing from a file to a folder).
        dirs_to_clean = [
            PATHS['TEMP'], 
            PATHS['OUTPUT_SUBS'], 
            PATHS['OUTPUT_LITE']
        ]
        
        logger.info("Cleaning up old directories...")
        for d in dirs_to_clean:
            if os.path.exists(d):
                try:
                    shutil.rmtree(d)
                except Exception as e:
                    logger.warning(f"Could not remove {d}: {e}")

        # Ensure directories exist
        for path in [PATHS['TEMP'], PATHS['FINAL_ASSETS'], PATHS['API'], 
                     os.path.join(PATHS['TEMP'], 'logos'), 
                     os.path.join(PATHS['TEMP'], 'html_cache')]:
            os.makedirs(path, exist_ok=True)
        
        # Prepare GEOIP
        await self._setup_geoip()

    async def cleanup(self):
        if self.session: 
            await self.session.close()
            self.session = None
        if self.geo_reader: 
            self.geo_reader.close()

    async def _fetch_url(self, url: str) -> Optional[bytes]:
        if not self.session: return None
        try:
            async with self.session.get(url, timeout=CONSTANTS['TIMEOUT']) as response:
                if response.status == 200:
                    return await response.read()
        except Exception:
            pass
        return None

    async def _setup_geoip(self):
        db_path = PATHS['GEOIP']
        if not os.path.exists(db_path) or (datetime.now().timestamp() - os.path.getmtime(db_path) > 86400):
            logger.info("Downloading GeoIP Database...")
            data = await self._fetch_url(URLS['GEOIP'])
            if data:
                with open(db_path, 'wb') as f: f.write(data)
        
        try:
            self.geo_reader = geoip2.database.Reader(db_path)
        except Exception:
            logger.warning("Could not load GeoIP database.")

    async def check_reachability(self, parsed: Dict) -> bool:
        """
        Tests if the config host:port is reachable via TCP.
        Handles SNI fallback if host is missing.
        """
        # 1. Determine Target Host
        host = parsed.get('host') or parsed.get('add', '')
        port = int(parsed.get('port', 0))

        # 2. "Do something for SNI/WS" 
        # If the 'host' (address) is missing or looks like a placeholder, 
        # but 'sni' is provided, try connecting to the SNI address.
        sni = parsed.get('sni') or parsed.get('params', {}).get('sni') or parsed.get('params', {}).get('host')
        
        if (not host or host == '127.0.0.1') and sni:
            host = sni

        # If we still don't have a valid host or port, fail.
        if not host or not port:
            return False

        # 3. Clean IPv6 brackets for socket connection
        target_host = host.strip('[]')

        async with self.tcp_semaphore:
            try:
                # Attempt TCP Handshake
                future = asyncio.open_connection(target_host, port)
                reader, writer = await asyncio.wait_for(future, timeout=CONSTANTS['TCP_TIMEOUT'])
                
                # If we get here, connection works
                writer.close()
                await writer.wait_closed()
                return True
            except (OSError, asyncio.TimeoutError):
                return False
            except Exception:
                return False

    async def resolve_ip(self, host: str) -> Optional[str]:
        if not host: return None
        if host in self.dns_cache: return self.dns_cache[host]
        
        async with self.dns_semaphore:
            try:
                loop = asyncio.get_running_loop()
                ip = await loop.run_in_executor(None, socket.gethostbyname, host)
                self.dns_cache[host] = ip
                return ip
            except Exception:
                self.dns_cache[host] = None
                return None

    def get_geo_code(self, ip: str) -> str:
        if not self.geo_reader or not ip: return "XX"
        try:
            return self.geo_reader.country(ip).country.iso_code or "XX"
        except: return "XX"

    @staticmethod
    def get_flag(code: str) -> str:
        if not code or len(code) != 2: return "🏳️"
        return chr(127397 + ord(code[0])) + chr(127397 + ord(code[1]))

    async def process_sources(self):
        try:
            with open(PATHS['INPUT'], 'r', encoding='utf-8') as f:
                sources = json.load(f)
        except FileNotFoundError:
            logger.error("Input file not found.")
            return

        tasks = []
        for key, data in sources.items():
            tasks.append(self._process_single_source(key, data))
        
        results = await asyncio.gather(*tasks)
        
        logos_to_fetch = {}
        for key, configs, logo_url in results:
            if logo_url: logos_to_fetch[key] = logo_url
            for c in configs: self.all_configs.append((c, key))
            
        logo_tasks = [self._fetch_and_save_logo(k, u) for k, u in logos_to_fetch.items()]
        if logo_tasks: await asyncio.gather(*logo_tasks)

        await self._fetch_private_configs()

    async def _process_single_source(self, key: str, data: Dict) -> Tuple[str, List[str], Optional[str]]:
        url = data.get('subscription_url') or f"https://t.me/s/{key}"
        content = await self._fetch_url(url)
        configs = []
        logo = None
        types = set()
        title = data.get('title', key)

        if content:
            text = content.decode('utf-8', errors='ignore')
            if data.get('subscription_url'):
                try:
                    decoded = ConfigUtils.safe_base64_decode(text)
                    if 'vmess://' in decoded or 'vless://' in decoded:
                        text = decoded
                except: pass
            
            configs = PROTOCOL_REGEX.findall(text)
            for c in configs: 
                ct = ConfigUtils.detect_type(c)
                if ct: types.add(ct)
            
            t_match = re.search(r'<meta property="twitter:title" content="(.*?)">', text)
            i_match = re.search(r'<meta property="twitter:image" content="(.*?)">', text)
            if t_match: title = t_match.group(1)
            if i_match: logo = i_match.group(1)

        self.channel_assets[key] = {
            'title': title,
            'logo': URLS['GITHUB_LOGO'] + f"/{key}.jpg" if logo else data.get('logo', ''),
            'types': sorted(list(types))
        }
        return key, configs, logo

    async def _fetch_and_save_logo(self, key, url):
        data = await self._fetch_url(url)
        if data:
            try:
                with open(os.path.join(PATHS['TEMP'], 'logos', f"{key}.jpg"), 'wb') as f:
                    f.write(data)
            except: pass

    async def _fetch_private_configs(self):
        data = await self._fetch_url(URLS['PRIVATE'])
        if not data: return
        try:
            p_confs = json.loads(data)
            for c_name, confs in p_confs.items():
                c_name = c_name.strip()
                if not c_name: continue
                p_types = set()
                for c in confs:
                    ct = ConfigUtils.detect_type(c)
                    if ct: 
                        p_types.add(ct)
                        self.all_configs.append((c, c_name))
                if c_name in self.channel_assets:
                    curr_types = set(self.channel_assets[c_name]['types'])
                    self.channel_assets[c_name]['types'] = sorted(list(curr_types | p_types))
                else:
                    self.channel_assets[c_name] = {'title': c_name, 'logo': '', 'types': sorted(list(p_types))}
        except Exception as e:
            logger.error(f"Error parsing private configs: {e}")

    def deduplicate_configs(self) -> Dict[str, Tuple[str, Dict, str]]:
        unique_map = {}
        for conf_str, chan in self.all_configs:
            parsed = ConfigParser.parse(conf_str)
            if not parsed: continue
            
            fp = ConfigParser.get_fingerprint(parsed)
            orig_name = parsed.get('ps') or parsed.get('name') or parsed.get('hash', '')
            
            if fp not in unique_map:
                unique_map[fp] = (orig_name, parsed, chan)
        return unique_map

    async def enrich_and_tag(self, unique_map: Dict):
        final_list = []
        lite_list = []
        api_data = []
        groups = {'channels': defaultdict(list), 'locations': defaultdict(list)}
        channel_counts = defaultdict(int)
        
        total = len(unique_map)
        logger.info(f"Processing {total} configs (Checking TCP + GeoIP)...")

        # We will process tasks in batches to keep the progress bar accurate
        # and prevent queuing 10,000 tasks instantly.
        
        for i, (fp, (orig, parsed, chan)) in enumerate(unique_map.items()):
            if i % 100 == 0: sys.stdout.write(f"\rProcessing... {int(i/total*100)}%")
            
            # --- NEW STEP: Check TCP Connectivity ---
            is_reachable = await self.check_reachability(parsed)
            if not is_reachable:
                # Skip dead configs
                continue
            # ----------------------------------------

            clean_chan = chan.strip().lstrip('@')
            host = parsed.get('host') or parsed.get('add', '')
            
            # Resolve DNS for GeoIP
            ip = await self.resolve_ip(host)
            
            # ... (Rest of the logic remains exactly the same) ...
            country_code = self.get_geo_code(ip)
            is_cf = ConfigUtils.is_cloudflare(ip)
            flag = self.get_flag(country_code)
            
            ctype_disp = parsed.get('type', 'UNK').upper()
            
            new_tag = f"{flag} {country_code} | {ctype_disp} | @{clean_chan}"
            final_str = ConfigParser.reassemble(parsed, new_tag)
            
            if not final_str: continue
            
            final_list.append(final_str)
            
            groups['channels'][clean_chan].append(final_str)
            groups['locations'][country_code].append(final_str)
            if is_cf:
                groups['locations']['CF'].append(final_str)
            
            if channel_counts[clean_chan] < CONSTANTS['LITE_LIMIT']:
                lite_list.append(final_str)
                channel_counts[clean_chan] += 1
                
            eff_type = parsed['type']
            if eff_type == 'vless' and 'security=reality' in final_str: eff_type = 'reality'
            assets = self.channel_assets.get(clean_chan, {})
            
            api_data.append({
                'channel': {'username': clean_chan, 'title': assets.get('title', ''), 'logo': assets.get('logo', '')},
                'country': country_code, 'flag': flag, 'type': eff_type, 'config': final_str, 'is_cf': is_cf
            })
            
        print("\nProcessing complete.")
        return final_list, lite_list, groups, api_data

    def write_output(self, final_list, lite_list, groups, api_data):
        sorted_assets = dict(sorted(self.channel_assets.items()))
        with open(os.path.join(PATHS['TEMP'], 'channelsAssets.json'), 'w', encoding='utf-8') as f:
            json.dump(sorted_assets, f, indent=4, ensure_ascii=False)
        
        if os.path.exists(PATHS['FINAL_ASSETS']): shutil.rmtree(PATHS['FINAL_ASSETS'])
        shutil.copytree(PATHS['TEMP'], PATHS['FINAL_ASSETS'])

        def write_subscription_package(configs: List[str], base_dir: str, title_prefix: str):
            groups = defaultdict(lambda: defaultdict(list))
            fake_configs = [ConfigUtils.create_fake_config(n) for n in CONSTANTS['FAKE_NAMES']]
            
            for c in configs:
                ct = ConfigUtils.detect_type(c)
                if not ct: continue
                parsed = ConfigParser.parse(c)
                if not parsed: continue
                host = parsed.get('host') or parsed.get('add', '')
                addr_type = ConfigUtils.get_address_type(host)
                groups[ct][addr_type].append(c)
                if ct == 'vless' and ConfigUtils.is_reality(c):
                    groups['reality'][addr_type].append(c)
                if ConfigUtils.is_xhttp(c):
                    groups['xhttp'][addr_type].append(c)

            self._write_files(base_dir, 'mix', configs, f"{title_prefix} | MIX", fake_configs)

            for proto, addr_groups in groups.items():
                all_proto_configs = []
                for at, confs in addr_groups.items():
                    if not confs: continue
                    filename = f"{proto}_{at}"
                    header_title = f"{title_prefix} | {proto.upper()} {at.upper()}"
                    self._write_files(base_dir, filename, confs, header_title, fake_configs)
                    all_proto_configs.extend(confs)
                if all_proto_configs:
                    header_title = f"{title_prefix} | {proto.upper()}"
                    self._write_files(base_dir, proto, all_proto_configs, header_title, fake_configs)

        logger.info("Writing files...")
        write_subscription_package(final_list, os.path.join(PATHS['OUTPUT_SUBS'], 'xray'), "PSG")
        write_subscription_package(lite_list, os.path.join(PATHS['OUTPUT_LITE'], 'xray'), "PSG Lite")
        
        for loc, confs in groups['locations'].items():
            safe_name = re.sub(r'[^a-zA-Z0-9]', '', loc) or "XX"
            path = os.path.join(PATHS['OUTPUT_SUBS'], 'locations')
            self._write_files(path, safe_name, confs, f"PSG | Location {loc}")

        for chan, confs in groups['channels'].items():
            # --- FIX: Sanitize channel name to prevent filesystem errors ---
            safe_chan = re.sub(r'[^a-zA-Z0-9_.-]', '_', chan)
            path = os.path.join(PATHS['OUTPUT_SUBS'], 'channels', safe_chan)
            self._write_files(path, 'list', confs, f"PSG | @{chan}")

        with open(PATHS['CONFIG_TXT'], 'w', encoding='utf-8') as f:
            f.write('\n'.join(final_list))
        
        with open(os.path.join(PATHS['API'], 'allConfigs.json'), 'w', encoding='utf-8') as f:
            json.dump(api_data, f, indent=4, ensure_ascii=False)

    def _write_files(self, directory: str, filename: str, configs: List[str], title: str, prepends: List[str] = None):
        """Writes both Normal and Base64 versions of a file."""
        # This will now succeed because initialize() deleted the old bad structure
        os.makedirs(os.path.join(directory, 'normal'), exist_ok=True)
        os.makedirs(os.path.join(directory, 'base64'), exist_ok=True)
        
        merged = (prepends or []) + configs
        content = ConfigUtils.generate_header(title) + '\n'.join(merged)
        b64_content = base64.b64encode(content.encode()).decode()
        
        try:
            with open(os.path.join(directory, 'normal', filename), 'w', encoding='utf-8') as f:
                f.write(content)
            with open(os.path.join(directory, 'base64', filename), 'w', encoding='utf-8') as f:
                f.write(b64_content)
        except IOError as e:
            logger.error(f"Failed to write {filename} in {directory}: {e}")

# --- Entry Point ---

async def main():
    processor = SubscriptionProcessor()
    try:
        # 1. Initialize (This cleans up the old folders causing the error)
        await processor.initialize()
        
        logger.info("1. Fetching Sources")
        await processor.process_sources()
        
        logger.info("2. Deduplicating")
        unique_map = processor.deduplicate_configs()
        
        logger.info("3. Enriching and Tagging (GeoIP + DNS)")
        final, lite, groups, api_data = await processor.enrich_and_tag(unique_map)
        
        logger.info("4. Writing Outputs")
        processor.write_output(final, lite, groups, api_data)
        
    finally:
        # Ensures session is closed even if scripts crash
        await processor.cleanup()
        logger.info("Cleanup done.")

if __name__ == "__main__":
    if os.name == 'nt':
        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    asyncio.run(main())