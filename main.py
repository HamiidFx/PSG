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
    'LITE_LIMIT': 10,
    'TIMEOUT': 15,
    'DNS_WORKERS': 50, # Limit concurrent DNS lookups
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

# --- Utility Class ---

class ConfigUtils:
    @staticmethod
    def safe_base64_decode(s: str) -> str:
        s = s.strip()
        missing_padding = len(s) % 4
        if missing_padding:
            s += '=' * (4 - missing_padding)
        try:
            return base64.b64decode(s).decode('utf-8', errors='ignore')
        except Exception:
            return ""

    @staticmethod
    def detect_type(config: str) -> Optional[str]:
        # Optimization: Check strictly against prefixes
        if config.startswith('vmess://'): return 'vmess'
        if config.startswith('vless://'): return 'vless'
        if config.startswith('trojan://'): return 'trojan'
        if config.startswith('ss://'): return 'ss'
        if config.startswith('tuic://'): return 'tuic'
        if config.startswith(('hy2://', 'hysteria2://')): return 'hy2'
        if config.startswith('hysteria://'): return 'hysteria'
        return None

    @staticmethod
    def is_cloudflare(ip_str: str) -> bool:
        if not ip_str: return False
        try:
            # Optimization: Remove brackets once
            clean_ip = ip_str.strip('[]')
            ip_obj = ipaddress.ip_address(clean_ip)
            return any(ip_obj in net for net in CLOUDFLARE_NETWORKS)
        except ValueError:
            return False

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

    @staticmethod
    def create_fake_config(name: str) -> str:
        encoded_name = quote(name.lstrip('#'))
        return f"vless://00000000-0000-0000-0000-000000000000@127.0.0.1:443?security=none&type=ws&path=/#{encoded_name}"

    @staticmethod
    def get_address_type(host: str) -> str:
        """Determines if host is IPv4, IPv6, or Domain."""
        # Clean brackets from IPv6 [::1]
        host = host.strip('[]')
        try:
            ip = ipaddress.ip_address(host)
            return 'ipv6' if isinstance(ip, ipaddress.IPv6Address) else 'ipv4'
        except ValueError:
            return 'domain'

    @staticmethod
    def is_reality(config: str) -> bool:
        return 'security=reality' in config and config.startswith('vless://')

    @staticmethod
    def is_xhttp(config: str) -> bool:
        return 'type=xhttp' in config

class ConfigParser:
    """Handles parsing and reassembling of configuration strings safely."""
    
    @staticmethod
    def parse(config_str: str) -> Optional[Dict]:
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
            # Log valid parsing errors for debugging
            # logger.debug(f"Failed to parse {ctype}: {config_str[:20]}...")
            return None

    @staticmethod
    def _parse_vmess(config_str: str) -> Dict:
        b64 = config_str[8:]
        data = json.loads(ConfigUtils.safe_base64_decode(b64))
        return {
            'type': 'vmess',
            'ps': data.get('ps', ''),
            'add': data.get('add', ''),
            'port': str(data.get('port', '')),
            'id': data.get('id', ''),
            'net': data.get('net', ''),
            'type_transport': data.get('type', ''),
            'host': data.get('host', ''),
            'path': data.get('path', ''),
            'tls': data.get('tls', ''),
            'sni': data.get('sni', ''),
            'full_data': data
        }

    @staticmethod
    def _parse_ss(config_str: str) -> Dict:
        parsed = urlparse(config_str)
        # Handle cases where user info is base64 encoded
        if '@' in parsed.netloc:
            user_info_raw, host_port = parsed.netloc.split('@', 1)
        else:
            user_info_raw, host_port = parsed.netloc, ""

        method, password = "auto", ""
        try:
            # Attempt decode, but handle failures gracefully
            decoded = ConfigUtils.safe_base64_decode(user_info_raw)
            if ':' in decoded:
                method, password = decoded.split(':', 1)
            else:
                method = "auto"
                password = decoded # Fallback
        except:
            pass
            
        host, _, port = host_port.partition(':')
        
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
            'user': parsed.username or '',
            'password': parsed.password or '',
            'host': parsed.hostname or '',
            'port': str(parsed.port) if parsed.port else '',
            'params': clean_params,
            'path': parsed.path
        }

    @staticmethod
    def reassemble(parsed: Dict, new_tag: str = None) -> Optional[str]:
        if not parsed: return None
        try:
            ctype = parsed.get('type')
            if ctype == 'vmess':
                data = parsed.get('full_data', {}).copy()
                if new_tag: data['ps'] = new_tag
                # Ensure critical fields exist
                data.setdefault('add', '127.0.0.1')
                data.setdefault('port', 443)
                json_str = json.dumps(data, separators=(',', ':'), ensure_ascii=False)
                return 'vmess://' + base64.b64encode(json_str.encode()).decode()

            elif ctype == 'ss':
                user_pass = f"{parsed.get('method')}:{parsed.get('password')}"
                b64_user = base64.b64encode(user_pass.encode()).decode()
                host = parsed.get('host', '')
                if ':' in host and not host.startswith('['): host = f"[{host}]"
                uri = f"ss://{b64_user}@{host}:{parsed.get('port', '')}"
                name = new_tag if new_tag else parsed.get('name', '')
                return f"{uri}#{quote(name)}"

            else:
                # Generic reassembly for vless, trojan, etc.
                user = parsed.get('user', '')
                password = parsed.get('password', '') 
                userinfo = f"{user}:{password}" if password else user
                
                host = parsed.get('host', '')
                if ':' in host and not host.startswith('['): host = f"[{host}]"
                
                netloc = f"{userinfo}@{host}:{parsed.get('port', '')}"
                
                query_params = parsed.get('params', {}).copy()
                path = parsed.get('path', '')
                
                # Logic to handle path inside params vs URI path
                full_path = ""
                if ctype in ['vless', 'trojan']:
                    full_path = path
                    if query_params: full_path += "?" + urlencode(query_params, doseq=True)
                else:
                    if path and path != '/': query_params['path'] = path
                    if query_params: full_path = "?" + urlencode(query_params, doseq=True)
                
                name = new_tag if new_tag else parsed.get('hash', '')
                return f"{ctype}://{netloc}{full_path}#{quote(name)}"
        except Exception as e:
            logger.error(f"Reassembly error: {e}")
            return None

    @staticmethod
    def get_fingerprint(parsed: Dict) -> str:
        """Generates a unique signature for deduplication."""
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
            param_str = "&".join(f"{k}={v}" for k, v in sorted(params.items()))
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

    async def initialize(self):
        self.session = aiohttp.ClientSession()
        # Ensure directories
        for path in [PATHS['TEMP'], PATHS['FINAL_ASSETS'], PATHS['API'], 
                     os.path.join(PATHS['TEMP'], 'logos'), 
                     os.path.join(PATHS['TEMP'], 'html_cache')]:
            os.makedirs(path, exist_ok=True)
        
        # Prepare GEOIP
        await self._setup_geoip()

    async def cleanup(self):
        if self.session: await self.session.close()
        if self.geo_reader: self.geo_reader.close()

    async def _fetch_url(self, url: str) -> Optional[bytes]:
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

    async def resolve_ip(self, host: str) -> Optional[str]:
        if not host: return None
        if host in self.dns_cache: return self.dns_cache[host]
        
        async with self.dns_semaphore:
            try:
                loop = asyncio.get_running_loop()
                # Run blocking socket call in executor
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
        
        # Aggregate results
        logos_to_fetch = {}
        for key, configs, logo_url in results:
            if logo_url: logos_to_fetch[key] = logo_url
            for c in configs: self.all_configs.append((c, key))
            
        # Download Logos (Optional - Fire and forget mostly)
        logo_tasks = [self._fetch_and_save_logo(k, u) for k, u in logos_to_fetch.items()]
        if logo_tasks: await asyncio.gather(*logo_tasks)

        # Private Configs
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
            # Attempt base64 decode if it looks like a sub
            if data.get('subscription_url'):
                try:
                    decoded = ConfigUtils.safe_base64_decode(text)
                    if 'vmess://' in decoded or 'vless://' in decoded:
                        text = decoded
                except: pass
            
            configs = PROTOCOL_REGEX.findall(text)
            
            # Metadata extraction
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
            with open(os.path.join(PATHS['TEMP'], 'logos', f"{key}.jpg"), 'wb') as f:
                f.write(data)

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
                
                # Update assets
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
        
        # Categorized collections
        groups = {
            'channels': defaultdict(list),
            'locations': defaultdict(list)
        }
        
        channel_counts = defaultdict(int)
        
        total = len(unique_map)
        logger.info(f"Processing {total} unique configs...")

        # Process in chunks or one-by-one with DNS resolution
        # We need to resolve IPs to get Geo info
        
        for i, (fp, (orig, parsed, chan)) in enumerate(unique_map.items()):
            if i % 100 == 0: sys.stdout.write(f"\rProcessing... {int(i/total*100)}%")
            
            clean_chan = chan.strip().lstrip('@')
            host = parsed.get('host') or parsed.get('add', '')
            
            ip = await self.resolve_ip(host)
            country_code = self.get_geo_code(ip)
            is_cf = ConfigUtils.is_cloudflare(ip)
            flag = self.get_flag(country_code)
            
            ctype_disp = parsed.get('type', 'UNK').upper()
            
            # Create Tag
            new_tag = f"{flag} {country_code} | {ctype_disp} | @{clean_chan}"
            final_str = ConfigParser.reassemble(parsed, new_tag)
            
            if not final_str: continue
            
            final_list.append(final_str)
            
            # Groups
            groups['channels'][clean_chan].append(final_str)
            groups['locations'][country_code].append(final_str)
            if is_cf:
                groups['locations']['CF'].append(final_str)
            
            # Lite List (Limited count)
            if channel_counts[clean_chan] < CONSTANTS['LITE_LIMIT']:
                lite_list.append(final_str)
                channel_counts[clean_chan] += 1
                
            # API Data
            eff_type = parsed['type']
            if eff_type == 'vless' and 'security=reality' in final_str: eff_type = 'reality'
            assets = self.channel_assets.get(clean_chan, {})
            
            api_data.append({
                'channel': {'username': clean_chan, 'title': assets.get('title', ''), 'logo': assets.get('logo', '')},
                'country': country_code,
                'flag': flag,
                'type': eff_type,
                'config': final_str,
                'is_cf': is_cf
            })
            
        print("\nProcessing complete.")
        return final_list, lite_list, groups, api_data

    def write_output(self, final_list, lite_list, groups, api_data):
        # 1. Update Assets JSON
        sorted_assets = dict(sorted(self.channel_assets.items()))
        with open(os.path.join(PATHS['TEMP'], 'channelsAssets.json'), 'w', encoding='utf-8') as f:
            json.dump(sorted_assets, f, indent=4, ensure_ascii=False)
        
        if os.path.exists(PATHS['FINAL_ASSETS']): shutil.rmtree(PATHS['FINAL_ASSETS'])
        shutil.copytree(PATHS['TEMP'], PATHS['FINAL_ASSETS'])

        # 2. Helper to write subscription packages (DRY)
        def write_subscription_package(configs: List[str], base_dir: str, title_prefix: str):
            """
            Groups configs by Protocol AND Address Type (IPv4/IPv6/Domain),
            then writes Normal and Base64 files for each group.
            """
            
            # Data Structure: groups[protocol][address_type] = [list_of_configs]
            # using defaultdict to avoid 'if key not in dict' checks
            groups = defaultdict(lambda: defaultdict(list))
            
            fake_configs = [ConfigUtils.create_fake_config(n) for n in CONSTANTS['FAKE_NAMES']]
            
            # --- 1. Categorize ---
            for c in configs:
                ct = ConfigUtils.detect_type(c)
                if not ct: continue
                
                # We must parse to get the host to determine address type
                parsed = ConfigParser.parse(c)
                if not parsed: continue
                
                host = parsed.get('host') or parsed.get('add', '')
                addr_type = ConfigUtils.get_address_type(host)
                
                # Standard Grouping (e.g., vmess_ipv4)
                groups[ct][addr_type].append(c)
                
                # Special Case: Reality (Subset of Vless)
                if ct == 'vless' and ConfigUtils.is_reality(c):
                    groups['reality'][addr_type].append(c)
                
                # Special Case: XHTTP
                if ConfigUtils.is_xhttp(c):
                    groups['xhttp'][addr_type].append(c)

            # --- 2. Write "Mix" File (All protocols combined) ---
            self._write_files(base_dir, 'mix', configs, f"{title_prefix} | MIX", fake_configs)

            # --- 3. Write Categorized Files ---
            for proto, addr_groups in groups.items():
                
                # We collect all configs for this protocol to write the "Main" protocol file
                # e.g., 'vmess' (containing ipv4 + ipv6 + domain)
                all_proto_configs = []
                
                for at, confs in addr_groups.items():
                    if not confs: continue
                    
                    # Write specific type: e.g., 'vmess_ipv4', 'vless_domain'
                    filename = f"{proto}_{at}"
                    header_title = f"{title_prefix} | {proto.upper()} {at.upper()}"
                    self._write_files(base_dir, filename, confs, header_title, fake_configs)
                    
                    all_proto_configs.extend(confs)
                
                # Write the generic protocol file (e.g., 'vmess')
                if all_proto_configs:
                    header_title = f"{title_prefix} | {proto.upper()}"
                    self._write_files(base_dir, proto, all_proto_configs, header_title, fake_configs)

        # 3. Write Subscriptions
        logger.info("Writing files...")
        write_subscription_package(final_list, os.path.join(PATHS['OUTPUT_SUBS'], 'xray'), "PSG")
        write_subscription_package(lite_list, os.path.join(PATHS['OUTPUT_LITE'], 'xray'), "PSG Lite")
        
        # 4. Locations & Channels
        for loc, confs in groups['locations'].items():
            safe_name = re.sub(r'[^a-zA-Z0-9]', '', loc) or "XX"
            path = os.path.join(PATHS['OUTPUT_SUBS'], 'locations')
            self._write_files(path, safe_name, confs, f"PSG | Location {loc}")

        for chan, confs in groups['channels'].items():
            path = os.path.join(PATHS['OUTPUT_SUBS'], 'channels', chan)
            self._write_files(path, 'list', confs, f"PSG | @{chan}")

        # 5. Config TXT & API
        with open(PATHS['CONFIG_TXT'], 'w', encoding='utf-8') as f:
            f.write('\n'.join(final_list))
        
        with open(os.path.join(PATHS['API'], 'allConfigs.json'), 'w', encoding='utf-8') as f:
            json.dump(api_data, f, indent=4, ensure_ascii=False)

    def _write_files(self, directory: str, filename: str, configs: List[str], title: str, prepends: List[str] = None):
        """Writes both Normal and Base64 versions of a file."""
        os.makedirs(os.path.join(directory, 'normal'), exist_ok=True)
        os.makedirs(os.path.join(directory, 'base64'), exist_ok=True)
        
        merged = (prepends or []) + configs
        # Use join for efficient string building
        content = ConfigUtils.generate_header(title) + '\n'.join(merged)
        b64_content = base64.b64encode(content.encode()).decode()
        
        # Try/Except block for file safety
        try:
            with open(os.path.join(directory, 'normal', filename), 'w', encoding='utf-8') as f:
                f.write(content)
            with open(os.path.join(directory, 'base64', filename), 'w', encoding='utf-8') as f:
                f.write(b64_content)
        except IOError as e:
            logger.error(f"Failed to write {filename}: {e}")

# --- Entry Point ---

async def main():
    processor = SubscriptionProcessor()
    await processor.initialize()
    
    logger.info("1. Fetching Sources")
    await processor.process_sources()
    
    logger.info("2. Deduplicating")
    unique_map = processor.deduplicate_configs()
    
    logger.info("3. Enriching and Tagging (GeoIP + DNS)")
    final, lite, groups, api_data = await processor.enrich_and_tag(unique_map)
    
    logger.info("4. Writing Outputs")
    processor.write_output(final, lite, groups, api_data)
    
    await processor.cleanup()
    logger.info("Done.")

if __name__ == "__main__":
    if os.name == 'nt':
        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    asyncio.run(main())