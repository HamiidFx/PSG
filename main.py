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
    """
    Handles parsing for analysis (GeoIP) and safely renaming configs 
    without losing data (Non-destructive reassembly).
    """

    @staticmethod
    def parse(config_str: str) -> Optional[Dict]:
        """
        Parses the config ONLY to extract Host/IP and Type for classification.
        Returns a dict containing the 'original_config' to ensure no data loss.
        """
        ctype = ConfigUtils.detect_type(config_str)
        if not ctype: return None

        host = ""
        # 1. Parse VMess
        if ctype == 'vmess':
            try:
                b64 = config_str[8:]
                # Fix padding if necessary
                missing_padding = len(b64) % 4
                if missing_padding: b64 += '=' * (4 - missing_padding)
                
                json_str = base64.b64decode(b64).decode('utf-8', errors='ignore')
                data = json.loads(json_str)
                host = data.get('host') or data.get('add') or data.get('sni') or ""
                return {
                    'type': 'vmess',
                    'host': host,
                    'original_config': config_str,
                    # We store the JSON data to update the name later safely
                    'vmess_json': data 
                }
            except Exception:
                return None

        # 2. Parse URI Schemes (ss, vless, trojan, tuic, hy2, etc.)
        try:
            parsed = urlparse(config_str)
            
            # Extract Host
            # Handle [IPv6] brackets
            netloc = parsed.netloc
            if '@' in netloc:
                _, host_port = netloc.rsplit('@', 1)
            else:
                host_port = netloc
                
            if host_port.startswith('['):
                # IPv6
                host = host_port.split(']')[0].strip('[')
            elif ':' in host_port:
                # IPv4 or Domain with port
                host = host_port.split(':')[0]
            else:
                host = host_port

            return {
                'type': ctype,
                'host': host,
                'original_config': config_str,
                'uri_parsed': parsed # Store the parsed object for safe fragment replacement
            }
        except Exception:
            return None

    @staticmethod
    def reassemble(parsed_data: Dict, new_tag: str) -> Optional[str]:
        """
        Updates the name/tag of the config WITHOUT reconstructing the whole string.
        This prevents missing fields (plugins, flow, allowInsecure, etc.).
        """
        if not parsed_data: return None
        
        ctype = parsed_data.get('type')
        
        # --- Case 1: VMess (JSON inside Base64) ---
        if ctype == 'vmess':
            try:
                # Get the original JSON we saved
                data = parsed_data.get('vmess_json', {}).copy()
                
                # Update only the Name
                data['ps'] = new_tag
                
                # Re-encode strictly
                json_str = json.dumps(data, separators=(',', ':'), ensure_ascii=False)
                return 'vmess://' + base64.b64encode(json_str.encode()).decode()
            except Exception:
                # Fallback: return original if we can't rename
                return parsed_data.get('original_config')

        # --- Case 2: URI Schemes (SS, Vless, etc.) ---
        try:
            # We use the original parsed object
            original_parsed = parsed_data.get('uri_parsed')
            if not original_parsed: return parsed_data.get('original_config')
            
            # Safely replace ONLY the fragment (the part after #)
            # quote() ensures emojis and spaces in the tag don't break the URL
            new_parsed = original_parsed._replace(fragment=quote(new_tag))
            
            return new_parsed.geturl()
        except Exception:
             return parsed_data.get('original_config')

    @staticmethod
    def get_fingerprint(parsed_data: Dict) -> str:
        """
        Generates a unique signature. 
        For non-destructive parsing, we use the 'host' and 'port' and 'path' 
        from the string, or just the raw string minus the hash.
        """
        try:
            ctype = parsed_data['type']
            
            if ctype == 'vmess':
                d = parsed_data.get('vmess_json', {})
                # Unique ID + Addr + Port
                return f"vmess|{d.get('id')}|{d.get('add')}|{d.get('port')}"
            
            else:
                # For URIs, the unique part is everything BEFORE the fragment (#)
                # This treats 'vless://...@host?key=1#nameA' and '...#nameB' as duplicates
                orig = parsed_data.get('original_config', '')
                if '#' in orig:
                    return orig.split('#')[0]
                return orig
        except:
            # Fallback to random to avoid deletion if fingerprinting fails
            return parsed_data.get('original_config', '')

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
        logger.info(f"Processing {total} unique configs...")

        for i, (fp, (orig, parsed, chan)) in enumerate(unique_map.items()):
            if i % 100 == 0: sys.stdout.write(f"\rProcessing... {int(i/total*100)}%")
            
            clean_chan = chan.strip().lstrip('@')
            host = parsed.get('host') or parsed.get('add', '')
            
            ip = await self.resolve_ip(host)
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