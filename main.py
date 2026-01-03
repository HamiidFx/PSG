import asyncio
import aiohttp
import json
import os
import re
import base64
import shutil
import ipaddress
import urllib.parse
import socket
import geoip2.database
import sys
from urllib.parse import urlparse, parse_qs, urlencode, unquote, quote
from datetime import datetime, timezone
from collections import defaultdict

# --- Configuration Constants ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
INPUT_FILE = os.path.join(BASE_DIR, 'channelsData', 'channelsAssets.json')
FINAL_ASSETS_DIR = os.path.join(BASE_DIR, 'channelsData')
TEMP_BUILD_DIR = os.path.join(BASE_DIR, 'temp_build')
HTML_CACHE_DIR = os.path.join(TEMP_BUILD_DIR, 'html_cache')
LOGOS_DIR = os.path.join(TEMP_BUILD_DIR, 'logos')
API_DIR = os.path.join(BASE_DIR, 'api')

# Output Directories
SUBS_DIR = os.path.join(BASE_DIR, 'subscriptions', 'xray')
LITE_DIR = os.path.join(BASE_DIR, 'lite', 'subscriptions', 'xray')
CHANNELS_SUBS_DIR = os.path.join(BASE_DIR, 'subscriptions', 'channels')
LOCATIONS_SUBS_DIR = os.path.join(BASE_DIR, 'subscriptions', 'locations')

GEOIP_DB_PATH = os.path.join(BASE_DIR, 'Country.mmdb')

# Limits
LITE_LIMIT = 10  # Max configs per channel for Lite

# URLs
GITHUB_LOGO_BASE_URL = 'https://raw.githubusercontent.com/itsyebekhe/PSG/main/channelsData/logos'
PRIVATE_CONFIGS_URL = 'https://raw.githubusercontent.com/itsyebekhe/PSGP/main/private_configs.json'

# Output Files
CONFIG_FILE = os.path.join(BASE_DIR, 'config.txt')
API_OUTPUT_FILE = os.path.join(API_DIR, 'allConfigs.json')

# Fake Configs
FAKE_CONFIG_NAMES = ['#همکاری_ملی', '#جاویدشاه', '#KingRezaPahlavi']

# Regex
PROTOCOL_REGEX = r'(?:vmess|vless|trojan|ss|tuic|hy2|hysteria2?):\/\/[^\s"\']+(?=\s|<|>|$)'

# Cloudflare CIDRs
CLOUDFLARE_CIDR_STRINGS = [
    "173.245.48.0/20","103.21.244.0/22","103.22.200.0/22","103.31.4.0/22",
    "141.101.64.0/18","108.162.192.0/18","190.93.240.0/20","188.114.96.0/20",
    "197.234.240.0/22","198.41.128.0/17","162.158.0.0/15","104.16.0.0/13",
    "104.24.0.0/14","172.64.0.0/13","131.0.72.0/22","2400:cb00::/32",
    "2606:4700::/32","2803:f800::/32","2405:b500::/32","2405:8100::/32",
    "2a06:98c0::/29","2c0f:f248::/32"
]
# Pre-compile networks for performance
CLOUDFLARE_NETWORKS = [ipaddress.ip_network(cidr) for cidr in CLOUDFLARE_CIDR_STRINGS]

# --- Helper Functions ---

def safe_base64_decode(s):
    s = s.strip()
    missing_padding = len(s) % 4
    if missing_padding:
        s += '=' * (4 - missing_padding)
    try:
        return base64.b64decode(s).decode('utf-8', errors='ignore')
    except:
        return ""

def detect_type(config):
    if config.startswith('vmess://'): return 'vmess'
    if config.startswith('vless://'): return 'vless'
    if config.startswith('trojan://'): return 'trojan'
    if config.startswith('ss://'): return 'ss'
    if config.startswith('tuic://'): return 'tuic'
    if config.startswith(('hy2://', 'hysteria2://')): return 'hy2'
    if config.startswith('hysteria://'): return 'hysteria'
    return None

def get_address_type(host):
    host = host.strip('[]')
    try:
        ip = ipaddress.ip_address(host)
        return 'ipv6' if isinstance(ip, ipaddress.IPv6Address) else 'ipv4'
    except ValueError:
        return 'domain'

def is_cloudflare(ip_str):
    if not ip_str: return False
    try:
        ip_obj = ipaddress.ip_address(ip_str.strip('[]'))
        for net in CLOUDFLARE_NETWORKS:
            if ip_obj in net:
                return True
    except:
        pass
    return False

def is_reality(config):
    return 'security=reality' in config and config.startswith('vless://')

def is_xhttp(config):
    return 'type=xhttp' in config

def create_fake_config(name):
    encoded_name = quote(name.lstrip('#'))
    return f"vless://00000000-0000-0000-0000-000000000000@127.0.0.1:443?security=none&type=ws&path=/#{encoded_name}"

def hiddify_header(title):
    b64_title = base64.b64encode(title.encode()).decode()
    return f"""#profile-title: base64:{b64_title}
#profile-update-interval: 1
#subscription-userinfo: upload=0; download=0; total=10737418240000000; expire=2546249531
#support-url: https://t.me/yebekhe
#profile-web-page-url: https://github.com/itsyebekhe/PSG

"""

def parse_config(config_str):
    ctype = detect_type(config_str)
    if not ctype: return None
    
    try:
        if ctype == 'vmess':
            b64 = config_str[8:]
            data = json.loads(safe_base64_decode(b64))
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
        elif ctype == 'ss':
            parsed = urlparse(config_str)
            user_info_b64 = parsed.netloc.split('@')[0] if '@' in parsed.netloc else ''
            host_port = parsed.netloc.split('@')[-1] if '@' in parsed.netloc else parsed.netloc
            method = ""
            password = ""
            if user_info_b64:
                try:
                    decoded_user_pass = safe_base64_decode(user_info_b64)
                    if ':' in decoded_user_pass:
                        method, password = decoded_user_pass.split(':', 1)
                    else:
                        method = "auto"
                        password = decoded_user_pass
                except: pass
            
            host_parts = host_port.split(':')
            host = host_parts[0]
            port = host_parts[1] if len(host_parts) > 1 else ''
            return {
                'type': 'ss',
                'name': unquote(parsed.fragment),
                'host': host,
                'port': str(port),
                'method': method,
                'password': password
            }
        else: # vless, trojan, etc.
            parsed = urlparse(config_str)
            params = parse_qs(parsed.query)
            clean_params = {}
            for k, v in params.items():
                if isinstance(v, list): clean_params[k] = v[0] if v else ""
                else: clean_params[k] = v

            return {
                'type': ctype,
                'hash': unquote(parsed.fragment),
                'user': parsed.username if parsed.username else '',
                'password': parsed.password if parsed.password else '',
                'host': parsed.hostname if parsed.hostname else '',
                'port': str(parsed.port) if parsed.port else '',
                'params': clean_params,
                'path': parsed.path
            }
    except: return None

def reassemble_config(parsed, new_name=None):
    if not parsed: return None
    ctype = parsed.get('type')

    if ctype == 'vmess':
        data = parsed.get('full_data', {}).copy()
        if new_name: data['ps'] = new_name
        data.setdefault('add', '127.0.0.1')
        data.setdefault('port', 443)
        data.setdefault('id', '')
        json_str = json.dumps(data, separators=(',', ':'), ensure_ascii=False)
        return 'vmess://' + base64.b64encode(json_str.encode()).decode()

    elif ctype == 'ss':
        method = parsed.get('method', 'chacha20-ietf-poly1305')
        password = parsed.get('password', '')
        user_pass = f"{method}:{password}"
        b64_user = base64.b64encode(user_pass.encode()).decode()
        host = parsed.get('host', '')
        if ':' in host and not host.startswith('['): host = f"[{host}]"
        uri = f"ss://{b64_user}@{host}:{parsed.get('port', '')}"
        name = new_name if new_name else parsed.get('name', '')
        return f"{uri}#{quote(name)}"

    else:
        user = parsed.get('user', '')
        password = parsed.get('password', '') 
        userinfo = user
        if password: userinfo += f":{password}"
        host = parsed.get('host', '')
        if ':' in host and not host.startswith('['): host = f"[{host}]"
        netloc = f"{userinfo}@{host}:{parsed.get('port', '')}"
        query_params = parsed.get('params', {}).copy()
        path = parsed.get('path', '')
        full_path = ""
        if ctype in ['vless', 'trojan']:
             full_path = path
             if query_params: full_path += "?" + urlencode(query_params, doseq=True)
        else:
             if path and path != '/': query_params['path'] = path
             if query_params: full_path = "?" + urlencode(query_params, doseq=True)
        name = new_name if new_name else parsed.get('hash', '')
        return f"{ctype}://{netloc}{full_path}#{quote(name)}"

def get_unique_fingerprint(parsed):
    if not parsed: return ""
    ctype = parsed['type']
    def norm(s): return str(s).strip().lower()

    if ctype == 'vmess':
        return "|".join([
            'vmess',
            norm(parsed.get('add', '')),
            norm(parsed.get('port', '')),
            norm(parsed.get('id', '')),
            norm(parsed.get('net', '')),
            norm(parsed.get('type_transport', '')),
            norm(parsed.get('path', '')),
            norm(parsed.get('host', '')),
            norm(parsed.get('sni', ''))
        ])
    elif ctype == 'ss':
        return "|".join([
            'ss',
            norm(parsed.get('host', '')),
            norm(parsed.get('port', '')),
            norm(parsed.get('method', '')),
            norm(parsed.get('password', ''))
        ])
    else: 
        params = parsed.get('params', {})
        sorted_params = sorted(params.items())
        param_str = "&".join([f"{k}={v}" for k, v in sorted_params])
        return "|".join([
            norm(ctype),
            norm(parsed.get('user', '')),
            norm(parsed.get('host', '')),
            norm(parsed.get('port', '')),
            norm(parsed.get('path', '')),
            norm(param_str)
        ])

# --- Async Tasks ---

async def fetch_url(session, url, retries=3):
    for i in range(retries):
        try:
            async with session.get(url, timeout=15) as response:
                if response.status == 200: return await response.read()
        except: pass
        if i < retries - 1: await asyncio.sleep(1 + i)
    return None

async def process_source(session, source_key, source_data, channel_assets_dict):
    url = source_data.get('subscription_url')
    if not url: url = f"https://t.me/s/{source_key}"
    
    content_bytes = await fetch_url(session, url)
    
    extracted_types = set()
    configs_found = []
    logo_url = None
    title = source_data.get('title', source_key)

    if content_bytes:
        try:
            content_str = content_bytes.decode('utf-8', errors='ignore')
            is_sub = False
            decoded_sub = ""
            if source_data.get('subscription_url'):
                try:
                    decoded_sub = safe_base64_decode(content_str)
                    if any(p in decoded_sub for p in ['vmess://', 'vless://', 'ss://', 'trojan://']):
                        is_sub = True
                except: pass
            text_to_scan = decoded_sub if is_sub else content_str
            matches = re.findall(PROTOCOL_REGEX, text_to_scan, re.IGNORECASE)
            configs_found = matches
            for conf in configs_found:
                ctype = detect_type(conf)
                if ctype: extracted_types.add(ctype)
            if not is_sub and content_str:
                cache_path = os.path.join(HTML_CACHE_DIR, f"{source_key}.html")
                try:
                    with open(cache_path, 'w', encoding='utf-8') as f: f.write(content_str)
                except: pass
                t_match = re.search(r'<meta property="twitter:title" content="(.*?)">', content_str, re.IGNORECASE)
                i_match = re.search(r'<meta property="twitter:image" content="(.*?)">', content_str, re.IGNORECASE)
                if t_match: title = t_match.group(1)
                if i_match: logo_url = i_match.group(1)
        except: pass

    channel_assets_dict[source_key] = {
        'title': title,
        'logo': GITHUB_LOGO_BASE_URL + f"/{source_key}.jpg" if logo_url else (source_data.get('logo', '')),
        'types': sorted(list(extracted_types))
    }
    return source_key, configs_found, logo_url

# --- GeoIP ---

async def download_geoip_db(session):
    if os.path.exists(GEOIP_DB_PATH):
        if (datetime.now(timezone.utc).timestamp() - os.path.getmtime(GEOIP_DB_PATH)) < 86400:
            print("Using existing GeoIP Database.")
            return GEOIP_DB_PATH
    print("Downloading latest GeoIP Database...")
    url = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
    try:
        async with session.get(url) as resp:
            if resp.status == 200:
                with open(GEOIP_DB_PATH, 'wb') as f: f.write(await resp.read())
                return GEOIP_DB_PATH
    except: pass
    return GEOIP_DB_PATH if os.path.exists(GEOIP_DB_PATH) else None

def get_flag_emoji(country_code):
    if not country_code or len(country_code) != 2: return "🏳️"
    return chr(127397 + ord(country_code[0])) + chr(127397 + ord(country_code[1]))

def get_geo_info(reader, ip):
    if not reader or not ip: return "XX"
    try:
        response = reader.country(ip)
        return response.country.iso_code or "XX"
    except: return "XX"

# --- Main Logic ---

async def main():
    print("--- STARTING PYTHON BOT ---")
    
    if os.path.exists(TEMP_BUILD_DIR): shutil.rmtree(TEMP_BUILD_DIR)
    os.makedirs(HTML_CACHE_DIR, exist_ok=True)
    os.makedirs(LOGOS_DIR, exist_ok=True)
    os.makedirs(FINAL_ASSETS_DIR, exist_ok=True)
    os.makedirs(os.path.join(LITE_DIR, 'normal'), exist_ok=True)
    os.makedirs(os.path.join(LITE_DIR, 'base64'), exist_ok=True)
    os.makedirs(CHANNELS_SUBS_DIR, exist_ok=True)

    if not os.path.exists(INPUT_FILE):
        print(f"Error: {INPUT_FILE} not found.")
        return

    with open(INPUT_FILE, 'r', encoding='utf-8') as f:
        sources_data = json.load(f)

    channel_assets_results = {}
    all_raw_configs = []
    logos_to_fetch = {}

    async with aiohttp.ClientSession() as session:
        print(f"\n1. Fetching content for {len(sources_data)} sources...")
        fetch_tasks = []
        for key, data in sources_data.items():
            fetch_tasks.append(process_source(session, key, data, channel_assets_results))
        fetch_results = await asyncio.gather(*fetch_tasks)
        for key, configs, logo_url in fetch_results:
            if logo_url: logos_to_fetch[key] = logo_url
            for c in configs: all_raw_configs.append((c, key))

        if logos_to_fetch:
            print(f"\n2. Fetching {len(logos_to_fetch)} logos...")
            logo_tasks = []
            for key, url in logos_to_fetch.items():
                async def fetch_logo(k, u):
                    d = await fetch_url(session, u)
                    if d:
                        try:
                            with open(os.path.join(LOGOS_DIR, f"{k}.jpg"), 'wb') as f: f.write(d)
                        except: pass
                logo_tasks.append(fetch_logo(key, url))
            await asyncio.gather(*logo_tasks)

        print("\n3. Integrating Private Configs...")
        p_bytes = await fetch_url(session, PRIVATE_CONFIGS_URL)
        if p_bytes:
            try:
                p_confs = json.loads(p_bytes)
                for c_name, confs in p_confs.items():
                    c_name = c_name.strip()
                    if not c_name: continue
                    p_types = set()
                    for c in confs:
                        ct = detect_type(c)
                        if ct:
                            p_types.add(ct)
                            all_raw_configs.append((c, c_name))
                    if c_name in channel_assets_results:
                        channel_assets_results[c_name]['types'] = sorted(list(set(channel_assets_results[c_name]['types']) | p_types))
                    else:
                        channel_assets_results[c_name] = {'title': c_name, 'logo': '', 'types': sorted(list(p_types))}
            except: pass
        
        db_path = await download_geoip_db(session)

    print("\n4. Saving assets...")
    sorted_assets = dict(sorted(channel_assets_results.items()))
    with open(os.path.join(TEMP_BUILD_DIR, 'channelsAssets.json'), 'w', encoding='utf-8') as f:
        json.dump(sorted_assets, f, indent=4, ensure_ascii=False)
    if os.path.exists(FINAL_ASSETS_DIR): shutil.rmtree(FINAL_ASSETS_DIR)
    shutil.copytree(TEMP_BUILD_DIR, FINAL_ASSETS_DIR)

    print(f"\n5. Deduplicating {len(all_raw_configs)} raw configs...")
    unique_map = {}
    for conf_str, chan in all_raw_configs:
        parsed = parse_config(conf_str)
        if not parsed: continue
        fp = get_unique_fingerprint(parsed)
        orig_name = ""
        if parsed['type'] == 'vmess': orig_name = parsed.get('ps', '')
        elif parsed['type'] == 'ss': orig_name = parsed.get('name', '')
        else: orig_name = parsed.get('hash', '')
        if fp not in unique_map:
            unique_map[fp] = (orig_name, parsed, chan)
    print(f"   Reduced to {len(unique_map)} unique configs.")

    final_list = []
    lite_list = [] 
    api_list = []
    channel_groups = defaultdict(list)
    location_groups = defaultdict(list) # Stores configs by Country Code and 'CF'
    
    geo_reader = None
    try:
        if db_path: geo_reader = geoip2.database.Reader(db_path)
    except: pass

    dns_cache = {}
    channel_counts = defaultdict(int)

    # --- PROGRESS BAR VARIABLES ---
    total_configs = len(unique_map)
    processed_count = 0
    bar_width = 30 # Length of the visual bar

    print(f"   Tagging {total_configs} configs with GeoIP and Cloudflare check...")
    
    for _, (orig, parsed, chan) in unique_map.items():
        # --- Progress Bar Update ---
        processed_count += 1
        if processed_count % 10 == 0 or processed_count == total_configs: # Update every 10 for speed
            percent = int((processed_count / total_configs) * 100)
            filled = int(bar_width * processed_count // total_configs)
            bar = '=' * filled + '-' * (bar_width - filled)
            sys.stdout.write(f"\r   [{bar}] {percent}% ({processed_count}/{total_configs})")
            sys.stdout.flush()
        # ---------------------------

        clean_chan = chan.strip().lstrip('@')
        host = parsed.get('host', parsed.get('add', ''))
        ip = None
        if host:
            if host in dns_cache: ip = dns_cache[host]
            else:
                try:
                    loop = asyncio.get_running_loop()
                    ip = await loop.run_in_executor(None, socket.gethostbyname, host)
                    dns_cache[host] = ip
                except: dns_cache[host] = None

        code = get_geo_info(geo_reader, ip)
        
        # Check Cloudflare
        is_cf = is_cloudflare(ip)
        
        flag = get_flag_emoji(code)
        
        ctype_up = parsed.get('type', 'UNK').upper()
        if ctype_up == 'VMESS': ctype_up = 'VMESS'
        
        new_tag = f"{flag} {code} | {ctype_up} | @{clean_chan}"
        final_str = reassemble_config(parsed, new_tag)
        if not final_str: continue

        final_list.append(final_str)
        channel_groups[clean_chan].append(final_str)
        
        # Location grouping
        location_groups[code].append(final_str)
        if is_cf:
            location_groups['CF'].append(final_str)

        if channel_counts[clean_chan] < LITE_LIMIT:
            lite_list.append(final_str)
            channel_counts[clean_chan] += 1
        
        assets = sorted_assets.get(clean_chan, {})
        eff_type = parsed.get('type')
        if eff_type == 'vless' and is_reality(final_str): eff_type = 'reality'
        api_list.append({
            'channel': {'username': clean_chan, 'title': assets.get('title', ''), 'logo': assets.get('logo', '')},
            'country': code, 'flag': flag, 'type': eff_type, 'config': final_str, 'is_cf': is_cf
        })
    
    print() # New line after progress bar finishes
    if geo_reader: geo_reader.close()

    print("\n6. Writing output files...")
    
    def write_groups(config_list, output_base_dir):
        groups = {}
        fakes = [create_fake_config(n) for n in FAKE_CONFIG_NAMES]

        for c in config_list:
            ct = detect_type(c)
            if not ct: continue
            p = parse_config(c)
            if not p: continue
            h = p.get('host', p.get('add', ''))
            at = get_address_type(h)
            
            if ct not in groups: groups[ct] = {}
            if at not in groups[ct]: groups[ct][at] = []
            groups[ct][at].append(c)
            
            if ct == 'vless' and is_reality(c):
                if 'reality' not in groups: groups['reality'] = {}
                if at not in groups['reality']: groups['reality'][at] = []
                groups['reality'][at].append(c)
            if is_xhttp(c):
                if 'xhttp' not in groups: groups['xhttp'] = {}
                if at not in groups['xhttp']: groups['xhttp'][at] = []
                groups['xhttp'][at].append(c)

        normal_dir = os.path.join(output_base_dir, 'normal')
        base64_dir = os.path.join(output_base_dir, 'base64')
        
        mix_content = hiddify_header("PSG | MIX") + '\n'.join(config_list)
        try:
            with open(os.path.join(normal_dir, 'mix'), 'w', encoding='utf-8') as f: f.write(mix_content)
            with open(os.path.join(base64_dir, 'mix'), 'w', encoding='utf-8') as f: f.write(base64.b64encode(mix_content.encode()).decode())
        except: pass

        for proto, addrs in groups.items():
            all_p = []
            for at, confs in addrs.items():
                fname = f"{proto}_{at}"
                merged = fakes + confs
                plain = hiddify_header(f"PSG | {proto.upper()} {at.upper()}") + '\n'.join(merged)
                b64 = base64.b64encode(plain.encode()).decode()
                try:
                    with open(os.path.join(normal_dir, fname), 'w', encoding='utf-8') as f: f.write(plain)
                    with open(os.path.join(base64_dir, fname), 'w', encoding='utf-8') as f: f.write(b64)
                except: pass
                all_p.extend(confs)
            
            if all_p:
                fname = proto
                merged = fakes + all_p
                plain = hiddify_header(f"PSG | {proto.upper()}") + '\n'.join(merged)
                b64 = base64.b64encode(plain.encode()).decode()
                try:
                    with open(os.path.join(normal_dir, fname), 'w', encoding='utf-8') as f: f.write(plain)
                    with open(os.path.join(base64_dir, fname), 'w', encoding='utf-8') as f: f.write(b64)
                except: pass

    write_groups(final_list, SUBS_DIR)
    write_groups(lite_list, LITE_DIR)

    # --- Write Location Based Configs ---
    print("   Generating Location-based subscriptions (including Cloudflare)...")
    LOC_NORMAL_DIR = os.path.join(LOCATIONS_SUBS_DIR, 'normal')
    LOC_BASE64_DIR = os.path.join(LOCATIONS_SUBS_DIR, 'base64')
    
    if os.path.exists(LOCATIONS_SUBS_DIR): shutil.rmtree(LOCATIONS_SUBS_DIR)
    os.makedirs(LOC_NORMAL_DIR, exist_ok=True)
    os.makedirs(LOC_BASE64_DIR, exist_ok=True)
    
    fakes = [create_fake_config(n) for n in FAKE_CONFIG_NAMES]
    
    for loc_code, confs in location_groups.items():
        if not confs: continue
        # Normalize code for filename (CF, US, DE, etc.)
        safe_code = re.sub(r'[^a-zA-Z0-9]', '', loc_code)
        if not safe_code: safe_code = "XX"
        
        merged = fakes + confs
        header_title = f"PSG | Cloudflare" if loc_code == 'CF' else f"PSG | Location {loc_code}"
        content = hiddify_header(header_title) + '\n'.join(merged)
        b64 = base64.b64encode(content.encode()).decode()
        
        try:
            with open(os.path.join(LOC_NORMAL_DIR, safe_code), 'w', encoding='utf-8') as f: f.write(content)
            with open(os.path.join(LOC_BASE64_DIR, safe_code), 'w', encoding='utf-8') as f: f.write(b64)
        except: pass
    # ------------------------------------

    print("   Generating Per-Channel subscriptions...")
    if os.path.exists(CHANNELS_SUBS_DIR): shutil.rmtree(CHANNELS_SUBS_DIR)
    os.makedirs(CHANNELS_SUBS_DIR, exist_ok=True)

    fakes = [create_fake_config(n) for n in FAKE_CONFIG_NAMES]
    for chan, confs in channel_groups.items():
        if not confs: continue
        merged = fakes + confs
        content = hiddify_header(f"PSG | @{chan}") + '\n'.join(merged)
        b64 = base64.b64encode(content.encode()).decode()
        try:
            with open(os.path.join(CHANNELS_SUBS_DIR, chan, 'normal'), 'w', encoding='utf-8') as f: f.write(content)
            with open(os.path.join(CHANNELS_SUBS_DIR, chan, 'base64'), 'w', encoding='utf-8') as f: f.write(b64)
        except: pass

    with open(CONFIG_FILE, 'w', encoding='utf-8') as f: f.write('\n'.join(final_list))
    os.makedirs(API_DIR, exist_ok=True)
    with open(API_OUTPUT_FILE, 'w', encoding='utf-8') as f: json.dump(api_list, f, indent=4, ensure_ascii=False)

    print(f"\n--- DONE! Main, Lite, Channel, and Location versions generated. ---")

if __name__ == "__main__":
    if os.name == 'nt': asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    asyncio.run(main())