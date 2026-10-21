"""Optional bounded public-source request. No credentials, retries or bulk download.
Check current source terms before use; this script grants no redistribution rights.
"""
import urllib.request,hashlib
from pathlib import Path
URL='https://baseballsavant.mlb.com/statcast_search/csv?all=true&type=details&player_type=batter&game_date_gt=2025-04-01&game_date_lt=2025-04-01'
p=Path(__file__).parent/'statcast-2025-04-01.csv'
if p.exists():
 print('Existing data preserved:',p.name);raise SystemExit(0)
with urllib.request.urlopen(URL,timeout=30) as r:
 b=r.read(8*1024*1024+1)
if len(b)>8*1024*1024:raise RuntimeError('8MiB acquisition cap exceeded; no file written')
if b'game_date' not in b[:4000]:raise RuntimeError('Response does not resemble expected CSV')
p.write_bytes(b);print(len(b),hashlib.sha256(b).hexdigest())
