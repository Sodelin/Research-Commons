import urllib.request,hashlib,json,zipfile
from pathlib import Path
p=Path(__file__).parent
# Bounded six-season panel, 20MB compressed cap each; no retries.
log=[]
for year in range(2020,2026):
 f=p/f'{year}csvs.zip';u=f'https://www.retrosheet.org/downloads/{year}/{year}csvs.zip'
 if not f.exists():
  with urllib.request.urlopen(u,timeout=40) as r:b=r.read(20000001)
  if len(b)>20000000:raise RuntimeError('archive cap exceeded')
  with f.open('xb') as out:out.write(b)
 with zipfile.ZipFile(f) as z:assert f'{year}plays.csv' in z.namelist()
 log.append(dict(year=year,url=u,bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
 (p/'source-manifest.json').write_text(json.dumps(log,indent=2));print(year,f.stat().st_size,flush=True)
