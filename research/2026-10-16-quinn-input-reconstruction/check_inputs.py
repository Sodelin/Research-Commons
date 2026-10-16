"""Read-only checks of preserved small inputs; no network or viewshed execution."""
import hashlib,json,sqlite3,subprocess,tempfile,zipfile
from pathlib import Path
p=Path(__file__).resolve().parent/'evidence'
zpath=p/'2019_TrafficSections.zip'
assert hashlib.sha256(zpath.read_bytes()).hexdigest()=='f16747ac4aa85cd7b75cfceb6c352ae30c37213ded1518a37284a05f72a7e642'
with tempfile.TemporaryDirectory() as tmp:
 root=Path(tmp)
 with zipfile.ZipFile(zpath) as z:
  assert z.testzip() is None
  for n in z.namelist():assert (root/n).resolve().is_relative_to(root)
  z.extractall(root)
 base=['ogrinfo','-ro','-q',str(root/'2019TrafficSections.gdb'),'-dialect','SQLite','-sql']
 sql='SELECT COUNT(*) AS n, COUNT(DISTINCT StateRouteNumber) AS route_numbers, COUNT(DISTINCT RouteIdentifier) AS route_ids, SUM(CASE WHEN AADT IS NULL THEN 1 ELSE 0 END) AS null_aadt, MIN(AADT) AS min_aadt, MAX(AADT) AS max_aadt, SUM(SHAPE_Length)*0.304800609601219/1000 AS length_km FROM TrafficSections2019'
 r=subprocess.run(base+[sql],check=True,capture_output=True,text=True).stdout
 for s in ['n (Integer) = 4913','route_numbers (Integer) = 188','route_ids (Integer) = 251','null_aadt (Integer) = 0','11362.178']:assert s in r,s
 print(r)
 print(subprocess.run(base+['SELECT RelatedRouteType, COUNT(*) AS n FROM TrafficSections2019 GROUP BY RelatedRouteType'],check=True,capture_output=True,text=True).stdout)
with sqlite3.connect('file:'+str(p/'USGS_1_n48w123_20200107.gpkg')+'?mode=ro',uri=True) as c:
 assert c.execute('SELECT count(*) FROM n48w123').fetchone()[0]==92
 assert c.execute('SELECT srs_id FROM gpkg_contents').fetchone()[0]==4269
 print('USGS spatial metadata: 92 provenance polygons; EPSG:4269; no elevation raster downloaded')
a=json.loads((p/'tnm-wa-products.json').read_text())['items']+json.loads((p/'tnm-wa-products-page2.json').read_text())['items']
assert len(a)==178 and len(set(x['sourceId'] for x in a))==178
assert json.loads((p/'wsdot-2019-count.json').read_text())['count']==4913
print('Checks passed. These are candidate-input checks, not identification of Quinn historical outputs.')
