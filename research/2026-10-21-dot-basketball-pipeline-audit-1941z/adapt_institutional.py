"""Adapter ONLY for audited Etalab-derived own-team lineup intervals."""
import csv,json,hashlib
from collections import defaultdict
from datetime import date
from pathlib import Path
p=Path(__file__).resolve().parent
source=p.parent/'institutional-derived'/'2015-16.csv'
group=defaultdict(list)
for order,r in enumerate(csv.DictReader(source.open())):
 parts=r['lineup'].split('_')
 ids=[s.rsplit(' - ',1)[1] for s in parts]
 gid=r['game_id'];date.fromisoformat(gid[:10])
 group[gid].append({'game_id':gid,'quarter':int(r['quarter']),'side':r['team'],'order':order,'seconds':int(r['time']),'lineup':ids,'pm':int(r['pm'])})
games=[];rejected=[]
for gid,rs in sorted(group.items()):
 quarters=sorted({r['quarter'] for r in rs})
 if len(quarters)<4 or quarters!=list(range(1,max(quarters)+1)):
  rejected.append({'game_id':gid,'quarters':quarters,'reason':'nonconsecutive source quarter labels; no repair inferred'});continue
 games.append({'game_id':gid,'date':gid[:10],'season':'2015-16','home_margin':sum(r['pm'] for r in rs if r['side']=='home'),'segments':rs})
data={'provenance':{'kind':'licensed_institutional_derived_NBA','source':'https://doi.org/10.57745/9NVFIQ','permission_basis':'Etalab2.0 grant for author-derived records, as preserved in acquisition review','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'lineup_order':'preserved source order; independently checked against author processing code','score_check':'internal complementarity only; external scoreboard not checked','raw_external_PBP_included':False},'games':games}
(p/'rejected-games.json').write_text(json.dumps({'source_games':len(group),'retained_games':len(games),'rejected':rejected},indent=2)+'\n')
(p/'institutional-adapted.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps({'games':len(games),'segments':sum(len(g['segments']) for g in games),'source_sha256':data['provenance']['source_sha256']}))
