import csv,io,json,zipfile,datetime as dt,collections
from pathlib import Path
import numpy as np
p=Path(__file__).parent
# PA,O,batting,SB,CS,pitchingouts,FIPnumerator,positionpartial
rec=collections.defaultdict(lambda:np.zeros(8)); audits=[]; ref=np.zeros(8)
pos={2:12.5,3:-12.5,4:2.5,5:2.5,6:7.5,7:-7.5,8:2.5,9:-7.5}
for year in range(2020,2026):
 z=zipfile.ZipFile(p/f'{year}csvs.zip'); got=collections.defaultdict(lambda:np.zeros(4)); expected=collections.defaultdict(lambda:np.zeros(4));seen=set()
 with z.open(f'{year}plays.csv') as f:
  for r in csv.DictReader(io.TextIOWrapper(f)):
   if r['gametype']!='regular':continue
   assert r['pbp']=='full'; key=(r['gid'],r['pn']);assert key not in seen;seen.add(key)
   d=dt.datetime.strptime(r['date'],'%Y%m%d').date().toordinal();b=r['batter'];pit=r['pitcher'];v=lambda k:int(r[k]); outs=v('outs_post')-v('outs_pre');assert 0<=outs<=3
   rec[(pit,d)][5]+=outs;got[(r['gid'],pit)][2]+=outs
   for k,rate in pos.items():
    fid=r[f'f{k}'];assert fid;rec[(fid,d)][7]+=outs*rate/4374
   if v('pa'):
    u=v('walk')-v('iw');O=v('single')+u+v('hbp');D=v('ab')+u+v('hbp')+v('sf');W=.699*u+.728*v('hbp')+.883*v('single')+1.238*v('double')+1.558*v('triple')+1.979*v('hr')
    rec[(b,d)][:3]+=[1,O,(W-.320*D)/1.185]
    N=13*v('hr')+3*(v('walk')+v('hbp'))-2*v('k');rec[(pit,d)][6]+=N;got[(r['gid'],pit)][3]+=N
   for j,end in [(1,'2'),(2,'3'),(3,'h')]:
    for kind,idx in [('sb',3),('cs',4)]:
     n=v(kind+end)
     if n:
      runner=r[f'br{j}_pre'];assert runner,(r['gid'],r['pn'],kind,end)
      rec[(runner,d)][idx]+=n;got[(r['gid'],runner)][idx-3]+=n
 # Player/game totals independent of resumed event dates.
 for table in ['batting','pitching']:
  with z.open(f'{year}{table}.csv') as f:
   for r in csv.DictReader(io.TextIOWrapper(f)):
    if r['gametype']!='regular' or r['stattype']!='value':continue
    key=(r['gid'],r['id'])
    if table=='batting':expected[key][:2]+=[int(r['b_sb']),int(r['b_cs'])]
    else:expected[key][2:]+=[int(r['p_ipouts']),13*int(r['p_hr'])+3*(int(r['p_w'])+int(r['p_hbp']))-2*int(r['p_k'])]
 dif=[{'key':list(k),'parsed':got[k].tolist(),'daily':expected[k].tolist()} for k in set(got)|set(expected) if not np.array_equal(got[k],expected[k])]
 audits.append({'year':year,'discrepancies':len(dif),'examples':dif[:20]});print(year,len(dif),flush=True)
(p/'component-reconciliation.json').write_text(json.dumps(audits,indent=2))
assert not any(a['discrepancies'] for a in audits),'Responsibility/reconstruction audit must resolve before fitting'
for (b,d),v in rec.items():
 if dt.date.fromordinal(d).year==2020:ref+=v
c=(.2*ref[3]-.435*ref[4])/ref[1];rho=ref[6]/ref[5]
players=collections.defaultdict(list)
for (b,d),v in rec.items():players[b].append([d,*v[:2],v[2],.2*v[3]-.435*v[4]-c*v[1],v[5],(rho*v[5]-v[6])/9,v[7]])

with (p/'next-round'/'daily-supported-local.json').open('w') as f:json.dump(dict(players),f)
print('daily cache saved; no new forecasts fitted')
