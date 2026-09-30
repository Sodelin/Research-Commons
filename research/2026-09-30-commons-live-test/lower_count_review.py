"""Finite corroboration of the written unbounded twin-count review; max19taxa."""
from fractions import Fraction as F
from pathlib import Path
import json
from twin_normalization_review import distance,ex,sunlet

rows=[]
for k in (2,3,5,8):
    r=2*k+1
    base,leaves=sunlet(r+1)
    net=ex.cherry_at(base,leaves[0],'twin-')
    cert=net.validate();labels=sorted(net.leaves);qs,_=ex.quartet_system(net)
    x,xp='twin-x','twin-y';u,z,v=leaves[1],leaves[k+1],leaves[r]
    for b in (F(-1),F(0),F(1,6),F(1,4),F(2,5)):
        d=distance(qs,labels,F(0),F(1),b,F(1))
        assert d[x,xp]==2*r
        assert d[x,u]==d[x,v]==4*r-2+b*(r-1)*(r-2)
        assert d[x,z]==d[x,u]+2*(1-b)*k*k
        assert d[u,v]==r*r+r-2
        assert d[u,z]==d[v,z]==3*k*k+3*k+4*b*k
        tuv=d[x,xp]+d[u,v]-d[x,u]-d[xp,v]
        tuz=d[x,xp]+d[u,z]-d[x,u]-d[xp,z]
        tvz=d[x,xp]+d[v,z]-d[x,v]-d[xp,z]
        assert tuv==4*(1-2*b)*k*k+(4*b-6)*k-2
        assert tuz==tvz==(1-6*b)*k*k+(8*b-9)*k-2
        rows.append({'k':k,'n':len(labels),'b':str(b),'Tuv':str(tuv),'Tuz=Tvz':str(tuz)})
    for a in (F(-1),F(0),F(99,100)):
        d=distance(qs,labels,F(1),F(1),a,F(1))
        tuv=d[x,xp]+d[u,v]-d[x,u]-d[xp,v]
        tuz=d[x,xp]+d[u,z]-d[x,u]-d[xp,z]
        tvz=d[x,xp]+d[v,z]-d[x,v]-d[xp,z]
        assert tuv==2*(1-a)*(r-1)*(r-2)>0
        assert tuz==tvz==2*(1-a)*k*(3*k-4)>0
        rows.append({'k':k,'n':len(labels),'c':'1','a':str(a),'Tuv':str(tuv),'Tuz=Tvz':str(tuz)})
report={'status':'PASS_DIRECT_SOURCE_TWIN_COUNT_FORMULAS','maximum_taxa':19,'graph_family':'odd ordinary-path sunlet with hybrid replaced by binarycherry','controls':rows,'scope':'Finite corroboration; all-size conclusion uses written count/class arguments, not polynomial interpolation'}
(Path(__file__).parent/'lower-count-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'controls':len(rows),'maximum_taxa':19}))
