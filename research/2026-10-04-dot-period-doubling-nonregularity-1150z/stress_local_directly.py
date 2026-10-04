"""Independent finite falsification controls, not the universal certificate.
Uses explicit run-language expressions and literal word rewriting, no automaton import.
"""
from itertools import groupby,product
from functools import lru_cache
from pathlib import Path
import json

def expressions(bits):
 words={''};pos=0;cost=0
 for bit,gg in groupby(bits):
  L=len(list(gg))
  if bit=='1':
   c=str(pos%2);bar=str(1-pos%2);r=L//2
   choices={c*r} if L%2==0 else {c*h+bar*(r-h+2) for h in range(r+1)}
   words={a+b for a in words for b in choices};cost+=(L+1)//2
  pos+=L
 return words,cost
@lru_cache(None)
def reduce_once(s):
 out=set()
 for i in range(len(s)-1):
  if s[i]==s[i+1]:out.add(s[:i]+s[i+2:])
 for i in range(len(s)-2):
  if s[i]==s[i+1]==s[i+2]:out.add(s[:i]+str(1-int(s[i]))+s[i+3:])
 return out

def main():
 checked=targets=0
 for L,R in product((0,1,2,3,24,25),repeat=2):
  for gap in (0,2,2000):
   for x,y,z in product('01',repeat=3):
    src='1'*L+x+'1'+'0'*gap+y+z+'1'*R
    dst='1'*L+str(1-int(x))+'1'+'0'*gap+str(1-int(y))+str(1-int(z))+'1'*R
    ss,si=expressions(src);tt,ti=expressions(dst)
    if si!=ti+1:continue
    diff=len(next(iter(ss)))-len(next(iter(tt)))
    assert diff in (0,2,4)
    rr=ss
    for _ in range(diff//2):rr={t for s in rr for t in reduce_once(s)}
    assert tt<=rr,(L,R,gap,x,y,z,tt-rr)
    checked+=1;targets+=len(tt)
 receipt={'status':'PASS','local_instances':checked,'target_tilings':targets,'outer_run_lengths':[0,1,2,3,24,25],'middle_zero_gaps':[0,2,2000],'scope':'Finite direct falsification controls only; universal conclusion rests on the separate exhaustive transition-state closure.'}
 Path(__file__).with_name('DIRECT-LOCAL-STRESS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
if __name__=='__main__':main()
