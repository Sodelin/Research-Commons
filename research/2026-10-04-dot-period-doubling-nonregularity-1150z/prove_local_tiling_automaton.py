"""Finite-state inclusion certificate for a UNIVERSAL local tiling lemma.
This is not a bounded word-length test. Acceptance requires exhaustion of every
reachable product state. A resource stop is explicitly not acceptance.
"""
from collections import deque
from functools import lru_cache
from itertools import groupby
from pathlib import Path
import hashlib,json,time

# Tiling state: used monomer in current 1-run, awaiting second domino bit.
# Output symbols encode domino colour c as c, monomer colour c as (1-c)^2.
def tiles(state,bit,colour):
 used,pending=state
 if not bit:
  return [] if pending else [((0,0),())]
 if pending:return [((used,0),(1-colour,))]
 out=[((used,1),())]
 if not used:out.append(((1,0),(1-colour,1-colour)))
 return out

# One length-reducing rewrite, or identity: aa -> empty; aaa -> complement(a).
# 0 before rewrite, 1 after; 2+c holds one c; 4+c holds two c's.
def redstep(st,c):
 if st==0:return [(0,(c,)),(2+c,())]
 if st==1:return [(1,(c,))]
 if st in (2,3):
  return [(1,()),(4+c,())] if c==st-2 else []
 return [(1,(1-c,))] if c==st-4 else []

def pipe(r1,r2,letters):
 states={(r1,r2,())}
 for c in letters:
  nxt=set()
  for q1,q2,out in states:
   for n1,emit in redstep(q1,c):
    if not emit:nxt.add((n1,q2,out))
    else:
     for n2,emit2 in redstep(q2,emit[0]):nxt.add((n1,n2,out+emit2))
  states=nxt
 return states

def match(buf,witness,target):
 # Positive side is witness ahead, negative is target ahead.
 side,s=buf;left=(s if side==1 else ())+witness;right=(s if side==-1 else ())+target
 m=min(len(left),len(right))
 if left[:m]!=right[:m]:return None
 left=left[m:];right=right[m:]
 rem=(1,left) if left else ((-1,right) if right else (0,()))
 return rem

# Witness state is ((used,pending), rewrite1, rewrite2, (ahead side,buffer)).
@lru_cache(None)
def witness_step(w,before,colour,target):
 T,r1,r2,buf=w;out=set()
 for T1,emit in tiles(T,before,colour):
  for r11,r21,emit2 in pipe(r1,r2,emit):
   B=match(buf,emit2,target)
   if B is not None:out.add((T1,r11,r21,B))
 return frozenset(out)

# A deterministic input state chooses a target tiling of the AFTER Gray word.
# The nondeterministic subset chooses a BEFORE tiling and up to two rewrites.
def consume(T,S,before,after,colour):
 out=[]
 for TT,emit in tiles(T,after,colour):
  SS=frozenset(v for w in S for v in witness_step(w,before,colour,emit))
  out.append((TT,SS))
 return out

def Iword(s):return sum((len(list(r))+1)//2 for b,r in groupby(s) if b=='1')
def eligible(l,r,g,x,y,z):
 pre='1'*l+str(x)+'1'+'0'*(2*g)+str(y)+str(z)+'1'*r
 post='1'*l+str(1-x)+'1'+'0'*(2*g)+str(1-y)+str(1-z)+'1'*r
 return Iword(pre)==Iword(post)+1

def final_witness(S):return any(not T[1] and r1 in (0,1) and r2 in (0,1) and buf==(0,()) for T,r1,r2,buf in S)

def run(limit=100000):
 # control: phase, left parity, right parity, positive even gap, x,y,z, position parity.
 c0=('L',0,0,0,-1,-1,-1,0);T0=(0,0)
 S0=frozenset([((0,0),0,0,(0,()))]);start=(c0,T0,S0)
 queue=deque([start]);seen={start};pred={};edges=0;ends=0;maxsubset=1;started=time.time()
 while queue:
  state=queue.popleft();c,T,S=state;phase,l,r,g,x,y,z,p=c
  maxsubset=max(maxsubset,len(S))
  if phase=='R' and not T[1] and eligible(l,r,g,x,y,z):
   ends+=1
   if not final_witness(S):
    trace=[];s=state
    while s!=start:s0,label=pred[s];trace.append(label);s=s0
    return {'status':'COUNTEREXAMPLE','trace':trace[::-1],'states':len(seen),'ends':ends}
  moves=[]
  if phase=='L':
   moves.append((('L',1-l,r,g,x,y,z,1-p),[(1,1,p)],'left-1'))
   for v in (0,1):moves.append((('F',l,r,g,v,y,z,1-p),[(v,1-v,p)],'x='+str(v)))
  elif phase=='F':moves.append((('G',l,r,g,x,y,z,1-p),[(1,1,p)],'fixed-1'))
  elif phase=='G':
   moves.append((('G',l,r,1,x,y,z,p),[(0,0,p),(0,0,1-p)],'gap-00'))
   for v in (0,1):moves.append((('Z',l,r,g,x,v,z,1-p),[(v,1-v,p)],'y='+str(v)))
  elif phase=='Z':
   for v in (0,1):moves.append((('R',l,r,g,x,y,v,1-p),[(v,1-v,p)],'z='+str(v)))
  else:moves.append((('R',l,1-r,g,x,y,z,1-p),[(1,1,p)],'right-1'))
  for cc,digits,label in moves:
   nexts=[(T,S)]
   for before,after,colour in digits:nexts=[v for TT,SS in nexts for v in consume(TT,SS,before,after,colour)]
   for TT,SS in nexts:
    edges+=1;new=(cc,TT,SS)
    if new not in seen:
     if len(seen)>=limit:return {'status':'RESOURCE_STOP_NOT_A_PROOF','states':len(seen),'remaining':len(queue),'max_subset':maxsubset}
     seen.add(new);pred[new]=(state,label);queue.append(new)
  if len(seen)%10000==0 and len(seen)>0:print('states',len(seen),'queue',len(queue),flush=True)
 receipt={'status':'PASS_EXHAUSTIVE_REACHABLE_STATE_CLOSURE','states':len(seen),'transitions':edges,'eligible_ends':ends,'max_subset':maxsubset,'seconds':time.time()-started,'maximum_observed_output_queue':max(len(w[3][1]) for _,_,S in seen for w in S),'scope':'All L,R>=0, all even middle zero gaps, all x,y,z, every target minimum tiling, when the independent-set drop is exactly one. Up to two abstract reductions. Exact unbounded-queue transition system; completeness is certified by finite reachable-state closure, not a word-length or output-queue cutoff.'}
 # Canonical transition-state inventory, no inferred bound from a test length.
 def canon(s):
  c,T,S=s;return [c,T,sorted(S,key=repr)]
 inventory=sorted((canon(s) for s in seen),key=repr)
 raw=json.dumps(inventory,separators=(',',':')).encode();receipt['state_inventory_sha256']=hashlib.sha256(raw).hexdigest()
 Path(__file__).with_name('LOCAL-TILING-AUTOMATON-STATES.json').write_bytes(raw)
 return receipt
if __name__=='__main__':
 receipt=run();print(receipt,flush=True)
 Path(__file__).with_name('LOCAL-TILING-AUTOMATON-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
