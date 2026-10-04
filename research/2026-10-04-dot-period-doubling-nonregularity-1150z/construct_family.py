"""Explicit certificates for the uniform separation-family constructions.
No nonautomaticity or odd-case optimality is inferred from these controls.
"""
import json
from pathlib import Path

def gray_decode(g):
 n=0;p=0
 for c in g:p^=c;n=(n<<1)|p
 return n

def pal(a,b):
 while b-a>2:
  if (b-a)%2==0:return False
  a//=2;b//=2
 if b-a<=1:return True
 h=a//2+1
 return ((h&-h).bit_length()-1)%2==1

def ind(n):
 g=n^(n>>1);k=0
 while g:
  if g&1:k+=1;g>>=2
  else:g>>=1
 return k

class PathCertificate:
 def __init__(self,a,b):
  self.a,self.b=a,b;self.g=[int(c) for c in '1'*(2*a)+'011'*b+'0'];self.n=gray_decode(self.g)
  self.initial=self.n;self.path=[self.n];self.marked=False
 def step(self,m):
  n=self.n
  assert 0<=m<n and pal(m,n),(n,m,'invalid palindrome')
  self.marked |= n-m==1 and ((n&-n).bit_length()-1)%2==1
  self.n=m;self.path.append(m)
  self.g=[int(c) for c in format(m^(m>>1),'0'+str(len(self.g))+'b')]
 def toggle(self,*ps):
  g=self.g[:]
  for p in ps:g[p]^=1
  self.step(gray_decode(g))
 def B(self,p,q):self.toggle(p,q,q+1)
 def D(self,p,q):self.B(p,q);self.toggle(p+1)
 def R(self,p):self.B(p+2,p+4);self.B(p,p+2)
 def E(self,A,q):
  p=2*A-4;self.B(p+2,q);self.B(p,p+2);self.D(p+1,q+3)
 def clear_prefix(self,A):
  assert A%2==0
  for p in range(0,2*A,4):self.D(p,p+2)
 def initial_odd_gap(self,a,b):
  p=2*a-6;q=2*a+1;self.R(p);self.D(p+1,q)
  return a-3,b-1,q+3
 def even(self,a,b):
  assert a>b and (a-b)%2==0
  if not b:self.clear_prefix(a);return
  A,B,q=self.initial_odd_gap(a,b)
  while B>=2:self.E(A,q);A-=2;B-=2;q+=6
  if B:self.D(2*A-2,q);A-=1
  self.clear_prefix(A)
 def odd_upper(self,a,b):
  assert a>b and (a-b)%2==1
  self.step(self.n-1);self.toggle(len(self.g)-2)
  if b:self.even(a,b-1)
  else:self.clear_prefix(a-1)
 def power_finish(self):
  assert self.n and self.n&(self.n-1)==0 and (self.n.bit_length()-1)%2==1
  self.step(self.n-1);self.step(0)
 def marked_odd(self,a,b):
  assert a-b>=3 and (a-b)%2==1
  if not b:
   for p in range(0,2*(a-3),4):self.D(p,p+2)
   self.R(2*a-6);self.power_finish();return
  A,B,q=self.initial_odd_gap(a,b)
  while B>=2:self.E(A,q);A-=2;B-=2;q+=6
  if not B:
   assert b%2==1 and A%2==1
   self.step(self.n-1);self.toggle(2*A-1);self.clear_prefix(A-1)
  else:
   assert b%2==0 and A%2==0
   for p in range(0,2*(A-2),4):self.D(p,p+2)
   p=2*A-4;self.B(p+2,q);self.B(p,p+2);self.power_finish()

def controls():
 records=[];edges=0
 for a in range(1,41):
  for b in range(a):
   cases=['even'] if (a-b)%2==0 else ['odd_upper']+(['marked_odd'] if a-b>=3 else [])
   for case in cases:
    c=PathCertificate(a,b);getattr(c,case)(a,b)
    expected=a+b+(case!='even')
    assert c.n==0 and len(c.path)-1==expected,(a,b,case,len(c.path)-1,expected)
    assert case!='marked_odd' or c.marked
    assert ind(c.initial)==a+b
    if case=='even':assert expected==ind(c.initial)
    edges+=expected
    records.append({'a':a,'b':b,'construction':case,'pieces':expected,'singleton_one':c.marked,'input_bits':c.initial.bit_length()})
 receipt={'status':'PASS','cases':len(records),'exact_palindrome_edges':edges,'max_input_bits':max(r['input_bits'] for r in records),'scope':'Bounded independent edge-predicate controls of explicit uniform constructions; not a D/S or nonautomaticity certificate','records':records}
 Path(__file__).with_name('CONSTRUCTION-CONTROLS.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print({k:v for k,v in receipt.items() if k!='records'})
if __name__=='__main__':controls()
