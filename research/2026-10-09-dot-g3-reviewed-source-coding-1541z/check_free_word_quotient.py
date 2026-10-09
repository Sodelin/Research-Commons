"""Exact inherited-quotient arithmetic; not a full forest or G3 compiler."""
from fractions import Fraction as F
from math import comb
from itertools import product
from pathlib import Path
import json
q=p=F(1,2)
def b(n):
    return sum(F(comb(n,k))*p**k*(1-p)**(n-k)*q**(k*(k-1)//2+(n-k)*(n-k-1)//2) for k in range(n+1))
c=(1-q)**3/12
assert (b(2),b(4),c)==(F(3,4),F(81,512),F(1,96))
letters=[]
for lead,tail in [(F(1,4),F(1,2)),(F(1,2),F(1,4))]:
    b2=lead*b(2)*tail; b4=lead**6*b(4)*tail**6; C=lead**6*c*tail
    letters.append({'b2':b2,'b4':b4,'C':C,'F':C/b2,'chi':b4/b2})
assert letters[0]['F']==F(1,73728) and letters[1]['F']==F(1,2304)
assert letters[0]['chi']==letters[1]['chi']==F(27,4194304)
assert 0<letters[0]['chi']<F(1,2)
seen={}
for length in range(9):
    for word in product((0,1),repeat=length):
        chi,value=F(1),F(0)
        for i in word:
            value+=chi*letters[i]['F'];chi*=letters[i]['chi']
        key=(chi,value)
        assert key not in seen
        seen[key]=word
result={'scope':'Exact quotient values and bounded word comparison only','letters':[{k:str(v) for k,v in row.items()} for row in letters],'max_word_length':8,'distinct_words_checked':len(seen),'passed':True}
Path(__file__).with_name('FREE-WORD-QUOTIENT-CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
