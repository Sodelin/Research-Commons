"""Exact finite certificates; universal gate is the cited morphism theorem."""
import json
from fractions import Fraction
from itertools import product
from pathlib import Path

def period(w,p):
    return all(w[i]==w[i+p] for i in range(len(w)-p))

def critical(w):
    best=Fraction(0); witness=None
    for i in range(len(w)):
        for j in range(i+1,len(w)+1):
            z=w[i:j]
            p=next(p for p in range(1,len(z)+1) if period(z,p))
            value=Fraction(len(z),p)
            if value>best:best=value;witness=[i,j,p,z]
    return best,witness

def complement(w):return w.translate(str.maketrans('01','10'))
def image(images,w):return ''.join(images[int(a)] for a in w)
images=['010011001001','101100110110']
assert images[1]==complement(images[0])
full_periods=[next(p for p in range(1,13) if period(w,p)) for w in images]
assert full_periods==[7,7]
assert images[0][0]!=images[1][0] and images[0][-1]!=images[1][-1]
long_overlaps=[(a,l) for a in [0,1] for l in range(6,13) if images[a][:l]==images[1-a][-l:]]
assert not long_overlaps
rows=[];input_words=[]
for length in range(1,5):
    for bits in product('01',repeat=length):
        w=''.join(bits); ci,_=critical(w)
        if ci>=3:continue
        assert ci<=2
        input_words.append(w)
        out=image(images,w);co,wi=critical(out)
        assert co<=Fraction(8,3)
        rows.append({'input':w,'output':out,'critical_exponent':str(co),'attainment':wi})
assert len(rows)==22
endpoint=[]
for a,b,x,offset,z in [
 ('01001','10010','10',0,'100100100'),
 ('01101','10110','01',0,'011011011'),
 ('01001','10110','011',3,'01101101'),
 ('01101','10010','001',4,'10110110')]:
    out=image([a,b],x)
    assert critical(x)[0]<Fraction(8,3)
    assert out[offset:offset+len(z)]==z and period(z,3)
    assert Fraction(len(z),3)>=Fraction(8,3)
    endpoint.append({'images':[a,b],'input':x,'offset':offset,'factor':z,'period':3})
markers={'00100','11011','01010','10101'}
marker_rows=[]
for suffix in ['0010','1101']:
 for prefix in ['0110','1001']:
    s=suffix+prefix
    occ=[(i-4,s[i:i+5]) for i in range(4) if s[i:i+5] in markers]
    assert len(occ)==1
    off,m=occ[0]
    assert off==(-3 if m in ['01010','10101'] else -4)
    marker_rows.append({'suffix':suffix,'prefix':prefix,'offset':off,'marker':m})
# Independent finite exhaustion of all normalized marked length-five maps.
rejected=0
for tail0 in map(''.join,product('01',repeat=4)):
 a='0'+tail0
 for middle1 in map(''.join,product('01',repeat=3)):
    b='1'+middle1+complement(a[-1])
    assert any(critical(image([a,b],w))[0]>=Fraction(8,3) for w in input_words)
    rejected+=1
assert rejected==128
result={'status':'PASS','full_image_least_periods':full_periods,'opposite_image_long_overlaps':long_overlaps,'seed_tests':rows,'endpoint_witnesses':endpoint,'marker_table':marker_rows,'normalized_marked_length5_maps_rejected':rejected,'limits':'Exact fixed-seed and endpoint controls. Universal statement relies on hand proof and the cited Kobayashi sufficient criterion.'}
Path(__file__).with_name('SEED-AND-ENDPOINT-CERTIFICATE.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(rows),'seed input tests;',rejected,'marked length-five maps;',len(marker_rows),'marker cases')
