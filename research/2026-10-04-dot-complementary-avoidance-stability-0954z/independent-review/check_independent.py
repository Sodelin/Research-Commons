"""Independent exact controls using period-comparison runs, not substring minima."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent.parent
OUT=Path(__file__).resolve().parent

def ce(w):
    if not w:return Fraction(0)
    best=Fraction(1)
    for p in range(1,len(w)+1):
        run=0
        for i in range(len(w)-p):
            run=run+1 if w[i]==w[i+p] else 0
            best=max(best,Fraction(p+run,p))
    return best

def period(w,p):return w[p:]==w[:-p] if p<len(w) else p==len(w)
def morph(g,w):return ''.join(g[int(a)] for a in w)
def comp(w):return ''.join('1' if a=='0' else '0' for a in w)
def words(n):return (''.join(x) for x in product('01',repeat=n))
g=('010011001001','101100110110')
assert len(g[0])==len(g[1])==12 and g[1]==comp(g[0])
whole_periods=[min(p for p in range(1,13) if period(a,p)) for a in g]
assert whole_periods==[7,7]
assert g[0][0]!=g[1][0] and g[0][-1]!=g[1][-1]
assert all(g[a][:k]!=g[1-a][-k:] for a in (0,1) for k in range(6,13))
inputs=[w for n in range(1,5) for w in words(n) if ce(w)<3]
assert len(inputs)==22 and all(ce(w)<=2 for w in inputs)
rows=[{'input':w,'output':morph(g,w),'critical_exponent':str(ce(morph(g,w)))} for w in inputs]
assert all(Fraction(r['critical_exponent'])<=Fraction(8,3) for r in rows)
author=json.loads((ROOT/'SEED-AND-ENDPOINT-CERTIFICATE.json').read_text())
assert rows==[{k:r[k] for k in ('input','output','critical_exponent')} for r in author['seed_tests']]
for r in author['seed_tests']:
    a,b,p,v=r['attainment'];out=morph(g,r['input'])
    assert out[a:b]==v and period(v,p) and Fraction(b-a,p)==Fraction(r['critical_exponent'])

# Exhaust every normalized, end-marked length-five binary map. Obtain an
# actual forbidden output for an admissible word, without the proof's pruning.
rejections=[]
for u in words(4):
    a='0'+u
    for v in words(3):
        b='1'+v+comp(a[-1])
        witness=next((w for w in inputs if ce(morph((a,b),w))>=Fraction(8,3)),None)
        assert witness is not None
        rejections.append({'images':[a,b],'input':witness,'ce':str(ce(morph((a,b),witness)))})
assert len(rejections)==128
for r in author['endpoint_witnesses']:
    a=r['offset'];v=r['factor'];out=morph(r['images'],r['input'])
    assert ce(r['input'])<Fraction(8,3)
    assert out[a:a+len(v)]==v and period(v,3) and Fraction(len(v),3)>=Fraction(8,3)

# Exhaust the claimed small-period reduction independently.
roots=[]
for root in words(4):
    v=(root*3)[:11]
    if ce(v)<3:
        assert all(x not in v for x in ('010','101'))
        roots.append(root)
assert roots==['0011','0110','1001','1100']
markers={'00100','11011','01010','10101'}
marker_table=[]
for left in ('0010','1101'):
    for right in ('0110','1001'):
        w=left+right;hits=[(i-4,w[i:i+5]) for i in range(4) if w[i:i+5] in markers]
        assert len(hits)==1
        offset,marker=hits[0]
        assert offset==(-3 if marker in ('01010','10101') else -4)
        marker_table.append([left,right,offset,marker])

# Finite transcription control only; the all-odd-length fact is supplied by
# the inspected primary proof, not inferred from this finite list.
def tm(a,n):return ''.join(str(i.bit_count()%2) for i in range(a,a+n))
def admissible_endpoints(v):
    return ((v[:4] in ('0110','1001') and v[-4:] in ('0010','1101')) or
            (v[:4] in ('0100','1011') and v[-4:] in ('0110','1001')))
odd_controls=[]
for m in range(5,256,2):
    starts={1:[4],5:[0],7:[6],3:[m-5,m-4]}[m%8]
    good=[a for a in starts if admissible_endpoints(tm(a,m))]
    assert good,m
    odd_controls.append([m,good])

sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt={'status':'PASS_INDEPENDENT_EXACT_CONTROLS',
'proof_sha256':sha(ROOT/'STABILITY-THEOREM-CANDIDATE.md'),
'author_checker_sha256':sha(ROOT/'verify_seed_and_endpoint.py'),
'author_receipt_sha256':sha(ROOT/'SEED-AND-ENDPOINT-CERTIFICATE.json'),
'independent_checker_sha256':sha(Path(__file__)),
'whole_image_least_periods':whole_periods,'short_input_count':len(inputs),'seed_rows':rows,
'normalized_marked_length5_rejection_count':len(rejections),'length5_rejections':rejections,
'cubefree_period4_length11_roots':roots,'marker_table':marker_table,
'odd_endpoint_transcription_controls':odd_controls,
'limits':'Finite seed verifies a universal published sufficient criterion. Odd-length controls supplement the source proof. Uniform marker/exponent argument is reviewed by hand.'}
(OUT/'CONTROLS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('seed_rows','length5_rejections','odd_endpoint_transcription_controls')},indent=2))
