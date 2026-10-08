"""Authenticate saved exact primitive evidence without running its code/oracle."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import subprocess,hashlib,json
C='d90bca775931e3db6f65193b54a4be603427d2a4'
P='research/2026-10-07-cloud-gmp-interval-sol-2354z/'
O=Path('research/2026-10-07-cloud-independent-auditor-1616z')
def raw(q): return subprocess.check_output(['git','show',C+':'+q])
def read(q): return raw(P+q)
sha=lambda b:hashlib.sha256(b).hexdigest()
manifestb=read('manifest.json'); m=json.loads(manifestb); checks=[]
for r in m['artifacts']:
 b=raw(r['path']); assert sha(b)==r['sha256'] and len(b)==r['bytes']; checks.append({**r,'immutable_Git_byte_identity':True})
assert len(checks)==10
ref=read('reference/certified_forward.py'); original=raw(m['authoritative_reference']['path']); assert ref==original and len(ref)==6604 and sha(ref)==m['authoritative_reference']['sha256']
r=json.loads(read('results/differential.json')); build=json.loads(read('results/build.json'))
inputs=read('results/differential-inputs.txt'); outputs=read('results/probe-output.jsonl'); lines=inputs.decode().splitlines(); records=[json.loads(v) for v in outputs.splitlines()]
assert len(lines)==len(records)==r['case_count']==2414
assert sha(inputs)==r['input_sha256'] and sha(outputs)==r['cpp_output_sha256'] and dict(Counter(v['status'] for v in records))==r['exact_status_counts']
assert r['status']=='PASS' and r['failure_count']==0 and not r['failures'] and r['cpp_returncode']==0 and r['primitive_comparison_cases']==2408 and r['separate_parser_contract_cases']==6
assert build['returncode']==0 and not build['stderr'] and build['binary_sha256']==m['build']['binary_sha256']
shape_checks=0; arithmetic_records=0; exponential_shapes=0; parser_refusals=0; exp_refusals=0
for line,v in zip(lines,records):
 t=line.split(); op=t[0]
 if v.get('phase')=='parser': parser_refusals+=1; continue
 if op=='exp':
  kind_x,x=t[1].split(':',1); kind_b,b=t[2].split(':',1)
  if kind_x not in ('i','q'):
   assert v=={'status':'DomainError','message':'exact rational exponential input required','phase':'primitive'};exp_refusals+=1;continue
  x=F(x)
  if x<0 or kind_b!='i' or not 8<=int(b)<=192:
   assert v=={'status':'DomainError','message':'exponential domain/precision','phase':'primitive'};exp_refusals+=1;continue
  assert v['status']=='ok' and v['kind']=='interval'
  lo,hi,width=map(F,(v['lower'],v['upper'],v['width']));bound=F(1,1<<int(b));assert 0<=lo<=hi<=1 and width==hi-lo<=bound
  if x==0:assert lo==hi==1
  if x>=int(b):assert lo==0 and hi==bound
  exponential_shapes+=1;continue
 # Exact interval arithmetic comparison uses saved input rationals only.
 if op=='point': lo=hi=F(t[1])
 else:
  a,b=map(F,t[1:3])
  if a>b:
   assert v=={'status':'ValueError','message':'reversed interval','phase':'primitive'};continue
  if op=='width':assert v=={'status':'ok','kind':'rational','value':str(b-a)};arithmetic_records+=1;continue
  if op=='contains':assert v=={'status':'ok','kind':'boolean','value':a<=F(t[3])<=b};arithmetic_records+=1;continue
  if op in ('add','sub','mul','intersects'):
   c,d=map(F,t[3:5]);assert c<=d
   if op=='intersects':assert v=={'status':'ok','kind':'boolean','value':max(a,c)<=min(b,d)};arithmetic_records+=1;continue
   if op=='add':lo,hi=a+c,b+d
   elif op=='sub':lo,hi=a-d,b-c
   else:xs=[a*c,a*d,b*c,b*d];lo,hi=min(xs),max(xs)
  elif op=='neg':lo,hi=-b,-a
  elif op=='unit':
   lo,hi=max(F(0),a),min(F(1),b)
   if lo>hi:assert v=={'status':'ValueError','message':'reversed interval','phase':'primitive'};continue
  elif op=='dyadic':
   bits=int(t[3])
   if bits<0:assert v=={'status':'ValueError','message':'negative shift count','phase':'primitive'};continue
   scale=1<<bits; lo=F((a*scale).numerator//(a*scale).denominator,scale);hi=F(-((-b*scale).numerator//(-b*scale).denominator),scale)
  else:
   c=F(t[3])
   if op=='div':
    if c==0:assert v=={'status':'ZeroDivisionError','message':'','phase':'primitive'};continue
    lo,hi=min(a/c,b/c),max(a/c,b/c)
   elif op in ('add_scalar','radd'):lo,hi=a+c,b+c
   elif op=='sub_scalar':lo,hi=a-c,b-c
   elif op=='rsub':lo,hi=c-b,c-a
   elif op in ('mul_scalar','rmul'):lo,hi=min(a*c,b*c),max(a*c,b*c)
   else:raise AssertionError(op)
 assert v=={'status':'ok','kind':'interval','lower':str(lo),'upper':str(hi),'width':str(hi-lo)};arithmetic_records+=1;shape_checks+=1
assert parser_refusals==6 and exp_refusals==48
subprocess.run(['git','merge-base','--is-ancestor',C,'origin/main'],check=True)
out={'status':'CODE/SOURCE ACCEPT; immutable saved author evidence correspondence PASS','author_commit':C,'manifest_sha256':sha(manifestb),'artifacts':checks,'frozen_reference_equals_immutable_original':True,'record_count':len(records),'actual_author_primitive_comparison_cases':2408,'actual_author_separate_parser_cases':6,'actual_author_exact_property_assertions':r['exact_property_assertions'],'reviewer_static_complete_interval_arithmetic_records':arithmetic_records,'reviewer_static_successful_exponential_shape_checks':exponential_shapes,'reviewer_static_exp_type_domain_refusals':exp_refusals,'reviewer_static_parser_phase_count':parser_refusals,'input_sha256':sha(inputs),'output_sha256':sha(outputs),'build_receipt':build,'differential_receipt':r,'probe_compiler_harness_or_Python_reference_execution_by_reviewer':False,'author_execution_binding_limit':'Harness does not hash launched executable at call; separate author build record pins binary. No independent source-to-binary attestation or replay.','scope':'Exact rational interval and exp_neg admitted typed primitive port only; full evaluator/inverse/statistical/width backend remains separate.'}
(O/'gmp-interval-port-source-receipt-authentication.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('artifacts','build_receipt','differential_receipt')},indent=2))
