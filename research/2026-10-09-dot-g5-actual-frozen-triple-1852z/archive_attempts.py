"""Losslessly bundle actual compiler attempts and reconstruct exact source revisions by hash."""
from pathlib import Path
import json,hashlib,difflib,itertools
R=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
records=[]
for p in sorted((R/'evidence').glob('*.json')):
 d=json.loads(p.read_text())
 if 'exit_code' not in d:continue
 out=(R/'evidence'/d['stdout']).read_bytes();err=(R/'evidence'/d['stderr']).read_bytes()
 records.append({'receipt_file':p.name,'receipt':d,'stdout_utf8':out.decode(),'stderr_utf8':err.decode(),'stdout_sha256':H(out),'stderr_sha256':H(err)})
wanted={r['receipt']['source_sha256'] for r in records};found={}
def add(b,path):
 h=H(b)
 if h in wanted:found[h]={'content_utf8':b.decode(),'bytes':len(b),'source_path':path}
for p in (R/'sources').rglob('*.lean'):
 rel=p.relative_to(R/'sources');b=p.read_bytes();add(b,str(rel))
 old=R/'review-v1/sources'/rel
 if not old.exists():continue
 a=old.read_bytes();add(a,str(rel));aa=a.decode().splitlines(keepends=True);bb=b.decode().splitlines(keepends=True)
 ops=difflib.SequenceMatcher(a=aa,b=bb,autojunk=False).get_opcodes();changes=sum(x[0]!='equal' for x in ops)
 assert changes<=18,(str(rel),changes)
 for mask in itertools.product([False,True],repeat=changes):
  it=iter(mask);lines=[]
  for tag,i,j,k,l in ops:
   lines.extend(bb[k:l] if tag!='equal' and next(it) else aa[i:j])
  add(''.join(lines).encode(),str(rel))
assert wanted<=found.keys(),sorted(wanted-found.keys())
(R/'evidence/COMPILER-ATTEMPTS.json').write_text(json.dumps({'scope':'All actual compiler invocations; failures are historical evidence, not certified proofs','attempt_count':len(records),'failed_count':sum(x['receipt']['exit_code']!=0 for x in records),'attempts':records},indent=2)+'\n')
(R/'evidence/SOURCE-REVISION-ARCHIVE.json').write_text(json.dumps({'scope':'Exact source revisions matching every recorded attempt SHA256; intermediate revisions reconstructed from frozen first/final bytes and authenticated against the recorded SHA256','revision_count':len(found),'revisions':found},indent=2)+'\n')
print('PASS',len(records),'attempts;',len(found),'exact source revisions; all hashes covered')
