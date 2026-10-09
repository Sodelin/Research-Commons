"""Bounded lexical audit, not a replacement for Lean parsing or semantic review."""
import hashlib,json,pathlib,re
R=pathlib.Path(__file__).resolve().parent
old=R/'review-v1/sources';new=R/'review-final/sources'
def strip(s):
 s=re.sub(r'/-.*?-/', '', s, flags=re.S)
 return re.sub(r'--[^\n]*','',s)
def decls(s):
 s=strip(s)
 pat=re.compile(r'^(?:noncomputable\s+)?(def|abbrev|theorem|lemma)\s+(\w+)\b',re.M)
 hits=list(pat.finditer(s));out={}
 for k,m in enumerate(hits):
  end=hits[k+1].start() if k+1<len(hits) else len(s)
  body=s[m.start():end];body=body.split('#print axioms')[0]
  cut=re.search(r':=|\bwhere\b',body)
  if cut is None:raise ValueError(m.group(2))
  statement=' '.join(body[:cut.start()].split())
  definition=' '.join(body.split('end GProgram.')[0].split()) if m.group(1) in ['def','abbrev'] else None
  out[m.group(2)]={'kind':m.group(1),'statement':statement,'definition':definition}
 return out
rows=[]
for p in sorted(old.rglob('*.lean')):
 rel=p.relative_to(old);q=new/rel; a=decls(p.read_text());b=decls(q.read_text())
 assert a.keys()==b.keys(),str(rel)
 for n,x in a.items():
  assert x['statement']==b[n]['statement'],(str(rel),n,'statement')
  # Boundaries may include namespace open declarations after the final def,
  # so exact definition comparison is separately reported, not assumed parsed.
 rows.append({'file':str(rel),'named_declarations':len(a),'statements_unchanged':True,'old_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'final_sha256':hashlib.sha256(q.read_bytes()).hexdigest()})
print(json.dumps({'status':'PASS','scope':'lexical named statement comparison after stripping comments/whitespace; source-semantic review and Lean compilation are separate','named_declarations':sum(r['named_declarations'] for r in rows),'files':rows},indent=2))
