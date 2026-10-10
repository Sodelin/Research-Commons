#!/usr/bin/env python3
"""Lossless DAG integrity, exact census agreement, and disclosed runtime companions.
No mathematical proof or runtime-behavior equivalence is asserted by this parser.
"""
import argparse,hashlib,json
from pathlib import Path
ALLOWED={'propext','Classical.choice','Quot.sound'}
CHILDREN={'app':(1,2),'lam':(2,3),'forallE':(2,3),'letE':(2,3,4),'mdata':(2,),'proj':(3,)}
KINDS={'bvar','fvar','mvar','sort','const','app','lam','forallE','letE','natVal','strVal','mdata','proj'}
def digest(x):return hashlib.sha256(json.dumps(x,ensure_ascii=False,separators=(',',':'),sort_keys=True).encode()).hexdigest()
def check_name(n):
 assert isinstance(n,list)and n
 if n[0]=='anonymous':assert len(n)==1;return
 assert n[0]in ('str','num')and len(n)==3
 check_name(n[1]);assert isinstance(n[2],str)if n[0]=='str'else isinstance(n[2],int)and not isinstance(n[2],bool)and n[2]>=0

def scan(lines,expected,census=None,classification=None):
 allowed=set(classification['allowed_G2_partial_names'])if classification else set()
 context_partial=set(classification['all_context_partial_names'])if classification else set()
 assert allowed<=context_partial
 structured_to_display={};display_to_structured={}
 def paired(n,s):
  check_name(n);assert isinstance(s,str)and s
  k=json.dumps(n,ensure_ascii=False,separators=(',',':'))
  assert structured_to_display.get(k,s)==s,('Inconsistent display for structured Name',n,s)
  assert display_to_structured.get(s,k)==k,('Noninjective display for distinct structured Names',s)
  structured_to_display[k]=s;display_to_structured[s]=k
  return s
 def paired_array(ns,ss):
  assert isinstance(ns,list)and isinstance(ss,list)and len(ns)==len(ss)
  return [paired(n,s)for n,s in zip(ns,ss)]
 headers=[];done=[];current=None;wanted=0;count=0;decls=[];seen=set();seen_partial=set()
 for line in lines:
  line=line.strip()
  if not line.startswith('{'):continue
  try:r=json.loads(line)
  except json.JSONDecodeError:continue
  if 'record'not in r:continue
  if r['record']=='header':
   assert current is None,'Unclosed prior module';assert r['schema']=='complete-module-dag-v1'
   current=paired(r['module'],r['module_display']);assert current not in headers and current in expected,current
   headers.append(current);wanted=r['declaration_count'];assert wanted>0;count=0
  elif r['record']=='declaration':
   assert current is not None
   n=paired(r['name'],r['name_display']);assert n not in seen,n;seen.add(n)
   assert r['kind']!='axiom','Owned axiom '+n
   assert r['unsafe']is False,('Unsafe declaration',n)
   assert r['partial']is (n in allowed),('Unclassified or missing partial companion',n)
   if r['partial']:
    assert r['kind']=='definition';seen_partial.add(n)
   ax=set(paired_array(r['axioms'],r['axioms_display']));assert ax<=ALLOWED,(n,ax)
   tr=paired_array(r['type_references'],r['type_references_display']);br=paired_array(r['body_references'],r['body_references_display'])
   assert not ((set(tr)|set(br))&context_partial-{n}),('Non-self logical reference to partial companion',n)
   assert r['kind']not in ('theorem','definition','opaque')or r['body_root']is not None,n
   hashes=[]
   for i,node in enumerate(r['nodes']):
    assert isinstance(node,list)and node and node[0]in KINDS,(n,i)
    assert node[0]not in ('fvar','mvar'),(n,'nonclosed expression')
    structural=list(node)
    for j in CHILDREN.get(node[0],()):
     q=node[j];assert isinstance(q,int)and not isinstance(q,bool)and 0<=q<i,(n,i,q)
     structural[j]={'child_structural_sha256':hashes[q]}
    hashes.append(digest(structural))
   ti=r['type_root'];bi=r['body_root'];assert isinstance(ti,int)and not isinstance(ti,bool)and 0<=ti<len(hashes)
   assert bi is None or (isinstance(bi,int)and not isinstance(bi,bool)and 0<=bi<len(hashes))
   decls.append({'module':current,'name':n,'structured_name':r['name'],'kind':r['kind'],'unsafe':r['unsafe'],'partial':r['partial'],'classification':'generated_runtime_companion'if r['partial']else 'ordinary_kernel_declaration','type_structural_sha256':hashes[ti],'body_structural_sha256':hashes[bi]if bi is not None else None,'level_parameters':r['level_parameters'],'type_references':sorted(tr),'body_references':sorted(br),'axioms':sorted(ax),'lossless_record_sha256':digest(r),'expression_node_count':len(hashes)})
   count+=1
  elif r['record']=='footer':
   assert current is not None and r['status']=='COMPLETE';assert count==wanted==r['declaration_count'],(current,count,wanted,r['declaration_count'])
   done.append({'module':current,'declarations':count});current=None
  else:raise AssertionError('Unknown audit record '+r['record'])
 assert current is None,'Incomplete last module';assert headers==expected,('Selected scope/order mismatch',headers,expected)
 assert seen_partial==allowed,('Partial companion scope mismatch',seen_partial,allowed)
 if census is not None:
  wide={r['name']:r for r in census['declarations']if r['module']in expected};assert set(wide)==seen,('Declaration census mismatch',sorted(set(wide)-seen),sorted(seen-set(wide)))
  for r in decls:
   w=wide[r['name']]
   for k in ('kind','module'):assert r[k]==w[k],(r['name'],k)
   for k in ('type_references','body_references','axioms'):assert r[k]==sorted(w[k]),(r['name'],k)
 return {'status':'COMPLETE_CURRENT_SOURCE_DAG_AND_SCOPE_CHECK','selected_modules':expected,'module_count':len(expected),'declaration_count':len(decls),'theorem_count':sum(r['kind']=='theorem'for r in decls),'owned_axioms':[],'nonstandard_axioms':[],'missing_modules':[],'unsafe_count':0,'partial_companion_count':len(seen_partial),'partial_companion_names':sorted(seen_partial),'non_self_logical_partial_references':[],'name_display_bijection_entries':len(display_to_structured),'modules':done,'census_comparison':'EXACT_MATCH'if census is not None else 'NOT_SUPPLIED','comparison_boundary':'Full structured names/term data retained. Lean display strings compare exactly to the prior census with a checked display/structured bijection. Classified partial runtime companions are retained; their executable behavior is not certified. No historical missing-body or second-kernel equivalence is asserted.','declarations':decls}
def main():
 a=argparse.ArgumentParser();a.add_argument('stdout');a.add_argument('--modules',required=True);a.add_argument('--census',required=True);a.add_argument('--classification',required=True);a.add_argument('--output',required=True);args=a.parse_args();p=Path(args.stdout);mods=json.loads(Path(args.modules).read_text());cp=Path(args.census);c=json.loads(cp.read_text());clp=Path(args.classification);cl=json.loads(clp.read_text())
 assert hashlib.sha256(cp.read_bytes()).hexdigest()==cl['passed_census_sha256']
 with p.open()as f:r=scan(f,mods,c,cl)
 r.update(stdout_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),module_list_sha256=hashlib.sha256(Path(args.modules).read_bytes()).hexdigest(),census_sha256=hashlib.sha256(cp.read_bytes()).hexdigest(),classification_sha256=hashlib.sha256(clp.read_bytes()).hexdigest())
 Path(args.output).write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n');print(json.dumps({k:r[k]for k in ['status','module_count','declaration_count','theorem_count','partial_companion_count','name_display_bijection_entries','census_comparison']}))
if __name__=='__main__':main()
