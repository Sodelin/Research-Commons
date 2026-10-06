#!/usr/bin/env python3
"""Validate complete streamed raw audits; compare full DAGs without tree expansion."""
import json,sys,pathlib,hashlib
ORIGINAL='G2LiteralMarkedClockTrace';GUARD=ORIGINAL+'KernelGuard'
def integer(x):assert isinstance(x,int) and not isinstance(x,bool) and x>=0;return x
def has_hygiene_marker(x):
 if x==['anonymous']:return False
 return (x[0]=='str' and x[2]=='_@') or has_hygiene_marker(x[1])
def name(x):
 assert isinstance(x,list) and x
 if x[0]=='anonymous':assert len(x)==1;return x
 assert x[0] in ('str','num') and len(x)==3
 p=name(x[1]);v=x[2]
 if x[0]=='str':assert isinstance(v,str)
 else:integer(v)
 if x[0]=='str' and v==GUARD and (p==['str',['anonymous'],'_private'] or has_hygiene_marker(p)):v=ORIGINAL
 return [x[0],p,v]
def freeze(x):return json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False)
def level(x):
 assert isinstance(x,list) and x
 tag=x[0]
 if tag=='zero':assert len(x)==1;return x
 if tag=='succ':assert len(x)==2;return [tag,level(x[1])]
 if tag in ('max','imax'):assert len(x)==3;return [tag,level(x[1]),level(x[2])]
 if tag=='param':assert len(x)==2;return [tag,name(x[1])]
 raise AssertionError('Unexpected or unresolved universe '+repr(x))
def substring(x):
 assert len(x)==3 and isinstance(x[0],str);integer(x[1]);integer(x[2]);return x
def info(x):
 if x[0]=='none':assert len(x)==1;return x
 if x[0]=='synthetic':assert len(x)==4;integer(x[1]);integer(x[2]);assert isinstance(x[3],bool);return x
 assert x[0]=='original' and len(x)==5;substring(x[1]);integer(x[2]);substring(x[3]);integer(x[4]);return x
def syntax(x):
 tag=x[0]
 if tag=='missing':assert len(x)==1;return x
 if tag=='node':assert len(x)==4;return [tag,info(x[1]),name(x[2]),[syntax(y) for y in x[3]]]
 if tag=='atom':assert len(x)==3 and isinstance(x[2],str);return [tag,info(x[1]),x[2]]
 assert tag=='ident' and len(x)==5
 pre=[]
 for p in x[4]:
  if p[0]=='namespace':assert len(p)==2;pre.append([p[0],name(p[1])])
  else:assert p[0]=='decl' and len(p)==3 and all(isinstance(v,str) for v in p[2]);pre.append([p[0],name(p[1]),p[2]])
 return [tag,info(x[1]),substring(x[2]),name(x[3]),pre]
def metadata(xs):
 out=[]
 for n,v in xs:
  assert len(v)==2;tag,w=v
  if tag=='name':w=name(w)
  elif tag=='syntax':w=syntax(w)
  elif tag=='string':assert isinstance(w,str)
  elif tag=='bool':assert isinstance(w,bool)
  elif tag=='nat':integer(w)
  elif tag=='int':assert isinstance(w,int) and not isinstance(w,bool)
  else:raise AssertionError('Unknown metadata constructor')
  out.append([name(n),[tag,w]])
 return out
REFS={'app':[1,2],'lam':[2,3],'forallE':[2,3],'letE':[2,3,4],'mdata':[2],'proj':[3]}
def normalize_node(x):
 assert isinstance(x,list) and x;tag=x[0];y=list(x)
 if tag in ('bvar','natVal'):assert len(x)==2;integer(x[1])
 elif tag=='strVal':assert len(x)==2 and isinstance(x[1],str)
 elif tag in ('fvar','mvar'):raise AssertionError('Nonclosed expression')
 elif tag=='sort':assert len(x)==2;y[1]=level(x[1])
 elif tag=='const':assert len(x)==3;y[1]=name(x[1]);y[2]=[level(u) for u in x[2]]
 elif tag=='app':assert len(x)==3
 elif tag in ('lam','forallE'):
  assert len(x)==5 and x[4] in ('default','implicit','strictImplicit','instImplicit');y[1]=name(x[1])
 elif tag=='letE':assert len(x)==6 and isinstance(x[5],bool);y[1]=name(x[1])
 elif tag=='mdata':assert len(x)==3;y[1]=metadata(x[1])
 elif tag=='proj':assert len(x)==4;y[1]=name(x[1]);integer(x[2])
 else:raise AssertionError('Unknown expression constructor '+str(tag))
 return y
def audit(path,intern):
 raw=pathlib.Path(path).read_bytes();rows=[]
 for line in raw.decode().splitlines():
  if line.startswith('{'):rows.append(json.loads(line))
  else:assert 'error:' not in line and 'error(' not in line,line
 assert rows[0]['record']=='header' and rows[-1]['record']=='footer'
 h,f=rows[0],rows[-1];assert h['schema']=='complete-module-dag-v1' and f['status']=='COMPLETE'
 assert h['module'] in (['str',['anonymous'],ORIGINAL],['str',['anonymous'],GUARD])
 assert h['declaration_count']==f['declaration_count']==len(rows)-2>0
 records={};total_nodes=0;theorems=0
 allowed={freeze(['str',['anonymous'],'propext']),freeze(['str',['str',['anonymous'],'Classical'],'choice']),freeze(['str',['str',['anonymous'],'Quot'],'sound'])}
 for d in rows[1:-1]:
  assert set(d)=={'record','name','kind','level_parameters','type_root','body_root','nodes','type_references','body_references','axioms','unsafe','partial'}
  assert d['record']=='declaration' and d['unsafe'] is False and d['partial'] is False
  assert d['kind'] in ('axiom','definition','theorem','opaque','quotient','inductive','constructor','recursor')
  if d['kind'] in ('definition','theorem','opaque'):assert d['body_root'] is not None
  theorems+=d['kind']=='theorem';nodes=[normalize_node(n) for n in d['nodes']];ids=[]
  for i,n in enumerate(nodes):
   cn=list(n)
   for pos in REFS.get(n[0],[]):
    ref=integer(n[pos]);assert ref<i;cn[pos]=ids[ref]
   k=freeze(cn)
   if k not in intern:intern[k]=len(intern)
   ids.append(intern[k])
  def traverse(root):
   if root is None:return set(),set()
   root=integer(root);assert root<len(nodes);seen=set();consts=set();todo=[root]
   while todo:
    i=todo.pop()
    if i in seen:continue
    seen.add(i);n=nodes[i]
    if n[0]=='const':consts.add(freeze(n[1]))
    todo.extend(n[pos] for pos in REFS.get(n[0],[]))
   return seen,consts
  ts,tr=traverse(d['type_root']);bs,br=traverse(d['body_root']);assert ts|bs==set(range(len(nodes)))
  assert tr=={freeze(name(n)) for n in d['type_references']}
  assert br=={freeze(name(n)) for n in d['body_references']}
  ax={freeze(name(n)) for n in d['axioms']};assert ax<=allowed
  key=freeze(name(d['name']));assert key not in records
  records[key]={'kind':d['kind'],'levels':[name(n) for n in d['level_parameters']],
    'type':ids[d['type_root']],'body':None if d['body_root'] is None else ids[d['body_root']],
    'type_refs':sorted(tr),'body_refs':sorted(br),'axioms':sorted(ax)}
  total_nodes+=len(nodes)
 return records,{'file':str(path),'sha256':hashlib.sha256(raw).hexdigest(),'declarations':len(records),'theorems':theorems,'expression_nodes':total_nodes}
def main():
 assert len(sys.argv) in (2,3);intern={};a,sa=audit(sys.argv[1],intern);out={'status':'PASS_COMPLETE_DAG_VALIDATION','ordinary':sa}
 if len(sys.argv)==3:
  b,sb=audit(sys.argv[2],intern);assert a==b,'Full declaration/type/body/reference/axiom mismatch'
  out.update(status='PASS_COMPLETE_ORDINARY_GUARD_EQUIVALENCE',guard=sb,normalization='Only exact module components in private or hygienic Names; all other binder labels, numeric hygiene tags, terms and metadata preserved; DAG sharing represented structurally')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
