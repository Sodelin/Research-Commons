from verify_dag_audit_v2 import scan
import json,copy,pathlib,hashlib
n=lambda s:['str',['anonymous'],s]
r=[{'record':'header','schema':'complete-module-dag-v1','module':n('Synthetic'),'module_display':'Synthetic','declaration_count':1},{'record':'declaration','name':n('syntheticDecl'),'name_display':'syntheticDecl','kind':'definition','level_parameters':[],'type_root':0,'body_root':0,'nodes':[['sort',['zero']]],'type_references':[],'type_references_display':[],'body_references':[],'body_references_display':[],'axioms':[],'axioms_display':[],'unsafe':False,'partial':False},{'record':'footer','status':'COMPLETE','declaration_count':1}]
def check(x,classification=None,census=None):return scan(map(json.dumps,x),['Synthetic'],census,classification)
assert check(r)['declaration_count']==1
partial=copy.deepcopy(r);partial[1].update(name=['str',['str',['anonymous'],'runtime'],'_unsafe_rec'],name_display='runtime._unsafe_rec',partial=True)
cl={'allowed_G2_partial_names':['runtime._unsafe_rec'],'all_context_partial_names':['runtime._unsafe_rec']}
assert check(partial,cl)['partial_companion_count']==1
cases=[]
def fail(label,x,classification=None,census=None):
 try:check(x,classification,census)
 except (AssertionError,KeyError):cases.append({'control':label,'rejected':True})
 else:raise AssertionError('Control accepted '+label)
for label,mut in [('missing_footer',lambda x:x.pop()),('wrong_scope',lambda x:x[0].update(module=n('Wrong'),module_display='Wrong')),('owned_axiom',lambda x:x[1].update(kind='axiom')),('nonstandard_axiom',lambda x:x[1].update(axioms=[n('sorryAx')],axioms_display=['sorryAx'])),('unsafe',lambda x:x[1].update(unsafe=True)),('unclassified_partial',lambda x:x[1].update(partial=True)),('dangling_DAG',lambda x:x[1].update(nodes=[['app',0,0]])),('missing_body',lambda x:x[1].update(body_root=None)),('wrong_count',lambda x:x[2].update(declaration_count=2)),('inconsistent_display',lambda x:x[1].update(body_references=[n('syntheticDecl')],body_references_display=['different'])),('noninjective_display',lambda x:x[1].update(body_references=[n('otherStructured')],body_references_display=['syntheticDecl'])),('reference_array_mismatch',lambda x:x[1].update(body_references=[n('otherStructured')]))]:
 x=copy.deepcopy(r);mut(x);fail(label,x)
x=copy.deepcopy(partial);x[1]['kind']='theorem';fail('partial_theorem',x,cl)
fail('missing_classified_companion',r,cl)
x=copy.deepcopy(partial);x[1].update(body_references=[n('providerPartial')],body_references_display=['providerPartial']);cl2=dict(cl,all_context_partial_names=['runtime._unsafe_rec','providerPartial']);fail('non_self_partial_reference',x,cl2)
x=copy.deepcopy(r);x[1].update(name=['str',['str',['anonymous'],'Synthetic'],'_@'],name_display='Synthetic.«_@»');c={'declarations':[{'name':'Synthetic._@','kind':'definition','module':'Synthetic','type_references':[],'body_references':[],'axioms':[]}]};fail('quote_stripping_not_accepted',x,census=c)
p=pathlib.Path(__file__).parent;out={'scope':'Synthetic parser controls only, no Lean proof or runtime verification.','valid_controls':2,'invalid_controls':cases,'verifier_sha256':hashlib.sha256((p/'verify_dag_audit_v2.py').read_bytes()).hexdigest()};(p/'DAG-VERIFIER-V2-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n');print('2 positive + '+str(len(cases))+' negative controls passed')
