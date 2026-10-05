"""Independent all-real menu formulas, coverage and tag/action controls."""
from pathlib import Path
import sys,json
import z3
P=Path(sys.argv[1]).resolve();sys.path.insert(0,str(P))
from verify_algebraic_policy import guard,expression
from assemble_cad_terminal_policy import legacy_guard
from cad_action_sections import ActionSectionWriter
from fractions import Fraction
full=json.loads((P/'PREPARED-TERMINAL-REQUEST.json').read_text());red=json.loads((P/'PRUNED-TERMINAL-REQUEST.json').read_text())['prepared'];sel=json.loads((P/'EXPORTED-REQUEST-TERMINAL-SELECTOR.json').read_text())
x,y,z,w=z3.Reals('h0_0 h0_1 h0_2 a0_0');obs={'h0_0':x,'h0_1':y,'h0_2':z,'a0_0':w}
H=z3.Or(z3.And(0<x,x<z3.RealVal('1/3'),y==x,z==1-2*x),z3.And(0<x,x<z3.RealVal('1/3'),z==x,y==1-2*x),z3.And(z3.RealVal('1/3')<x,x<1,y==(1-x)/2,z==(1-x)/2))
expected={0:z3.BoolVal(False),1:H,2:z3.And(H,0<w,w<1)};out=[]
def query(name,f):
 s=z3.SolverFor('QF_NRA');s.set(timeout=15000);s.add(f);status=s.check();out.append({'name':name,'status':str(status),'query_smt2':s.to_smt2()});assert status==z3.unsat,(name,status,s.model() if status==z3.sat else s.reason_unknown())
for a,b in zip(full['relations'],red['relations']):
 i=a['menu_index'];ar,ad=guard(a['fibre']['winning_relation'],obs);br,bd=guard(b['fibre']['winning_relation'],obs)
 query('original_support_'+str(i),z3.Xor(z3.And(ad,ar),expected[i]));query('pruned_support_'+str(i),z3.Xor(z3.And(bd,br),expected[i]))
allg=[];prior=z3.BoolVal(False)
for i,cell in enumerate(sel['Export']['cells']):
 g,d=guard(legacy_guard(cell['guard']),obs);allg.append(g);query(f'cell{i}_guard_total',z3.Not(d));query(f'cell{i}_guard_within_H',z3.And(g,z3.Not(H)))
 tag=Fraction(cell['weights'][-1]['value']);assert tag.denominator==1;support=full['configured_supports'][tag.numerator]
 if z3.is_false(z3.simplify(g)):continue
 call=ActionSectionWriter(1).call(cell['weights'][:-1],support);scope=dict(obs);domain=g
 for sec in call.get('sections',[]):
  root=z3.FreshReal('independentPositiveRoot');coeff=[expression(v,scope)[0] for v in sec['coefficients']];lo,lov=expression(sec['lower'],scope);hi,hiv=expression(sec['upper'],scope)
  poly=lambda u:sum(a*(z3.RealVal(1) if j==0 else u**j) for j,a in enumerate(coeff))
  query(f'cell{i}_root_endpoint_sign',z3.And(domain,z3.Not(z3.And(lov,hiv,lo<hi,poly(lo)*poly(hi)<0))))
  domain=z3.And(domain,lo<root,root<hi,poly(root)==0);scope[sec['name']]=root
 weights=[expression(v,scope) for v in call['weights']];w0,w1=[a for a,d in weights]
 query(f'cell{i}_selected_full_support',z3.And(domain,z3.Not(z3.And(*[d for a,d in weights],w0>0,w1>0,w0+w1==1))))
 query(f'cell{i}_chosen_menu_fibre',z3.And(domain,z3.Not(z3.substitute(expected[tag.numerator],(w,w0)))))
 query(f'cell{i}_principal_action_equation',z3.And(domain,w0*w0*(x*x+2)!=x*x+1))
query('complete_source_history_coverage',z3.Xor(z3.Or(*allg),H))
print(json.dumps({'status':'PASS_INDEPENDENT_COMPLETE_MENU_AND_SELECTED_ROOT_CONTROLS','controls':out,'separate_rival_source_parameters':'inherited exact fibre compiler; hand expected support relations checked globally'},indent=2))
