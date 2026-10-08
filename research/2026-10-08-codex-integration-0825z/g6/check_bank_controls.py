import importlib.util, json, copy
from pathlib import Path
base=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('gate',base/'shared_bank_gate.py');m=importlib.util.module_from_spec(spec)
import sys;sys.modules['gate']=m;spec.loader.exec_module(m)
from fractions import Fraction as Q

def interval(lo,hi=None,lc=True,hc=True): return dict(lo=str(lo),hi=None if hi is None else str(hi),lo_closed=lc,hi_closed=hc)
d={'schema':'g6-fixed-rational-chart-v1','source_witness_note':'Original rooted binary cut-child fixture, HAND admission only; no Lean or empirical claim.', 'root':'r','ages':{'r':'6','u':'4','v':'4','h':'2','w':'1','a':'0','b':'0','c':'0','d':'0'},'edges':{'r_u':['r','u'],'r_v':['r','v'],'u_c':['u','c'],'v_d':['v','d'],'u_h':['u','h'],'v_h':['v','h'],'h_w':['h','w'],'w_a':['w','a'],'w_b':['w','b']},'hybrids':['h'],'profiles':[{'id':'fine','cuts':['0','1/2','3','5','7']},{'id':'coarse','cuts':['0','3','7']}],'hazard_cells':[],'inheritance_cells':[]}
d['original_parent_registry']={'h':[{'edge':'u_h','parent':'u','stored_bool':True},{'edge':'v_h','parent':'v','stored_bool':False}]}
d['register_contract']='One original hybrid register coordinate h, drawn once with native TRUE probability gamma_h for COMMON; INDEPENDENT routes each current carried ancestor; the gate samples neither.'
for k,dt in m.exposures(d).items():
 rho=Q(1,2) if k[1]=='h_w' else Q(1)
 h=rho*dt
 d['hazard_cells'].append({'profile':k[0],'population':k[1],'young':k[2],'old':k[3],'cell':interval(max(Q(0),h-Q(1,100)),h+Q(1,100))})
for p in d['profiles']:d['inheritance_cells'].append({'profile':p['id'],'hybrid':'h','cell':interval(Q(2,5),Q(2,5))})
(base/'FIXED-CHART-EXAMPLE.json').write_text(json.dumps(d,indent=2)+'\n')
results=[]
res=m.solve(d);assert res['status']=='FIXED_CHART_BANK_FEASIBLE';assert m.replay(d,res['bank']);results.append({'case':'positive_original_fixture_shared_fine_coarse','result':res})
bad=copy.deepcopy(d)
# SAME full original u_c, equal length epochs [1,2] and [2,3] in coarse row.
chosen=[c for c in bad['hazard_cells'] if c['profile']=='coarse' and c['population']=='u_c' and (c['young'],c['old']) in [('1','2'),('2','3')]]
assert len(chosen)==2
chosen[0]['cell']=interval(1,Q(11,10));chosen[1]['cell']=interval(2,Q(21,10))
r=m.solve(bad);assert r['status']=='INFEASIBLE_FIXED_CHART';results.append({'case':'prior_shared_equal_epochs_conflict_source_embedded','result':r})
bad=copy.deepcopy(d);bad['inheritance_cells'][0]['cell']=interval(Q(1,10),Q(2,10));bad['inheritance_cells'][1]['cell']=interval(Q(8,10),Q(9,10));r=m.solve(bad);assert r['status']=='INFEASIBLE_FIXED_CHART';results.append({'case':'prior_shared_gamma_conflict_source_embedded','result':r})
# Saturated high hazard gives an actual positive rational rate.
x=copy.deepcopy(d)
for c in x['hazard_cells']:
 if c['population']=='h_w':c['cell']=interval(10,None)
r=m.solve(x);assert r['status']=='FIXED_CHART_BANK_FEASIBLE';results.append({'case':'saturated_crossing_same_edge','status':r['status'],'rate':r['bank']['rates']['h_w']})
# Open endpoints, unsupported float, omitted epoch and tampered witness.
assert m.Interval(Q(0),Q(1),False,False).witness()==Q(1,2)
assert m.Interval(Q(1),Q(1),True,False).empty()
for name,x in [('float_date',copy.deepcopy(d)),('missing_epoch',copy.deepcopy(d))]:
 if name=='float_date':x['ages']['h']=2.0
 else:x['hazard_cells'].pop()
 try:m.solve(x);raise AssertionError('unexpected accept')
 except ValueError as e:results.append({'case':name,'status':'REFUSED','reason':str(e)})
bank=copy.deepcopy(res['bank']);bank['rates']['h_w']='3/4'
try:m.replay(d,bank);raise AssertionError('unexpected accept')
except ValueError as e:results.append({'case':'tampered_constant_edge_witness','status':'REFUSED','reason':str(e)})
# Inheritance may approach zero but strict boundary zero cannot enter.
x=copy.deepcopy(d)
for c in x['inheritance_cells']:c['cell']=interval(0,0)
r=m.solve(x);assert r['status']=='INFEASIBLE_FIXED_CHART';results.append({'case':'boundary_gamma_zero','result':r})
# tied u/v date derives ONE point, no fabricated zero duration.
assert all(v>0 for v in m.exposures(d).values());results.append({'case':'tied_original_unrelated_nodes','epochs':len(m.exposures(d)),'zero_exposure_count':0})
for name in ['missing_inheritance_replay','duplicate_inheritance_replay','duplicate_original_hybrid_replay']:
 x=copy.deepcopy(d)
 if name=='missing_inheritance_replay':x['inheritance_cells'].pop()
 elif name=='duplicate_inheritance_replay':x['inheritance_cells'].append(copy.deepcopy(x['inheritance_cells'][0]))
 else:x['hybrids'].append('h')
 try:m.replay(x,res['bank']);raise AssertionError('unexpected accept')
 except ValueError as e:results.append({'case':name,'status':'REFUSED','reason':str(e)})
(base/'BANK-CONTROL-RESULTS.json').write_text(json.dumps({'status':'executed exact Fraction controls','cases':results,'lean_builds':0,'empirical_claim':False},indent=2)+'\n')
print(json.dumps({'cases':len(results),'feasible_exposures':len(m.exposures(d)),'status':'PASS'}))
