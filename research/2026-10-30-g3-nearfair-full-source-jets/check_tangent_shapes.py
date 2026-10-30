import argparse,sys,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('engine_root',type=Path);args=ap.parse_args();sys.path.insert(0,str(args.engine_root))
from source_bindings import verify
verify(args.engine_root)
from forest_modular import *
z=np.load(args.engine_root/'fullcap-data.npz');jets=np.load(Path(__file__).with_name('quartic-matrices.npz'))
assert int(z['P'])==P
V,W,T,U=[z[k] for k in ['V','W','T','U']];rc=z['root_counts']
R3=mm(mm(W,jets['R3']),V);R4=mm(mm(W,jets['R4']),V)
records=[]
for a in range(12,1,-1):
 ag=np.flatnonzero(rc==a)
 for b in range(a-1,0,-1):
  bg=np.flatnonzero(rc==b);ix=np.ix_(ag,bg)
  r=span_rank([T[ix],U[ix],R3[ix]]);r4=span_rank([T[ix],U[ix],R3[ix],R4[ix]])
  if r4>r:records.append({'from_roots':a,'to_roots':b,'base_rank':r,'with_quartic_rank':r4,'block_shape':[len(ag),len(bg)]})
out={'status':'PASS diagnostic','prime':P,'reference_t_mod':int(z['t']),'new_quartic_shape_blocks':records,'limitation':'Only tests instantaneous reference scale/gap/bias tangent shape spans plus cubic source direction; does NOT include nonlinear lower-order whole-word retiming residuals, clocks, or integration.'}
Path(__file__).with_name('tangent-shape-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
