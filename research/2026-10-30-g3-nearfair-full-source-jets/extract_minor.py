import argparse,sys,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('engine_root',type=Path);args=ap.parse_args();sys.path.insert(0,str(args.engine_root))
from source_bindings import verify
verify(args.engine_root)
from forest_modular import *
z=np.load(args.engine_root/'fullcap-data.npz');r=np.load(Path(__file__).with_name('quartic-matrices.npz'));V,W,T,U=[z[k] for k in ['V','W','T','U']];rc=z['root_counts'];R3=mm(mm(W,r['R3']),V);R4=mm(mm(W,r['R4']),V)
rows=np.flatnonzero(rc==12);cols=np.flatnonzero(rc==8);ix=np.ix_(rows,cols)
A=np.stack([a[ix].reshape(-1) for a in [T,U,R3,R4]])%P;G=A.copy();piv=[]
for i in range(4):
 j=int(np.flatnonzero(G[i])[0]);piv.append(j);G[i]=G[i]*pow(int(G[i,j]),-1,P)%P
 for k in range(i+1,4):G[k]=(G[k]-G[k,j]*G[i])%P
M=A[:,piv].tolist();G=[row[:] for row in M];det=1
for i in range(4):
 j=next(j for j in range(i,4) if G[j][i]%P)
 if j!=i:G[i],G[j]=G[j],G[i];det=-det
 pivot=G[i][i]%P;det=det*pivot%P;iv=pow(pivot,-1,P)
 for j in range(i+1,4):
  m=G[j][i]*iv%P;G[j]=[(a-m*b)%P for a,b in zip(G[j],G[i])]
assert det!=0
out={'prime':P,'cap':12,'reference_t_rational':[999,1000],'reference_t_mod':int(z['t']),'block':[12,8],'row_order':['reference h derivative T','ordinary generator U','dust cubic R3','dust critical quartic R4'],'selected_flat_block_columns':piv,'matrix_mod':M,'determinant_mod':det,'status':'PASS exact nonzero minor','limitation':'Linear tangent-shape independence only; complete nonlinear whole-word jets not eliminated.'}
Path(__file__).with_name('TANGENT-SHAPE-MINOR.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
