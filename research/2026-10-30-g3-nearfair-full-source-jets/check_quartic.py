import argparse,sys,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('engine_root',type=Path);args=ap.parse_args();sys.path.insert(0,str(args.engine_root))
from source_bindings import verify
verify(args.engine_root)
from forest_modular import *
z=np.load(Path(__file__).with_name('full-cap12-identity-jets.npz'));Q,A3,A4,R3=[z[k] for k in ['Q','A3','A4','R3']]
Q2=mm(Q,Q);Q3=mm(Q,Q2);Q4=mm(Q,Q3);QA3=mm(Q,A3)
def c(n,d=1):return n*pow(d,-1,P)%P
R4=(c(1,36)*A3-c(1,72)*A4+c(1,576)*Q+c(1,36)*QA3+c(5,384)*Q2+c(1,576)*Q3-c(1,384)*Q4)%P
QR=mm(Q,R3);RQ=mm(R3,Q)
res={'status':'PASS computation','prime':P,'cap':12,'rank_R3_R4':span_rank([R3,R4]),'rank_R3_QR3_R3Q':span_rank([R3,QR,RQ]),'rank_with_R4':span_rank([R3,QR,RQ,R4]),'scope':'Full source modular matrix span diagnostics; rank lower bounds over Q when rational identities bind; not physical whole-word feasibility or positivity'}
np.savez_compressed(Path(__file__).with_name('quartic-matrices.npz'),R4=R4,R3=R3,QR=QR,RQ=RQ)
Path(__file__).with_name('quartic-check.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
