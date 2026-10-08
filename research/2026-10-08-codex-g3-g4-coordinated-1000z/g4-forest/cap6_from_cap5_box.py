"""Complete six-root interval response of the SAME cap-five source cube.

The root in the cube is implicit, not the rational candidate. Conditional
use of the cap-five certificate awaits independent review of that package.
"""
from __future__ import annotations
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse,json,time,types

CAP5_REL="research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-positive/library-centre/"
PROVIDER_SHA="f00bf50eb084229c34a88ed6efe6552e59452fd56470dfe54a195dcd335d9109"
INPUT_SHA="bb6bcc498125a86b797748f8f936b60051ac327f07d761fab2caeab531d70a8e"
CERT_SHA="2ee7fcc77b2b5941b0350ea851118982dfe8ac20ab21a8f6be02585e9ccc3b34"
HELPER_SHA="e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8"

def captured_module(p,pin,name):
    raw=p.read_bytes()
    if sha256(raw).hexdigest()!=pin:raise ValueError(f"frozen source mismatch {p}")
    m=types.ModuleType(name);m.__file__=str(p)
    exec(compile(raw,str(p),"exec"),m.__dict__);return m

def source_class(m,h,fa):
    class Source6(m.Source):
        def __init__(self,fixed):
            states=[h.representative(s,fa) for s in h.SHAPES6];index={s:i for i,s in enumerate(h.SHAPES6)}
            E=h.ordinary_polynomials(states,index,fa);B=h.bigon_polynomials(states,index,fa)
            h.strict_source_controls(B,E,states,index,fa)
            assert all(poly.get((q,p),F(0))==c for row in B for poly in row for (p,q),c in poly.items())
            self.E=[[[ (k,m.D(c)) for k,c in p.items()] for p in row] for row in E]
            self.B=[[[ (p,q,m.D(c)) for (p,q),c in poly.items() if p>=q] for poly in row] for row in B]
            self.A=[m.D(v) for v in fixed["means"]]
            self.w4,self.U,self.seam,self.t,self.d,self.a,self.b=[m.D(fixed[k]) for k in ["w4","U","seam","t","d","a","b"]]
            self.q=[1-AA*self.t/2 for AA in self.A]
            self.C=h.delete_one(states,fa)
            self.source_controls={"all20_forest_rows_exact_equal_original":True,"strict_original_rational_arm_control":True}
        def vm(self,row,matrix):
            return [sum((row[k]*matrix[k][j] for k in range(20)),m.D(0)) for j in range(20)]
        def complete(self,u):
            w=[*u[:3],self.w4];X1,X2,X3,X6,X7=u[3:]
            X4,X5=self.q[0]*self.seam/self.b,1/(self.b*self.seam)
            edgesP=[self.a*self.b*self.U/self.q[2],X7/(self.q[1]*self.U),X6/(self.q[3]*X7),X5/(self.q[0]*X6),self.seam]
            edgesR=[self.seam,X3/(self.q[3]*X4),X2/(self.q[1]*X3),X1/(self.q[2]*X2),1/X1]
            row=[m.D(1)]+[m.D(0)]*19
            branches=[self.branch(A,W) for A,W in zip(self.A,w)]
            for labels,edges in [([2,1,3,0],edgesP),([0,3,1,2],edgesR)]:
                row=self.vm(row,self.ordinary(edges[0]))
                for j,label in enumerate(labels):
                    row=self.vm(row,branches[label]);row=self.vm(row,self.ordinary(edges[j+1]))
            target=self.ordinary(self.d)[0];residual=[x-y for x,y in zip(row,target)]
            # Exact algebraic edge telescoping: each label appears twice,
            # total ordinary survival = d/(q1*q2*q3*q4)^2, independently of X.
            qp=m.D(1)
            for q in self.q:qp*=q
            b6=(self.d/(qp*qp))**15
            for A,W in zip(self.A,w):b6*=self.diagonal(6,A,W)**2
            diagonal_difference=b6-self.d**15
            log_diagonal_defect=b6.log()-15*self.d.log()
            arm_gates=[]
            for A,W in zip(self.A,w):
                s,h2=1-A*self.t,W*self.t**3
                arm_gates.append([W.v,s.v,h2.v,(s*s-h2).v,((A*self.t)**2-h2).v])
            return row,residual,edgesP+edgesR,arm_gates,diagonal_difference,log_diagonal_defect
    return Source6

def main():
    ap=argparse.ArgumentParser();ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3]);ap.add_argument("--output",type=Path,required=True);args=ap.parse_args()
    if args.output.exists():raise ValueError("refusing to overwrite interval receipt")
    start=time.perf_counter();base=args.root/CAP5_REL
    m=captured_module(base/"certify_cap5_box_v3.py",PROVIDER_SHA,"frozen_cap5_interval_provider")
    m.mp.mp.dps=m.mp.iv.dps=160
    h=captured_module(args.root/m.HELPER,HELPER_SHA,"frozen_complete_forest_helper")
    fa,source_sha=h.load_source(args.root)
    raw=(base/"RATIONAL-BOX-INPUT.json").read_bytes();cert=(base/"INTERVAL-BOX-CERTIFICATE-V3.json").read_bytes()
    assert sha256(raw).hexdigest()==INPUT_SHA and sha256(cert).hexdigest()==CERT_SHA
    doc=json.loads(raw);prior=json.loads(cert)
    assert prior["status"]=="EXECUTED_OUTWARD_INTERVAL_CONTRACTION_GATE_PASS" and prior["input_sha256"]==INPUT_SHA
    cls=source_class(m,h,fa);src=cls(doc["fixed_rational_source"])
    radius=F(doc["parameter_cube_radius"])
    center=[m.D(x) for x in doc["approximate_rational_parameters"]]
    cube=[m.D(m.iv(x)+m.mp.iv.mpf([-1,1])*m.iv(radius)) for x in doc["approximate_rational_parameters"]]
    c_row,c_r,_,_,c_diag,c_log=src.complete(center)
    row,r,edges,arms,diag,logdef=src.complete(cube)
    lower=[sum((F(c,6)*v for c,v in zip(rr,r)),m.D(0)) for rr in src.C]
    physical=all(0<m.endpoints(e.v)[0]<=m.endpoints(e.v)[1]<1 for e in edges)
    physical=physical and all(all(m.endpoints(v)[0]>0 for v in gates) and m.endpoints(gates[1])[1]<1 for gates in arms)
    assert physical
    # Two equivalent actual source diagonal computations must overlap.
    diag_overlap=r[0].v-diag.v
    assert m.endpoints(diag_overlap)[0]<=0<=m.endpoints(diag_overlap)[1]
    def enc(v):return [str(m.exact_binary_rational(t)) for t in v._mpi_]
    def descriptive(v):return [m.mp.nstr(x,90) for x in m.endpoints(v)]
    separated=[i for i,v in enumerate(r) if m.endpoints(v.v)[1]<0 or m.endpoints(v.v)[0]>0]
    diag_separated=m.endpoints(diag.v)[1]<0 or m.endpoints(diag.v)[0]>0
    result={"status":"EXECUTED_OUTWARD_COMPLETE_CAP6_RESPONSE_OF_CAP5_SOURCE_CUBE",
            "source_sha256":source_sha,"helper_sha256":HELPER_SHA,"executed_interval_provider_sha256":PROVIDER_SHA,
            "cap5_input_sha256":INPUT_SHA,"cap5_certificate_sha256":CERT_SHA,
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),"mpmath_version":m.mp.__version__,"outward_precision_digits":160,
            "source_family":"SAME strict independent fair CURRENT-root eightcell P*R rational seam variant, all shared constants/parameters", "pair_target":"1/4",
            "parameter_order":doc["parameter_order"],"same_parameter_cube_radius":str(radius),
            "unknown_cap5_root_accounted":"all output intervals enclose EVERY source point of the closed cube; conditional application to unique implicit cap5 root awaits independent certificate review",
            "cap5_candidate_itself_not_claimed_centre":True,"exact_original_source_controls":src.source_controls,
            "full20_cap6_candidate_row_intervals":[enc(v.v) for v in c_row],
            "full20_cap6_candidate_residual_intervals":[enc(v.v) for v in c_r],
            "full20_cap6_cube_row_intervals":[enc(v.v) for v in row],
            "full20_cap6_cube_residual_intervals":[enc(v.v) for v in r],
            "full20_cap6_cube_residual_decimal_displays":[descriptive(v.v) for v in r],
            "complete_cap5_deletion_residual_cube_intervals":[enc(v.v) for v in lower],
            "cap5_root_lower_residual_is_zero_if_certificate_review_accepts":True,
            "cap6_target_free_coordinate_indices":h.FREE,
            "cap6_nine_cube_residual_intervals":[enc(r[i].v) for i in h.FREE],
            "new_diagonal_difference_tight_interval":enc(diag.v),
            "new_diagonal_difference_decimal_display":descriptive(diag.v),
            "new_log_diagonal_defect_tight_interval":enc(logdef.v),
            "new_log_diagonal_defect_decimal_display":descriptive(logdef.v),
            "direct_row_vs_telescoped_diagonal_interval_contains_zero":True,
            "new_diagonal_excludes_zero_on_entire_cube":diag_separated,
            "full_response_separating_indices_on_entire_cube":separated,
            "all_original_source_parameters_strict_over_cube":physical,
            "ordinary_edge_survival_cube_intervals":[enc(v.v) for v in edges],
            "arm_inequality_cube_intervals":[[enc(v) for v in gates] for gates in arms],
            "interval_endpoint_encoding":"exact rational representations of outward binary endpoints; decimals are displays only",
            "runtime_seconds":time.perf_counter()-start,
            "not_claimed":["cap5 certificate independently accepted here","cap6 ordinary commonzero","J6 admissibility before new diagonal match","all-cap obstruction","G4 master closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"new_diagonal_excludes_zero":diag_separated,
                      "new_diagonal_difference":result["new_diagonal_difference_decimal_display"],
                      "full_response_separators":separated,"runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":main()
