"""Outward-rounded interval contraction gate for an actual cap-five source.

Rational fixed source constants and rational approximate parameters are
inputs. No numerical output from the earlier root finder is taken as exact.
First derivatives propagate through the complete authenticated forest law.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import time
import types
import mpmath as mp

HELPER = "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-forest/exact_forest_layer.py"
HELPER_SHA = "e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8"
N = 8


def iv(q):
    if isinstance(q, str) or isinstance(q, F) or isinstance(q, int):
        q = F(q)
        return mp.iv.mpf(q.numerator)/q.denominator
    return q


def endpoints(x):
    return mp.mpf(x._mpi_[0]), mp.mpf(x._mpi_[1])


def upper_abs(x):
    a, b = endpoints(x)
    return max(abs(a), abs(b))


class D:
    def __init__(self, v, d=None):
        self.v = iv(v)
        self.d = [iv(0) for _ in range(N)] if d is None else d

    def __add__(self, y):
        y = lift(y)
        return D(self.v+y.v, [a+b for a,b in zip(self.d,y.d)])
    __radd__ = __add__

    def __neg__(self):
        return D(-self.v, [-a for a in self.d])

    def __sub__(self, y):
        return self+-lift(y)

    def __rsub__(self, y):
        return lift(y)+-self

    def __mul__(self, y):
        y = lift(y)
        return D(self.v*y.v, [a*y.v+self.v*b for a,b in zip(self.d,y.d)])
    __rmul__ = __mul__

    def __truediv__(self, y):
        y = lift(y)
        return D(self.v/y.v, [(a*y.v-self.v*b)/(y.v*y.v) for a,b in zip(self.d,y.d)])

    def __rtruediv__(self, y):
        return lift(y)/self

    def __pow__(self, n):
        if not isinstance(n,int) or n < 0:
            raise ValueError("only nonnegative integer AD powers")
        if n == 0:
            return D(1)
        return D(self.v**n, [n*self.v**(n-1)*a for a in self.d])

    def log(self):
        return D(mp.iv.log(self.v), [a/self.v for a in self.d])


def lift(v):
    return v if isinstance(v,D) else D(v)


class Source:
    def __init__(self, root, fixed):
        p = root/HELPER
        raw = p.read_bytes()
        if sha256(raw).hexdigest()!=HELPER_SHA:
            raise ValueError("helper source mismatch")
        h = types.ModuleType("read_only_authenticated_cap5_helper")
        h.__file__ = str(p)
        exec(compile(raw,str(p),"exec"),h.__dict__)
        fa, self.original_sha = h.load_source(root)
        states = [h.representative(s,fa) for s in h.SHAPES5]
        index = {s:i for i,s in enumerate(h.SHAPES5)}
        E = h.ordinary_polynomials(states,index,fa)
        B = h.bigon_polynomials(states,index,fa)
        self.E = [[[(k,D(c)) for k,c in p.items()] for p in row] for row in E]
        self.B = [[[(p,q,D(c)) for (p,q),c in poly.items() if p>=q] for poly in row] for row in B]
        self.A = [D(v) for v in fixed["means"]]
        self.w4,self.U,self.seam,self.t,self.d,self.a,self.b = [D(fixed[k]) for k in ["w4","U","seam","t","d","a","b"]]
        self.q = [1-AA*self.t/2 for AA in self.A]
        self.Einv = self.ordinary(1/self.d)[0]
        # Independent strict rational control against the original labelled
        # source API, before interval AD or quotient coordinates are used.
        xx,yy,zz=F(1,3),F(3,4),F(2,5)
        for i,f in enumerate(states):
            direct=[F(0)]*10
            for v,p in fa.bigon_law(len(f),xx,yy,F(1,2),"independent").items():
                direct[index[h.forest_shape(fa.graft(f,v))]]+=p
            polynomial=[sum((c*xx**p*yy**q for (p,q),c in poly.items()),F(0)) for poly in B[i]]
            if polynomial!=direct or min(direct)<0 or sum(direct,F(0))!=1:
                raise ValueError("original complete source control failed")
            direct=[F(0)]*10
            for v,p in fa.edge_law(len(f),zz).items():
                direct[index[h.forest_shape(fa.graft(f,v))]]+=p
            if [h.eval_poly(poly,zz) for poly in E[i]]!=direct:
                raise ValueError("original ordinary control failed")
        self.source_controls={"ten_current_forest_rows_exact_equal_original":True,
                              "rational_arms":[str(xx),str(yy)],"ordinary_survival":str(zz)}

    def ordinary(self,z):
        return [[sum((c*z**e for e,c in p),D(0)) for p in row] for row in self.E]

    def branch(self,A,w):
        s,h2=1-A*self.t,w*self.t**3
        values={}
        for row in self.B:
            for poly in row:
                for p,q,_ in poly:
                    if (p,q) in values:
                        continue
                    d=p-q
                    val=(s*s-h2)**q
                    if d:
                        val*=2*sum((comb(d,2*j)*s**(d-2*j)*h2**j for j in range(d//2+1)),D(0))
                    values[p,q]=val
        return [[sum((c*values[p,q] for p,q,c in poly),D(0)) for poly in row] for row in self.B]

    def diagonal(self,n,A,w):
        s,h2=1-A*self.t,w*self.t**3
        val=D(0)
        for k in range(n+1):
            px,py=comb(k,2),comb(n-k,2)
            lo,diff=min(px,py),abs(px-py)
            sym=(s*s-h2)**lo * sum((comb(diff,2*j)*s**(diff-2*j)*h2**j for j in range(diff//2+1)),D(0))
            val+=F(comb(n,k),2**n)*sym
        return val

    def vm(self,row,matrix):
        return [sum((row[k]*matrix[k][j] for k in range(10)),D(0)) for j in range(10)]

    def evaluate(self,u):
        w=[*u[:3],self.w4]
        theta=u[3:]
        X1,X2,X3,X6,X7=theta
        X4,X5=self.q[0]*self.seam/self.b,1/(self.b*self.seam)
        edgesP=[self.a*self.b*self.U/self.q[2],X7/(self.q[1]*self.U),X6/(self.q[3]*X7),X5/(self.q[0]*X6),self.seam]
        edgesR=[self.seam,X3/(self.q[3]*X4),X2/(self.q[1]*X3),X1/(self.q[2]*X2),1/X1]
        row=self.Einv
        branches=[self.branch(A,W) for A,W in zip(self.A,w)]
        for labels,edges in [([2,1,3,0],edgesP),([0,3,1,2],edgesR)]:
            row=self.vm(row,self.ordinary(edges[0]))
            for j,label in enumerate(labels):
                row=self.vm(row,branches[label])
                row=self.vm(row,self.ordinary(edges[j+1]))
        q4=[row[0]+F(2,5)*row[1],
            F(3,5)*row[1]+F(4,5)*row[2]+F(3,5)*row[3],
            F(2,5)*row[3]+F(2,5)*row[4]+F(4,5)*row[5]+F(4,5)*row[6],
            F(1,5)*row[2]+F(3,5)*row[4],
            F(1,5)*row[5]+F(1,5)*row[7]+F(3,5)*row[9],
            F(1,5)*row[6]+F(4,5)*row[7]+row[8]+F(2,5)*row[9]]
        C=q4[3]-(q4[2]+q4[3])/3
        H=q4[4]-(q4[4]+q4[5])/3
        ell=[sum((self.diagonal(n,A,W).log() for A,W in zip(self.A,w)),D(0)) for n in range(2,6)]
        l2,l3,l4,l5=ell
        F8=[2*(l3-3*l2)/self.t**3,
            2*(l4-4*l3+6*l2)/self.t**4,
            2*(l5-5*l4+10*l3-10*l2)/self.t**5,
            C/self.t**3,(C+H)/self.t**3,row[7]/self.t**3,row[8]/self.t**3,row[9]/self.t**3]
        # Physical arms are checked through exact h^2 inequalities, avoiding
        # uncertain square-root routing or a numerical positivity test.
        arm_gates=[]
        for A,W in zip(self.A,w):
            s,h2=1-A*self.t,W*self.t**3
            arm_gates.append([W.v,s.v,h2.v,(s*s-h2).v,((A*self.t)**2-h2).v])
        return F8,edgesP+edgesR,arm_gates


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[4])
    ap.add_argument("--input",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--precision",type=int,default=120)
    args=ap.parse_args()
    if args.output.exists():
        raise ValueError("refusing to overwrite saved certificate")
    started=time.perf_counter()
    mp.mp.dps=mp.iv.dps=args.precision
    raw=args.input.read_bytes()
    doc=json.loads(raw)
    fixed,center,r=doc["fixed_rational_source"],doc["approximate_rational_parameters"],F(doc["parameter_cube_radius"])
    src=Source(args.root,fixed)
    def parameters(box):
        out=[]
        for j,c in enumerate(center):
            v=iv(c)
            if box:
                v+=mp.iv.mpf([-1,1])*iv(r)
            derivative=[iv(int(j==k)) for k in range(N)]
            out.append(D(v,derivative))
        return out
    Fc,_,_=src.evaluate(parameters(False))
    midpoint=mp.matrix([[sum(endpoints(v.d[j]))/2 for j in range(N)] for v in Fc])
    approx_inverse=mp.inverse(midpoint)
    # Round the inverse to an explicit rational matrix, then revalidate it.
    C_rat=[[str(F(mp.nstr(approx_inverse[i,j],100))) for j in range(N)] for i in range(N)]
    C=[[iv(q) for q in row] for row in C_rat]
    Fb,edges,arm_gates=src.evaluate(parameters(True))
    J=[[v.d[j] for j in range(N)] for v in Fb]
    error=[[iv(int(i==j))-sum((C[i][k]*J[k][j] for k in range(N)),iv(0)) for j in range(N)] for i in range(N)]
    # All upper bounds are outward intervals until this final endpoint.
    q_rows=[sum((abs(v) for v in row),iv(0)) for row in error]
    q=max(endpoints(v)[1] for v in q_rows)
    displacement=[sum((C[i][j]*Fc[j].v for j in range(N)),iv(0)) for i in range(N)]
    displacement_bound=max(upper_abs(v) for v in displacement)
    M_iv=max([iv(1)]+[sum((abs(q) for q in row),iv(0)) for row in C],key=lambda x:endpoints(x)[1])
    M=endpoints(M_iv)[1]
    # Exact conservative rational M above the outward interval endpoint.
    M_rat=F(mp.nstr(M,100))*F(1000001,1000000)
    eta=r/(4*M_rat)
    edge_bounds=[endpoints(e.v) for e in edges]
    physical=all(0<lo<=hi<1 for lo,hi in edge_bounds)
    physical=physical and all(all(endpoints(v)[0]>0 for v in gates) and endpoints(gates[1])[1]<1 for gates in arm_gates)
    # Ninth control varies only the already positive oldest edge by v near1.
    oldest_v=iv(fixed["a"])*iv(fixed["b"])*iv(fixed["U"])/(1-iv(fixed["means"][2])*iv(fixed["t"])/2)
    vbox=iv(1)+mp.iv.mpf([-1,1])*iv(r)
    vlo,vhi=endpoints(oldest_v*vbox)
    physical=physical and 0<vlo<=vhi<1
    accepted=physical and q<mp.mpf("0.5") and displacement_bound<mp.mpf(r.numerator)/r.denominator/4 and M_rat>M
    def fmt(v): return mp.nstr(v,110)
    def enc(v): return list(map(fmt,endpoints(v)))
    result={
        "status":"EXECUTED_OUTWARD_INTERVAL_CONTRACTION_GATE_PASS" if accepted else "INTERVAL_GATE_FAIL",
        "input_sha256":sha256(raw).hexdigest(),"own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
        "helper_sha256":HELPER_SHA,"original_source_sha256":src.original_sha,
        "mpmath_version":mp.__version__,"interval_precision_decimal_digits":args.precision,
        "exact_original_source_controls":src.source_controls,
        "source_family":"strict private independent fair CURRENT-root eight-cell P*R; shared physical bank; rational seam variant with exact pair telescoping",
        "coordinate_order":["2sumD3/t^3","2sumD4/t^4","2sumD5/t^5","C(N)/t^3","D(N)/t^3","p7(N)/t^3","p8(N)/t^3","p9(N)/t^3"],
        "formal_normalization":"N=E(4)*S; E(4) is proof-only, not a physical factor",
        "explicit_rational_preconditioner_C":C_rat,
        "center_F_interval": [enc(v.v) for v in Fc],
        "complete_Jacobian_interval_on_cube":[[enc(v) for v in row] for row in J],
        "identity_minus_CJ_interval":[[enc(v) for v in row] for row in error],
        "row_sum_contraction_bound_intervals":list(map(enc,q_rows)),
        "contraction_infinity_norm_upper_bound":fmt(q),
        "center_displacement_CF_intervals":list(map(enc,displacement)),
        "center_displacement_infinity_upper_bound":fmt(displacement_bound),
        "parameter_cube_radius":str(r),"M_conservative_exact_rational":str(M_rat),
        "certified_target_scaled_coordinate_radius_exact_rational":str(eta),
        "certified_target_scaled_coordinate_radius_approximate":fmt(mp.mpf(eta.numerator)/eta.denominator),
        "ordinary_edge_interval_bounds": [[fmt(lo),fmt(hi)] for lo,hi in edge_bounds],
        "arm_strictness_gate_order":["w>0","0<s<1","h2>0","s2-h2>0","(A*t)2-h2>0"],
        "arm_strictness_gate_intervals":[list(map(enc,row)) for row in arm_gates],
        "ninth_leading_edge_interval":[fmt(vlo),fmt(vhi)],
        "all_parameters_strict_over_closed_cube":physical,
        "conclusion_if_gate_passes":"for every scaled coordinate target y with ||y||infinity<=eta, the fixed rational C contraction realizes y in this actual source cube; y=0 is an exact ordinary cap-five centre. Ninth pair coordinate v-1 factorizes independently and obeys same gate.",
        "runtime_seconds":time.perf_counter()-started,
        "not_claimed":["exact rational centre parameters","source realizations beyond cap-five","useful large library radius","uniform radius over signed clocks/caps","controlled Lawson factorization length or positive budget","G4 closure"]
    }
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"status":result["status"],"q":fmt(q),"displacement":fmt(displacement_bound),"M":fmt(M),"eta":result["certified_target_scaled_coordinate_radius_approximate"],"runtime_seconds":result["runtime_seconds"]}))
    if not accepted:
        raise SystemExit(1)


if __name__=="__main__":
    main()
