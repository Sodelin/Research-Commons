"""Bounded floating-point checks for candidate28; not a proof or interval certificate."""
import json
import math
import numpy as np
from scipy.special import gammaln, logsumexp

I = np.eye(2)
X = np.array([[0., 1.], [1., 0.]])
Z = np.diag([1., -1.])
n = (I-Z)/2

def on_site(a, j, count):
    out = np.ones((1, 1))
    for i in range(count):
        out = np.kron(out, a if i == j else I)
    return out

def full_state(beta, R, a):
    count = R+2
    zs = [on_site(Z, i, count) for i in range(R)]
    S = sum(zs)
    nm = on_site(n, R, count)
    nd = on_site(n, R+1, count)
    xm = on_site(X, R, count)
    reservoir = -S.copy()
    for i in range(R):
        for j in range(i+1, R):
            reservoir -= zs[i] @ zs[j]
    H = reservoir+a*S@nm+(beta*R)**(-.5)*S@xm@nd
    eigenvalues, vectors = np.linalg.eigh(H)
    weights = np.exp(-beta*(eigenvalues-eigenvalues[0]))
    rho = (vectors*(weights/weights.sum()))@vectors.T
    g = np.diag(S@nm).astype(int)
    law = {v: float(np.diag(rho)[g == v].sum()) for v in set(g)}
    return rho, float(np.trace(rho@nd)), law

def sector_statistics(beta, R, a):
    # Exact symmetry reduction, evaluated here in ordinary floating point.
    records = []
    nm, nd = np.kron(n,I), np.kron(I,n)
    xm = np.kron(X,I)
    for j in range(R+1):
        s = R-2*j
        penalty = 2*j*(R-j)+2*j
        core = a*s*nm+s/math.sqrt(beta*R)*xm@nd
        energies, vectors = np.linalg.eigh(core)
        logbinom = gammaln(R+1)-gammaln(j+1)-gammaln(R-j+1)
        for v in range(4):
            w = vectors[:,v]**2
            pm, pd = float(w@np.diag(nm)), float(w@np.diag(nd))
            records.append((logbinom-beta*(penalty+energies[v]), j, s, pm, pd))
    norm = logsumexp([x[0] for x in records])
    law, data, bad = {}, 0., 0.
    for lw,j,s,pm,pd in records:
        mass = math.exp(lw-norm)
        data += mass*pd
        bad += mass*(j != 0)
        law[0] = law.get(0,0.)+mass*(1-pm)
        law[s] = law.get(s,0.)+mass*pm
    return data, law, bad

def tv(p,q):
    return .5*sum(abs(p.get(x,0.)-q.get(x,0.)) for x in set(p)|set(q))

def leakage_bound(beta,R):
    return 4*math.exp(2)*(math.expm1(R*math.log1p(math.exp(-beta*R)))
            +math.exp(-beta*R+R*math.log1p(math.exp(-beta*(R-1)))))

cases = 0
max_error = 0.
for beta in (.25, 1., 3.):
    for R in (1,2,3,4):
        states=[]
        for a in (.5,1.):
            assert R >= 1/(4*beta)
            rho,p,law=full_state(beta,R,a)
            ps,ls,bad=sector_statistics(beta,R,a)
            error=max(abs(p-ps),tv(law,ls))
            max_error=max(max_error,error)
            assert error<1e-10, (beta,R,a,error)
            assert bad<=leakage_bound(beta,R)+1e-12
            states.append((rho,p,law))
            cases+=1
        gap=np.abs(np.linalg.eigvalsh(states[0][0]-states[1][0])).sum()
        assert gap+1e-12>=2*abs(states[0][1]-states[1][1])

examples=[]
for R in (10,100,1000):
    beta=1.
    p0,l0,b0=sector_statistics(beta,R,.5)
    p1,l1,b1=sector_statistics(beta,R,1.)
    observed=tv(l0,l1)
    bound=8/(beta*R)+4*math.exp(-beta*R/2)+2*leakage_bound(beta,R)
    assert observed<=bound+1e-12
    examples.append({"beta":beta,"R":R,"N":R+2,
                     "data_probability_gap":abs(p0-p1),
                     "trace_norm_lower_bound":2*abs(p0-p1),
                     "score_outcome_TV":observed,
                     "R_times_score_TV":R*observed,
                     "bad_reservoir_probability_max":max(b0,b1)})

print(json.dumps({"status":"PASS: bounded floating-point checks only",
                  "direct_full_matrix_comparisons":cases,
                  "max_full_matrix_vs_sector_error":max_error,
                  "examples":examples},indent=2))
