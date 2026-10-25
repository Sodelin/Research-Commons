"""Finite-state endpoint control, not a proof of full genealogy TV or novelty."""
import json, math, platform
import numpy as np
import scipy
from scipy.linalg import expm

# Two unordered extant lineages, states AA, AB, BB, coalesced.
# Coalesced state absorbs: deme of its remaining ancestor is deliberately forgotten.
gamma = 0.3
lam = 1.7
C = np.array([[-lam,0,0,lam],[0,0,0,0],[0,0,-lam,lam],[0,0,0,0]], float)
R = np.array([[(1-gamma)**2,2*gamma*(1-gamma),gamma**2,0],
              [0,1-gamma,gamma,0],[0,0,1,0],[0,0,0,1]], float)
rows=[]
for delta in [0.1,0.03,0.01,0.003,0.001,0.0003]:
    m=-math.log1p(-gamma)/delta
    M=np.array([[-2*m,2*m,0,0],[0,-m,m,0],[0,0,0,0],[0,0,0,0]])
    pulse=R@expm(C*delta)
    migration=expm((C+M)*delta)
    tv=float(np.abs(pulse-migration).sum(axis=1).max()/2)
    bound=min(1,2*lam*delta)
    assert tv <= bound+1e-12
    assert np.max(np.abs(pulse.sum(axis=1)-1)) < 1e-12
    assert np.max(np.abs(migration.sum(axis=1)-1)) < 1e-12
    rows.append(dict(delta=delta,migration_rate=m,endpoint_max_row_TV=tv,
                     full_genealogy_candidate_upper_bound=bound))
print(json.dumps(dict(python=platform.python_version(),numpy=np.__version__,
                     scipy=scipy.__version__,gamma=gamma,coalescence_rate=lam,
                     scope='Executed floating-point endpoint control only; not full genealogy verification.',
                     results=rows),indent=2))
