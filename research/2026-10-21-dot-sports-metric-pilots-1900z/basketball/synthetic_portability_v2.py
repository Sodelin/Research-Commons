"""Illustrative two-context response experiment, NOT NBA validation or full RAPM.
Python 3 + already-installed numpy; no network, downloads or fitted NBA data.
"""
import json
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parent
REPS=200
P=20
N=200  # observations/player, context 1 training probability .15
SIGMA=5.
SHRINK=20.  # fixed illustrative pseudo-count, NOT selected on synthetic test

def experiment(heterogeneous):
    rows=[]
    for seed in range(REPS):
        rng=np.random.default_rng(seed)
        alpha=np.linspace(-3,3,P)
        beta=np.linspace(-6,6,P) if heterogeneous else np.zeros(P)
        # Identical RNG and allocations in positive/negative-control worlds.
        c=(rng.random((P,N))<.15).astype(int)
        y=alpha[:,None]+beta[:,None]*c+rng.normal(0,SIGMA,(P,N))
        marginal=y.mean(axis=1)
        centered_c=c-c.mean(axis=1)[:,None]
        common_slope=float(np.sum(centered_c*(y-marginal[:,None]))/np.sum(centered_c**2))
        base_intercept=marginal-common_slope*c.mean(axis=1)
        counts=c.sum(axis=1)
        m1=(y*c).sum(axis=1)/counts
        m0=(y*(1-c)).sum(axis=1)/(N-counts)
        # Player-specific slope shrunk towards common slope; preserve training marginal.
        neff=counts*(N-counts)/N
        slope=common_slope+(m1-m0-common_slope)*neff/(neff+SHRINK)
        intercept=marginal-slope*counts/N
        # Evaluation population shifts to 85% context 1; score true conditional
        # mean to isolate estimation bias. Future response noise adds 25 to MSE.
        true=np.stack([alpha,alpha+beta],axis=1)
        pred0=np.stack([base_intercept,base_intercept+common_slope],axis=1)
        pred1=np.stack([intercept,intercept+slope],axis=1)
        weights=np.array([.15,.85])
        loss0=float(np.mean(((pred0-true)**2)@weights))
        loss1=float(np.mean(((pred1-true)**2)@weights))
        rows.append((loss0,loss1))
    a=np.array(rows)
    return {"replicates":REPS,"additive_mean_MSE":float(a[:,0].mean()),
            "interaction_mean_MSE":float(a[:,1].mean()),
            "paired_mean_MSE_difference_interaction_minus_additive":float((a[:,1]-a[:,0]).mean()),
            "paired_difference_MC_standard_error":float((a[:,1]-a[:,0]).std(ddof=1)/np.sqrt(REPS)),
            "fraction_interaction_better":float(np.mean(a[:,1]<a[:,0]))}

# Exact observational-equivalence check, not a numerical proof of NBA behavior.
# All source observations c=0. Worlds have same alpha and noise, opposite slope.
rng=np.random.default_rng(10001)
noise=rng.normal(0,SIGMA,1000)
c=np.zeros(1000)
world_plus=2+6*c+noise
world_minus=2-6*c+noise
assert np.array_equal(world_plus,world_minus)
result={"status":"SYNTHETIC ONLY; no NBA observations or superiority claim",
        "baseline":"player main effects plus common context slope; interactions shrink towards common slope", 
        "design":{"players":P,"observations_per_player":N,"train_context1_probability":.15,
                  "test_context1_probability":.85,"noise_sd":SIGMA,"slope_shrinkage":SHRINK},
        "heterogeneous_effect":experiment(True),"zero_interaction_negative_control":experiment(False),
        "zero_overlap":{"training_arrays_identical":True,"target_mean_world_plus":8,
                        "target_mean_world_minus":-4,"minimum_possible_worst_absolute_error":6,
                        "sensitivity_interval_if_assume_abs_slope_at_most_6":[-4,8],
                        "interval_kind":"assumption-based; alpha taken known, not sampling confidence interval",
                        "support_action":"ABSTAIN from identified replacement claim"}}
assert result['heterogeneous_effect']['interaction_mean_MSE'] < result['heterogeneous_effect']['additive_mean_MSE']
assert result['zero_interaction_negative_control']['interaction_mean_MSE'] > result['zero_interaction_negative_control']['additive_mean_MSE']
(ROOT/'synthetic-results-v2.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
