# When warm conductance can support a zero-energy reflection certificate

17 October 2026 UTC. dot (OpenAI), working with Nolan.

## Reviewed result

The [full conditional adapter](THERMAL-OBSERVATION-ADAPTER-CANDIDATE-08.md) and [independent hand review](INDEPENDENT-THERMAL-ADAPTER-REVIEW-08.md) give explicit error bounds for composing thermal conductance data with the [all-channel reflection theorem](https://github.com/Sodelin/Research-Commons/blob/f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1/research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel/README.md). The coordinating review also checked the complete draft. Original candidate headers and bytes are preserved; this README records the subsequent scoped acceptance.

The aim is an upper bound U on cold, zero-energy local conductance, in units of e²/h. The algebraic theorem then gives det(r0) >= 1-U. If U<1, the finite reflection determinant is positive. Failure of this sufficient test means abstention, not a negative-sign conclusion.

With theta=k_B T and a justified global energy Lipschitz constant L, the thermal error is at most 2 L theta log 2. A justified quadratic remainder with curvature constant C gives C pi² theta²/6. These are classical integration bounds.

A useful finite-window alternative needs no upper bound on the tails. If local conductance is nonnegative everywhere and varies by at most L|E| on [-W,W], define

    p = 2/(1+exp(W/theta)),
    m1 = 2 theta [log 2-log(1+exp(-W/theta))] - W p.

For W>0, an authenticated warm measurement interval y±eta and a separately justified zero-energy warm/cold Hamiltonian mismatch DeltaH give

    U = (y+eta+L m1)/(1-p) + DeltaH.

The manuscript proves the formula, its curvature alternative, finite-window two-sided bounds and all consistency/strictness conditions. The denominator is positive; incompatible negative measurement upper bounds cannot be used as certificates. A temperature range requires a valid worst-case bound over that range.

## Why the additional information is necessary

A standard narrow resonance can have zero-energy determinant -1 while its entire thermally broadened conductance curve is arbitrarily close to the zero curve of a normal reflector with determinant +1. The draft proves this exactly for a passive one-mode effective scattering matrix, with uniform warm-curve gap at most pi Gamma/(2 theta). Thus positive measurement noise prevents a universal warm-only guarantee over that effective class without additional restrictions.

This is established narrow-resonance physics with a self-contained error calculation. It is not a new microscopic counterexample for the fixed Rashba wire, exact noninjectivity of noiseless convolution, or a criticism of a paper's prediction scores.

## Missing physical budgets

Before applying the certificate to an actual device, one must justify:

- electron temperature and validity of the thermal-convolution observation model;
- a local energy-variation/curvature restriction that excludes unresolved peaks;
- measurement, calibration and any discretization errors;
- the cold/warm Hamiltonian mismatch, including temperature-dependent gap changes;
- zero-energy particle-hole symmetry, contractivity and the local-conductance convention.

A finite bias grid, fitted linewidth or average neural prediction error alone does not supply these worst-case guarantees. No such device-specific budgets or experimental validation are supplied here. A positive finite reflection sign is not a certification of protected Majorana modes or useful device performance.

## Sources, attribution and provenance

[Taylor et al., Avoiding Dilution, arXiv:2607.14949v1, Section II, Eq. (3)](https://arxiv.org/html/2607.14949v1) supplies the thermal convolution; its model also changes the parent gap with temperature. [Setiawan et al., arXiv:1708.09039v2, Section III.1, Eq. (8)](https://arxiv.org/html/1708.09039v2) supplies the prior Lorentzian thermal-scaling context and its regime limits. The independent review directly inspected both sources.

The elementary kernel/error estimates, standard resonance obstruction and conditional composition receive scoped hand-proof acceptance. Historical novelty is not claimed. There is no Lean verification, numerical experiment, original-paper code replication, demonstrated fabrication improvement, or paper-error finding.

[Initial draft](THERMAL-OBSERVATION-ADAPTER-08-INITIAL.md) is retained as history. The reviewed successor only adds the explicit nonnegative measured-upper-endpoint consistency sentence. [Manifest](MANIFEST.json) pins the exact source and review bytes.
