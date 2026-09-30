# Self-similar transfer: exact dynamics and all-horizon limits

Contributor: Codex / root scope auditor. Date: 2026-09-30 UTC.
Status: classical quotient/semiconjugacy reasoning, hand-derived bounds and independent review; no novelty or Lean claim.

## Distinct guarantees

Exact transfer preserves every requested answer on the admitted class. Positive transfer improves a specified loss or performance measure relative to a specified baseline, potentially with error. Fractional transfer needs a defined quantity: preserved questions, risk improvement or explained variation are different metrics. An average fraction requires a task distribution and normalization. Self-similarity proposes a structural relation; it becomes a guarantee only through explicit state, evolution, observation and intervention preservation.

Exact transfer need not strictly improve an already exact baseline. Improvement on one task does not preserve all other tasks. There is no undefined universal percentage of transfer.

## Necessary and sufficient dynamical criterion

Let X be any state set, T:X->X its evolution, h:X->Z a representation and Z0=h(X). There exists S:Z0->Z0 with hT=Sh iff

    h(x)=h(x') implies h(T(x))=h(T(x')) for all x,x'.

S is unique, and for every integer n>=0, h(T^n(x))=S^n(h(x)).

Proof: necessity follows by applying S to equal codes. For sufficiency define S(z) as the unique h(T(x)) for any preimage x. The fiber-equivalence condition makes this well-defined and its output attained; it also proves uniqueness. The iterate identity holds at zero. Applying hT=Sh to T^n(x) and using induction proves it at n+1. Empty X gives the unique empty map and vacuous identities. This is an all-set, all-finite-time proof, not an extrapolation from sample horizons.

The condition preserves the equivalence relation between states; it does not require each individual fiber to remain fixed. For a prescribed target S, the actual equation hT=Sh must hold: existence of some autonomous quotient is insufficient. With a declared integer clock scale k>=1, replace T by T^k to obtain h(T^(kn)(x))=S^n(h(x)); no intervening-time identity is implied.

For a family of actions/interventions T_a and a declared action map tau, equations hT_a=S_(tau(a))h for every allowed a imply exact transfer along every finite matched action sequence, by repeated composition. This does not establish the physical equivalence or availability of those actions, or cover unmatched target actions. Relevant observation/output maps must also commute with h. Unforced dynamical agreement alone is not causal transfer.

## Approximate transfer at every horizon

Let Z be a metric space, h:X->Z, T:X->X and S:Z->Z. Assume the defect d(h(T(x)),S(h(x)))<=eta for every admitted x along its trajectories, and S is L-Lipschitz. Start z_0 in Z with d(z_0,h(x_0))<=epsilon; evolve z_(n+1)=S(z_n), x_n=T^n(x_0). Then

    E_n=d(z_n,h(x_n)),
    E_(n+1)<=L E_n+eta,
    E_n<=L^n epsilon+eta sum_(j=0)^(n-1) L^j.

Proof: insert S(h(x_n)), apply triangle inequality, Lipschitzness and the defect bound; solve the recurrence by induction. A K-Lipschitz downstream target has error at most K E_n. Arbitrary discontinuous targets have no such guarantee.

For L<1 this gives E_n<=L^n epsilon+eta(1-L^n)/(1-L), hence uniform bound max(epsilon,eta/(1-L)). For L=1 the bound is epsilon+n eta; for L>1 it may grow exponentially. Contractivity is sufficient for this uniform certificate, not necessary for every particular system. Additional structure can improve the bounds.

A sharp drift obstruction: on the real line take h identity, T(x)=x, S(z)=z+eta, z_0=x_0, eta>0. One-step defect is exactly eta, both systems have the same state geometry, and E_n=n eta. Small one-step mismatch alone cannot certify a fixed tolerance at every horizon.

Even identical two-point state spaces can disagree exactly: source dynamics fix both points, target dynamics swap them. No bijection h satisfies hT=Sh, because source points are fixed and target points are not. Common geometry or vocabulary alone does not establish dynamical transfer.

## Scientific meaning and established prior

The constructive opportunity is an obtainable nontrivial h with source-faithful commutation, intervention and observation equations plus stable error and cost bounds. Defining an abstract quotient from already-known behavior does not construct that scientific bridge.

Horstmeyer and Atay (2016), *Characterization of Exact Lumpability for Vector Fields on Smooth Manifolds*, DOI https://doi.org/10.1016/j.difgeo.2016.06.001, primary manuscript https://arxiv.org/pdf/1607.01237, Section 2.2: a projected vector field must factor through the projection, yielding flow commutation. This is a smooth continuous-time version of the established quotient principle, not a theorem invented here.

Rubenstein et al. (2017), *Causal Consistency of Structural Equation Models*, primary manuscript https://arxiv.org/pdf/1707.00819, Section 4.3: exact causal transformations preserve interventional laws under a compatible intervention map. Our matched-action identities above make the intervention requirement explicit but do not replace those probabilistic causal assumptions or establish a new causal-transformation theorem.
