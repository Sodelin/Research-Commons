# Prior-work audit 06: a published Bayesian-network lower bound inside the Gibbs class

Date: 2026-10-16. Prepared by dot for Nolan. Status: source-checked prior import with an explicit hand-derived Gibbs embedding; not Lean-verified and not an independently reviewed new theorem. No novelty claim. P1 remains open.

## Result and attribution

Bhattacharyya, Canonne and Yang, *Independence Testing for Bounded Degree Bayesian Networks*, NeurIPS 2022, Definition 2.2 and Lemma 2.3, already supply a random pointer-controlled matching prior whose iid samples require Ω(2^{d/2} n/ε²) to distinguish from uniform, for d₀≤d≤c log n. Their displayed density on page 6 uses pair factors 1±4ε/√n. Their stronger independence conclusion is unnecessary here.

Primary: https://papers.nips.cc/paper_files/paper/2022/file/611252d40f23c8b57a8bc9ffb577419b-Paper-Conference.pdf

The following exact embedding imports that established statistical lower bound into P1. It improves the previously recorded locality dependence; its statistical hardness belongs to BCY2022.

## Explicit Gibbs admission and separation

Use d−1 pointer bits z and N=n−d+1 child bits, with N even. Put m=N/2 and choose a matching M on the children. For each e∈M choose a function f_e:{±1}^{d−1}→{±1}; its values at all pointer strings are independently signed in the BCY prior. Let t=4ε/√n and a=atanh(t). Define

H(z,x)=−(a/β) Σ_{e={i,j}∈M} f_e(z)x_i x_j.

Conditional on z, the partition function of the child system is 2^N cosh(a)^m, independent of z and of all signs. Thus the pointer is exactly uniform, and the full density relative to uniform is

P(z,x)/U(z,x)=∏_{e={i,j}∈M}(1+t f_e(z)x_i x_j).

This is precisely the supplier's density, after changing bits to spins. Expand each f_e in the Walsh basis. Every coefficient has absolute value at most 1. Each resulting Pauli term contains its own distinct child pair and a subset of the pointer sites, so different edges do not collide; weight is at most d+1. The identity coefficient is zero. If β≥atanh(4ε/√n), all Hamiltonian coefficients have absolute value at most 1. No bounded-degree condition is needed: pointer sites can occur in many terms.

Here is a direct uniform-separation check avoiding any conditioning of the prior. For a fixed pointer, the m pair parities are independent fair signs under U. Write L−1=tS+W, where S is their signed sum and W contains terms of degree ≥2. Orthogonality gives
E W²=(1+t²)^m−1−mt²≤b⁴, b=t√m,
when b²≤1. Also E|S|≥√(m/3), by the second/fourth-moment interpolation inequality. Therefore E|L−1|≥b/√3−b². For d≤n/3, m≥n/3 and b²≤8ε². For 0<ε≤1/32 this is at least 4ε/3−8ε²>ε. Averaging over the uniform pointer preserves the same bound. All alternatives, not merely most of them, are at full trace-norm distance >ε from the maximally mixed state.

Set k=d+1. Consequently the published prior supplies Ω(2^{(k−1)/2} n/ε²) copies in the regime d₀≤k−1≤c log n, n sufficiently large, 0<ε≤1/32, and β≥atanh(4ε/√n). Parity adjustments use a uniform spectator. Fixed positive β is eventually admissible. Constants come from the published lower bound; no claim is made outside that regime.

## Measurement and two-source transfer

Every state in this construction is diagonal in one known basis. For any collective POVM, its outcome law on any tensor product of these states is a stochastic function of the full basis strings. Drawing those strings and applying the POVM's diagonal response probabilities reproduces the quantum experiment. This also covers adaptive choices and a worst-case total copy budget.

A two-unknown equality tester includes the subproblem with its first state fixed to uniform. Uniform reference copies can be generated independently for free in the classical simulation. An algorithm using at most T copies in total uses at most T informative target samples. Hence the imported lower bound applies to the total-copy convention, including collective quantum measurements. It does not use a single-copy restriction.

## What this does and does not establish

The separate reviewed q≥3 hidden-hypermatching construction gives Ω_q(n log n/ε²) for fixed q and its pointwise temperature condition:
https://github.com/Sodelin/Research-Commons/blob/baacfd78289f1b1b6c922eb172d5e32c206cdef3/research/2026-10-16-g6-gibbs-certification/HYPERMATCHING-CANDIDATE-03.md

These are separate lower-bound families, so their bounds can be maximized where both are admitted; they cannot be multiplied. BCY2022 does not by itself establish the log n factor. The bounded prior search so far has not identified an exact published iid hidden-hypermatching n log n predecessor. This is not a novelty determination. Boolean Hidden Hypermatching communication/streaming results have a different input model and are not interchangeable with iid full-string sampling.

The general noncommuting two-unknown P1 upper bound remains supplied by Bluhm et al., Theorem 17:
https://arxiv.org/html/2603.29809v1
No bounded-degree Bayesian-network upper bound is asserted for general k-local Gibbs states: neither a bounded-indegree DAG nor a classical joint sample of all noncommuting observables is supplied by k-locality. Closing that statistical/measurement gap is still the main task.

## Addendum: independent review and exact locator (2026-10-16)

The embedding and transfers above now have a scoped independent hand-proof PASS. The supplier's full statistical lower-bound proof remains an attributed import, not independently reproved here. Exact review:
https://github.com/Sodelin/Research-Commons/blob/7ced6c47731396aad689718cfd25c66c1797149f/research/2026-10-16-g6-gibbs-certification/BCY-GIBBS-IMPORT-INDEPENDENT-REVIEW-09.md

Correction to the earlier locator: the displayed source density is on PDF page 7 (zero-based page index 6). For spectator padding, choose n_active in {n_total,n_total−1} with n_active−d+1 even and evaluate the exact temperature threshold and degree regime at n_active. Only the asymptotic rate replaces n_active by n_total. The earlier body is retained as the historical source-check record; this addendum governs those two clarifications. No Lean verification or general P1 closure is claimed.
