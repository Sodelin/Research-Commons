# General P1 gap audit 07: priors, admission conventions, and a failed upper-bound shortcut

Date: 2026-10-16. Prepared by dot for Nolan. Status: primary-source audit plus a complete elementary hand calculation. No Lean verification, experimental evidence, novelty claim, or closure of P1.

## Exact dimension convention for prior import 06

The displayed theorem in PRIOR-IMPORT-06.md uses an active dimension n with n−d+1 even. If a uniform spectator is appended, call the ambient dimension n_total and retain n_active in the exact temperature threshold β≥atanh(4ε/√n_active). Only the asymptotic rate may replace n_active by n_total. The padding sentence in note 06 must not be read as retaining the exact threshold with the larger ambient dimension.

Source and full import:
https://github.com/Sodelin/Research-Commons/blob/315dd70ed55367a0963511847326e4d936ad8f25/research/2026-10-16-g6-gibbs-certification/PRIOR-IMPORT-06.md

## What the further primary-source audit establishes

1. Canonne and Yang, NeurIPS 2024, Theorem 1.2 / 3.1, give a classical bounded-indegree Bayesian-network identity tester with a fully described reference. Its stated sample bound is Õ(2^{d/2} n^{3/2}/ε²+n²/ε⁴). This does not supply the original two-unknown noncommuting Gibbs tester. A k-local Hamiltonian does not furnish their DAG admission.
https://proceedings.neurips.cc/paper_files/paper/2024/file/eff4231d13b71a2859ce90242ed6ad8d-Paper-Conference.pdf

2. Bluhm et al., Theorem 17, explicitly include the two-unknown-copy experiment and give O(β² n^{2k}3^k k log(n/δ)/ε⁴) single-copy Pauli measurements. The equality-versus-full-trace-norm problem follows by rescaling the far threshold. Its proof uses an ℓ∞ discrepancy among low-weight Pauli expectations at scale ε²/(β n^k).
https://arxiv.org/html/2603.29809v1

3. The exact iid hidden-hypermatching n log n prior remains unresolved after bounded searches of Bayesian-network independence/uniformity testing, higher-order Ising/Markov models, and hidden-hypermatching literature. Boolean Hidden Hypermatching communication and streaming results use different experiments. No assertion of absence or novelty follows from this search.

For fixed k≥3, fixed positive β, constant failure probability, and the feasible small-ε/asymptotic regime of the reviewed family, the recorded original-problem gap remains at least
Ω_k(n log n/ε²) versus O_k(β² n^{2k} log n/ε⁴).
When k grows, the BCY prior import and the separately scoped noncommuting block lower bound have additional locality/temperature/measurement conditions; combine only by a maximum on their common admitted domain. Never multiply their rates. The displayed supplier upper is stated with k constant, so this audit does not claim uniform-in-k hidden constants.

## An explicit obstruction to dimension-free covariance

A tempting route would replace coordinatewise estimation by a quadratic test of the entire sufficient-statistic vector and assume that its covariance is bounded independently of n. The original coefficient bound does not imply that assumption.

Take β=1 and the admitted 2-local diagonal Hamiltonian
H(x)=−Σ_{i<j}x_i x_j, x_i∈{−1,+1}.
Every pair coefficient is −1. There is no degree restriction in P1. If r spins differ from the all-plus string, its energy exceeds the ground energy by 2r(n−r). The only ground strings are all-plus and all-minus. Consequently the Gibbs probability η_n of all other strings obeys
η_n ≤ 2^{n−1} exp(−2(n−1)) → 0.
Indeed every nonground string has energy gap at least 2(n−1), there are at most 2^n of them, and the partition function includes the two ground contributions.

Let F be any collection of L distinct odd-cardinality nonempty subsets, each of size at most k, and set φ_S(x)=∏_{i∈S}x_i. Spin-flip symmetry gives Eφ_S=0 exactly. For u=(1,…,1)/√L,
uᵀ Cov(φ) u = E[(Σ_S φ_S)²/L] ≥ (1−η_n)L,
because on either ground string all odd parities agree. Hence the covariance operator norm is at least (1−η_n)L. With all singleton parities L=n already diverges. With all odd Z-parities of weight≤k, L=Σ_{j≤k, j odd} binom(n,j). The same Hamiltonian is admitted for every k≥2.

This disproves only the automatic covariance premise. It does not prove that this family is hard to certify, and does not rule out covariance-adaptive, localized, or other nonlinear tests.

## Precise next lower-bound obligation

A stronger possible route is a dense random signed degree-k diagonal Hamiltonian, rather than another disjoint-block family. Let p=binom(n,k) and
F_s(x)=a Σ_{|S|=k} s_S φ_S(x),   P_s(x)=exp(F_s(x))/(2^n Z_s),
Z_s=E_U exp(F_s),   H_s=−F_s/β,
with a of order ε/√p and one sign vector s fixed before all samples. Coefficient admission is a≤β.

To turn the heuristic √p/ε² testing scale into a theorem, one needs both:
- a prior concentrated on states with ||P_s−U||_1≥ε, with quantitative constants;
- a bound below the testing threshold for
E_{s,s'}[(E_U exp(F_s+F_s')/(Z_s Z_s'))^T]−1
when T is of that order.

This identity is exact. The missing estimate is not supplied by orthogonality alone: partition functions fluctuate and parity products have cycle relations. Replacing exp(F_s)/Z_s by 1+F_s loses exact Gibbs admission because its logarithm generally has higher-weight terms. A Gaussian local-asymptotic analogy is not a finite-n proof. No dense-family lower bound is claimed here.


## Correction: measurement-specific upper bounds, 16 October 2026

The earlier displayed “original-problem gap” is superseded for unrestricted collective measurements. It remains a record of the applicable efficient single-copy Pauli supplier, not a best-general-copy upper. Theorem 16's exponential-time learner has the same n^(2k)/epsilon^4 copy scaling; removing computation constraints alone does not improve that theorem's rate.

A separate, independently hand-reviewed composition of the Gibbs covering net with Badescu–O'Donnell Corollary A.4 gives the full two-unknown collective upper
O((M log(2+beta M/epsilon)+log(1/delta))/epsilon^2),
where M=sum_(j=1)^k 3^j binom(n,j), with TOTAL copies across both sources. It uses a collective threshold-decision projector for fixed paired Helstrom effects and potentially enormous computation. The usable upper is the minimum with prior applicable bounds; superiority is not uniform in beta.

Thus unrestricted collective copy complexity, adaptive single-copy copy complexity, and efficient-time certification are three separate questions. For fixed k>=3 and fixed positive beta in the reviewed lower-family regime, the currently recorded collective gap is Omega_k(n log n/epsilon^2) versus O_k(n^k log(2+beta n^k/epsilon)/epsilon^2), at constant failure probability. The two-unknown adaptive single-copy experiment retains Theorem 17 as an applicable upper. No exhaustive best-known claim, optimality, novelty, or P1 closure is made.

Exact attributed composition, finite-precision construction and total-copy accounting:
https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md
Independent hand review of the clarified source:
https://github.com/Sodelin/Research-Commons/blob/bf1d9a0e98b99eaf0a7d229de640a345210b78d4/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-UPPER-13-INDEPENDENT-REVIEW.md

The prior body is preserved above as dated history. This addendum corrects its upper-bound scope; its covariance obstruction and exact normalized lower-bound obligation are unaffected.

## Accepted dense lower bound and updated gap, 16 October 2026

The dense lower-bound obligation above is now supplied at scoped independent hand-proof level by note 14. Its proof conditions the original sign prior on individual normalization events at amplitudes b and 4b. A finite convex tangent extension agrees with the paired log partition function on every retained pair. Its gradient bound and one-sided entropy concentration control the retained mixture without reintroducing the divergent unconditioned moment.

Exact scope: fix integer k>=3, D=binom(n,k) sufficiently large depending only on k, 0<epsilon<=1/(128*9^k), and beta>=8*3^k*epsilon/sqrt(D). Then equality versus full trace-norm separation epsilon in the original two-unknown bounded-Pauli-coefficient class requires Omega_k(sqrt(D)/epsilon^2) worst-case TOTAL copies at error<=1/3, even with collective measurements and adaptive source allocation. Expected stopping-time budgets are not covered. Fixed positive beta eventually satisfies admission. This is not a uniform growing-k claim.

Preserved proof:
https://github.com/Sodelin/Research-Commons/blob/20b87867bc1f6687455221358211890588ba4034/research/2026-10-16-g6-gibbs-certification/DENSE-CONVEX-TRUNCATION-LOWER-14.md
Independent complete hand review:
https://github.com/Sodelin/Research-Commons/blob/816c3e66f1de3f35a5bc19fce1ceda2ef16f2d96/research/2026-10-16-g6-gibbs-certification/DENSE-LOWER-14-INDEPENDENT-REVIEW.md
Readable result:
https://docs.google.com/document/d/1xAB16V_01daJzAWHVOYEPEOv0_UyuLMKVFjHVeAaHew/edit?tab=t.t14a2fheg3v7

At fixed k>=3 and fixed positive beta in this small-epsilon regime, the updated recorded collective gap is Omega_k(n^(k/2)/epsilon^2) versus O_k(n^k log(2+beta n^k/epsilon)/epsilon^2), with the usable upper minimized against other applicable bounds. All independently admitted lower families combine by maximum, never multiplication. The k=3 dense consequence is n^(3/2)/epsilon^2. General P1 remains OPEN. No Lean verification or numerical experiment is claimed.

### Focused prior audit accompanying acceptance

The combined result's historical novelty remains unresolved. A focused search on 16 October covered dense Ising uniformity/identity testing, higher-order Ising/Markov models and high-dimensional exponential-family testing. It did not identify an exact previous statement with all of note 14's hypotheses. This is bounded negative evidence, not a novelty certificate.

Daskalakis, Dikkala and Kamath, Testing Ising Models, ECCC revision 2 (2017), Section 8 Theorem 19, proves a linear-in-n lower bound with symmetric-KL separation using random matchings; Section 1's dense-construction discussion is contextual prior. That pair-interaction theorem does not itself give the degree-k n^(k/2) trace-distance statement. A large symmetric-KL distance cannot simply be converted into the required trace-distance lower bound.
https://eccc.weizmann.ac.il/report/2017/006/revision/2/download/

Jin, Wang and Lu (ICML 2020) study simple zero-field ferromagnetic pairwise models and graph-structure detection, including oracle-model computational bounds. Their primary abstract's scope does not establish the signed higher-order iid Gibbs claim:
https://proceedings.mlr.press/v119/jin20g.html

The BCY2022 Bayesian-network prior import is already retained separately with its exact Gibbs embedding and admission limits. Standard Rademacher-mixture, Fourier, hypercontractive, convex-extension and entropy methods are credited as such. Further citation-chain and general testing-method comparison remains necessary before any claim of originality.

The next substantive target is the optimal general copy gap: an applicable sharper collective upper or a stronger admitted quantum lower, with single-copy access and runtime kept distinct. Earlier dated bodies remain preserved for provenance.

## Varying-beta correction from established closeness hardness, 16 October 2026

The fixed-beta gap just recorded must not be read as predicting a beta-uniform square-root-D upper. The independently hand-reviewed Hamming-shell import supplies an obstruction at high inverse temperature.

For n>=k>=2, D=binom(n,k)>=2 and 0<epsilon<=1/4, put L=max{D^(2/3)/epsilon^(4/3),sqrt(D)/epsilon^2}, lambda=n log 2+log(100L). If beta>=n lambda+D log(4D), the original two-unknown problem needs Omega(L) worst-case total copies, including collective measurements and adaptive source allocation. The reduction imports Chan, Diakonikolas, Gregory Valiant and Paul Valiant's SODA2014 Theorem1.1. It smooths arbitrary alphabet distributions, uses nonnegative degree-k monomials on the Hamming-weight-k shell, and a quadratic penalty with explicit leakage. It preserves null equality exactly and uses only sample access in the contradiction.

Exact proof:
https://github.com/Sodelin/Research-Commons/blob/b2df79fbfd8a294c001f91a8228b309cd1630fe0/research/2026-10-16-g6-gibbs-certification/HAMMING-SHELL-CLOSENESS-IMPORT-15.md
Independent review:
https://github.com/Sodelin/Research-Commons/blob/efba9ef35ee1eb52a77d7587d2747c23bc9bbff1/research/2026-10-16-g6-gibbs-certification/HAMMING-SHELL-15-INDEPENDENT-REVIEW.md
Classical primary supplier:
https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf

At fixed k>=3 and constant epsilon, beta=O_k(n^k log n) suffices for the n^(2k/3) lower. This excludes an O_k(sqrt(D)/epsilon^2) upper uniform in beta, even allowing polylogarithmic factors. It does not strengthen the fixed-beta theorem. Fixed-beta optimal copies, varying-beta optimal copies, adaptive single-copy measurements and efficient implementation remain distinct unresolved targets. The existing collective upper13 remains valid. No novelty, Lean verification, experiment or P1 closure is claimed.
