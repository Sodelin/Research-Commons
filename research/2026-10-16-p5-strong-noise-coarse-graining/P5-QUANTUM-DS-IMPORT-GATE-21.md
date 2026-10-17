# P5: a new block-mixing source does not supply the Redfield response

17 October 2026, 02:29 UTC. dot (OpenAI), working with Nolan.

Status: bounded primary-source applicability check and elementary representation obstruction. Local research record, not an independently reviewed new P5 theorem, a physical instability result or a novelty claim.

## Source and precise mismatch

The newly inspected primary source is Rouzé and Stilck França, *Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions*, [arXiv:2610.03578v1, 2 October 2026](https://arxiv.org/pdf/2610.03578v1). The source check covered the construction in equations (1.1)–(1.3), the channel definition in Section 2.2, Theorem 4.4 on printed page 26, Theorem 6.1 on printed page 47, and the proof's explicit channel-contractivity use on printed page 42. This is not a full independent audit of the 67-page proof.

The source constructs Gibbs-preserving CPTP block updates using quantum belief propagation and a KMS Lindblad completion. Theorem 4.4 concerns their positive-rate mixture. Theorem 6.1 varies their Hamiltonian, not an arbitrary nonpositive generator. Its premises include finite range, polynomial volume growth, bounded local dimension, bounded-size/diameter labelled blocks, fixed positive rates and bounded internal times, a uniform positive reference DS margin, and equation (6.2)'s polynomial bounds on neighbourhood size and weighted block incidence. Its proof uses channel contractivity. These constructed dynamics are not identified with the actual full-filter Redfield generator. Larger blocks do not establish that identification.

## Exact obstruction to a direct positive-update representation

In any fixed finite volume, suppose a generator R could be written

    R = sum_B a_B (Phi_B − id),

where a_B>=0, each Phi_B is CPTP, and the finite total rate a=sum_B a_B is positive. Then P=a^−1 sum_B a_B Phi_B is CPTP and

    exp(tR)=exp(−at) sum_(r=0)^infinity (at)^r P^r/r!.

Every partial convex sum is completely positive, the series is norm convergent, and its coefficients sum to one. Thus exp(tR) is CPTP for every t>=0. The case a=0 is the identity semigroup. Adding a Hamiltonian commutator does not evade this conclusion: the finite-dimensional product formula composes these channels with unitary channels and retains complete positivity and trace preservation.

The already accepted physical two-site Redfield example has orthogonal unit vectors psi,phi and P=|phi><phi| satisfying

    <psi|R*(P)|psi> = −d < 0.

Hence <psi|exp(tR*)P|psi>=−dt+o(t)<0 for sufficiently small positive t. This forbids the displayed exact CPTP-update representation for that admitted member, irrespective of chosen block size. The source of this witness is the [reviewed obstruction packet](https://github.com/Sodelin/Research-Commons/blob/44ace19b8deed339e992c4ca6a6e07ca8c152bbe/research/2026-10-16-p5-strong-noise-coarse-graining/P5-REDFIELD-SITE-OSCILLATION-OBSTRUCTION-05-v2.md).

**Fresh parameter check of that inherited witness.** Its static Hamiltonian is H=J Z_1 X_2 with h=J, neighbourhood size m=2 and multiplicity nu=2. Its six independent on-site Pauli channels use Phi(s)=c_b/(2a) sech[pi(s+i a/2)/(2a)], with fixed a,c_b>0. The accepted thermal covariance has beta=a, tauB=2a/pi, gamma=2 sqrt(2)c_b/pi and b0=pi/(4 sqrt(2)). Its strong-noise margin is

    g=8 b0 gamma−J(2+192 gamma tauB).

Thus g>0 for 0<J<8 b0 gamma/(2+192 gamma tauB). The same source proves r(J)>0 and D(J)!=0 throughout another sufficiently small positive-J interval, using Re Phi(s)>0 and dominated convergence. Intersect these two intervals. This preserves the actual nonzero negative derivative and the strong-noise condition simultaneously. There is no growing neighbourhood or high-degree graph. Further strict smallness thresholds, if needed for the previously accepted finite-order estimates, can also be met by decreasing J. The bath's positive-type/KMS verification is inherited from its accepted proof, not rederived in this pass.

The exclusion is for this witness family and hence for a purported exact positive-update representation covering every admitted member that includes it. It does not assert that every Redfield generator is nonpositive.

This is an elementary incompatibility of a proposed exact import. It does not exclude an auxiliary CPTP reference followed by a separately proved signed-error estimate, a nonpositive extension of the block argument, or the original P5 conclusion. No such extension is supplied here. It also does not convert nonpositivity into a fixed-support instability or a lower bound on the coarse-graining error.

## Strongest remaining direct obligation

The accepted exact on-site reference, finite-order full-filter estimates and signed covariance diagnostic remain usable. The actual comparison remains finite-window GKSL versus full infinite-filter Redfield, for each fixed initial support, arbitrary initial states, and uniformly over physical time and total volume in the declared physical class.

The sufficient response estimate is still

    integral_0^infinity sum_(i,a) ||[sigma_i^a, exp(t R*) O_X]|| dt
      <= (C_X/gamma) ||O_X||,

with C_X independent of total volume. The strongest direct proof route presently identified is a rooted expansion or equivalent invariant estimate that retains whole products, their covariance and the full virtual-time unitary filters through arbitrarily many insertions. The on-site reference can supply decay; it does not license damping individual factors independently. A finite-order calculation, small-system polymer theorem or a bound on a time-integrated operator after cancellations does not imply this integral of nonnegative commutator norms.

The earlier long-filter amplification idea was also checked against the saved attempt10: it already requires an admitted static bounded-strength, bounded-neighborhood qubit Hamiltonian generating the harmful profile with sufficient amplitude after bath integration. No new such supplier was recovered here. Repeating that heuristic would add no evidence.

The fresh source above therefore closes one previously unchecked possible import. It produces no improved full-class P1 bound and no P5 closure. P1's latest source audit22 and hard-family gate23 were reread; their exact locality/statistical-experiment mismatches and the accepted lower-versus-upper gap are unchanged. No numerical or proof-assistant execution, new physical model or alternative comparator was introduced.
