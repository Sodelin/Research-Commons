# The distinct residual-lumped source approximation

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 19:22 UTC.
Status: HAND-DERIVED ADAPTER; INDEPENDENT REVIEW PENDING; LEAN DRAFT UNCHECKED.

This translates the residual alternative already stated in
[Astra's count/source handoff §3](../2026-10-07-astra-g6-source-poisson-prefix-124833z/HANDOFF-COUNT-SOURCE.md).
The classical common-subprobability argument and the earlier hand result
retain their attribution. The new contribution is a concrete adapter to the
current checked source definitions, with a separate
[Lean draft](proof-drafts/ResidualPrefix.lean). It does not change the
[normalized-prefix certificate](TAYLOR-CERTIFICATE.md).

## Exact law and proof

Fix one original admitted source N, sample carrier, positive physical rate
bank r, entering Code s, nonnegative duration t and cutoff K. Set
a=globalClockRate(r)·t, t_k=a^k/k!, S=Σ_{k≤K}t_k, T=t_{K+1}, U=S+2T.
Assume the exact ratio condition K+2≥2a. Existing TaylorCertificate proves
exp(a)≤U. Existing SourcePrefix defines Q by binding the actual Poisson law
conditioned on k≤K through the SAME sourceIteration N r k s. It proves
P(d)≥μQ(d), where P is sourceTimeKernel N r t s and μ=exp(−a)S.

Let ρ=S/U and δ=1−ρ=2T/U. Since S≥1 and T≥0, U>0,
0≤ρ≤1 and ρ≤μ. Define Z=sourceIteration N r 0 s and

    L(d) = ρ Q(d) + δ Z(d).

L is nonnegative and sums to one. P and L both dominate the SAME finite
vector c(d)=ρQ(d), whose mass is ρ. The already checked common-subprobability
theorem therefore gives TV(P,L)≤1−ρ=δ. No division by δ or 1−μ occurs;
a=0 and K=0 are included. Count zero is the original zero-step row, with
its original entering state, subtrees and register, not a new biological
event or a replacement source.

The count coefficients are exactly

    qL(k) = 1_{k≤K} t_k/U + δ·1_{k=0}.

Indeed ρ·(t_k/S)=t_k/U on the retained prefix, and k=0 is always in that
prefix. Thus these are the residual-lumped coefficients in the original
reference backend, whereas Q uses t_k/S. The draft proves this coefficient
identity separately; it does not relabel the normalized law as residual.

For one finite JOINT endpoint readout h, apply the same argument to the
actual mapped kernels. P pushed through h dominates ρ times Q pushed
through h, and the residual row is Z pushed through h. The error remains
δ without a state-count or coordinate-count factor. In particular all
coordinates retain one N, one physical parameter bank and one entering
state/register. No product of same-locus marginal distributions is used.

## Exact implementation scope

The draft defines residualMass, residualCountReal, residualVector and
residualSourceVector. It contains nine named reports: mass bounds,
deficit identity, comparison with the actual prefix mass, vector
nonnegativity and normalization, common-subprobability TV, exact count
coefficients, actual source TV and one actual joint-readout TV bound.
The residual distribution is represented by its real probability-vector
coordinates with proved nonnegativity/normalization, not yet by a new PMF
constructor or executable table evaluator.

All stochastic inputs are the existing actual PMFs; the final source
theorems derive domination from SourcePrefix/Conditioning. They do not
take an approximation assertion as a field of a source structure. For
rational a the displayed coefficients and δ are rational; the existing
RationalCertificate cutoff accepts the SAME ratio/error predicate. A
dedicated rational residual evaluator and its executable correspondence
are not established by these statements.

The original hidden physical parameters still range over arbitrary reals.
Computable-real enclosure integration, composition of residual programs,
backend executable correctness, the actual calendar/bin-history readout
and the full G6 source-to-master endpoint remain separate obligations.

## Preservation and verification

The original draft is saved before any compiler request. Its hash is to
be frozen in the publication/review receipt. Shared providers and the
currently running literal-prefix build are unchanged. Routine elaboration
repairs must use a separate derivative with actual receipts; this note
claims no compiler outcome.
