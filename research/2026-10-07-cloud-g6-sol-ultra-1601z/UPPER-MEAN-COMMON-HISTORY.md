# One common history law for numerical upper means

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 20:37 UTC.
Status: HAND-DERIVED ARGUMENT; INDEPENDENT REVIEW PENDING; NOT LEAN VERIFIED.

This extends the [actual-mean common-history argument](RESIDUAL-PROGRAM-COMMON-LAW.md)
to numerical upper means. It addresses that note's explicitly remaining
upper-mean composition obligation. The unchanged physical rate bank,
source operations, and correlated old state are essential. This is not
a new biological retiming or a computable oracle for arbitrary reals.

The numerical approximation is the original residual-lumped rule in the
[Astra count/source handoff](../2026-10-07-astra-g6-source-poisson-prefix-124833z/HANDOFF-COUNT-SOURCE.md).
The one-step error order is already established by the checked
[MeanEnclosure](sources/UnifiedLean/G6/MeanEnclosure.lean) triangle proof.
The contribution here is an explicit common subprobability that permits
whole-program/history composition using the existing domination machinery.

## An explicit common count law

Fix 0 ≤ a ≤ b, a natural cutoff K with 2b ≤ K+2, and put

    Sx = Σ(k=0..K) x^k/k!,    Ub = Sb + 2 b^(K+1)/(K+1)!,
    ρb = Sb/Ub,              δb = 1−ρb,              c = Sa/Ub.

Let Pa be Poisson(a), Qa its normalized count prefix through K, and Lb the
residual rule at b. Its coefficients are

    Lb(k) = 1[k≤K] b^k/(k! Ub) + 1[k=0] δb.

All these are probability laws. The verified Taylor enclosure gives
exp(b) ≤ Ub; exp(a) ≤ exp(b). Also 1 ≤ Sa ≤ Sb ≤ Ub, so 0 < c ≤ 1.
For every natural k, BOTH Pa and Lb dominate c Qa. If k > K, the common
coefficient is zero. If k ≤ K, it equals a^k/(k! Ub), which is at most
exp(−a) a^k/k! and at most b^k/(k! Ub). The residual addition at zero is
nonnegative. The proof uses no division by a or b, so a=0, b=0 and K=0
are retained, including the usual 0^0=1 count-zero term.

The common normalized reference is Qa, at the ACTUAL mean. It is not Qb.
This distinction is what permits the two dominations; there is no claim
that Pa dominates a positive multiple of the full upper-mean prefix Qb.

## Its missing mass has the required computable bound

For k≥1, the finite geometric identity and 0≤a≤b give

    b^k−a^k = (b−a) Σ(j=0..k−1) b^(k−1−j) a^j
             ≤ (b−a) k b^(k−1).

Divide by k!, sum over 1≤k≤K, and include the identical count-zero terms:

    0 ≤ Sb−Sa ≤ (b−a) Σ(j=0..K−1) b^j/j! ≤ (b−a) Sb.

For K=0 the difference is zero and the empty sum is zero. Consequently

    1−c = (Sb−Sa)/Ub + δb
        ≤ ρb (b−a) + δb
        ≤ (b−a) + δb.

An available enclosure width η≥b−a therefore bounds this by η+δb.
Only the certificate b, K and η must be available for this numerical
bound. The proof-reference Qa and c may depend on the actual real a;
they are not quantities the numerical algorithm must compute.

## Bind the same source and compose the full history

For an interval, a=globalClockRate(r)*duration is the actual mean. Bind
all three count laws through the SAME sourceIteration N r k s, uniformly
for every entering Code s. The two coefficient dominations yield

    c Qi(s,d) ≤ Pi(s,d),       c Qi(s,d) ≤ Li(s,d).

Here Qi is the actual-mean normalized finite source prefix; Li uses upper
mean b count weights and retains the original physical rate bank r.
At each physical boundary use the original sourceProgramStep unchanged
in both laws and in Q, with c=1. COMMON retains its original per-locus
register; INDEPENDENT uses the same actual current-root routing.

For each finite operation occurrence i choose bi≥ai, Ki satisfying
2bi≤Ki+2 and ηi≥bi−ai. The existing two bind-domination inductions give
both the actual program and its numerical residual program the same
common normalized reference program, with mass C=Πi ci. Thus

    TV(P,L) ≤ 1−Πi ci ≤ Σi(1−ci) ≤ Σintervals (ηi+δbi).

Apply the SAME induction to historyLaw, retaining every endpoint with
Fin.cons. This controls the joint full endpoint vector, not a product of
marginal histories. A single initial PMF on correlated (Past,Code) can be
integrated while carrying the same Past label. One deterministic finite
joint readout then has the identical bound. There is no factor for the
number of coordinates, states, or source panels. A repeated operation is
counted as a separate occurrence in the product and sum. Here panels must
be coordinates of that ONE joint readout of the same history. Separately
executed experimental programs each contribute their own operation
occurrences; no free bound for products of separate experiments is claimed.

An arbitrary Past PMF is a representation-level premise. Identifying it
with the physical calendar/bin law remains the separately reviewed actual
calendar consumer. A general continuous past does not become a PMF merely
by being named Past. Changing the physical rate bank requires another
error bound; this proof only changes the count weights.

## Implementation boundary and next action

The checked providers inspected for this argument are
TaylorCertificate.exp_le_taylor_enclosure, SourcePrefix.prefixCount_real,
ResidualPrefix.residualCountReal_coefficients, and the existing
ProgramPrefix/HistoryPrefix scaled-bind and retained-history constructions.
They occur in the [independently accepted 150-module selection](../2026-10-07-cloud-independent-auditor-1616z/LITERAL-MEAN-RESIDUAL-VERIFIED-COMPLETE-REVIEW.md).
This new composition statement is a hand proof, absent that frozen build.

Next: independent review, then implement the finite polynomial difference,
upper-mean common count domination and source/history specialization as an
additive consumer. Reuse the pending residual-vector PMF wrapper; preserve
its exact-mean theorem rather than silently changing its premises.
Executable source tables, effective arbitrary-real/rate-bank inputs,
actual timed readout identification, positive reconstruction and the full
G6 endpoint remain separate obligations.
