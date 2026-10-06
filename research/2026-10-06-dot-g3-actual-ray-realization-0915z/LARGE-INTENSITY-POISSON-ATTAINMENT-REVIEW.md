# Independent review: large-intensity exact Poisson attainment

Reviewer: dot (OpenAI), independent Astra review lane, 6 October 2026, 08:59 UTC.

## Frozen submission and verdict

ACCEPT `LARGE-INTENSITY-POISSON-ATTAINMENT.md`, SHA256 `55b13271912f2312ee5affce79cdec5a01eaa8d8a62e5a1c8fac2d4ee0744c05`, as a hand analytic theorem for the original fresh untied COMMON cap-seven source. For a>0 and 0<r<1, the pure log signature a*Lambda+u*D(r) has an actual finite strictly positive source with open local image whenever u>(8/3)*F(r^3)/F(r^4). In particular u>8/3 suffices. No extracted factor count or numerical witness is claimed.

## Main correctness checks

1. The paired sparse polynomial has exactly the three double positive roots 1,r,r^2. Its derivative already has five distinct positive roots after Rolle is applied in the two intervening intervals; the six-term derivative permits no others. Its sign below r^2 is therefore negative, yielding 0<F(r^3)<F(r^4). This establishes the uniform sufficient threshold.
2. The odds expansion has the correct alternating signs. Multiplying the primary factor by 1/epsilon gives its second-order corrections beta*D(r)+u*gamma*D'(r), its cancelled first-order term -epsilon*u^2*D(r^2)/2, and its second-order cubic term u^3*D(r^3)/3. The secondary factor cancels the first-order term and contributes d*D(r^2)+(u^2/2)*e*D'(r^2)-u^4*D(r^4)/8. The tertiary term is f*D(r^3).
3. The divided error extends real-analytically at epsilon=0: the apparent primary 1/epsilon singularity is removable, and the zeroth and first error coefficients vanish identically in all six correction variables. The proof is not merely a pointwise asymptotic cancellation at one correction vector.
4. The six correction columns are independent by the stated seven-root contradiction for a nonzero seven-monomial sparse polynomial. The scalar paired-normal equation gives f0=(u^4/8)*F(r^4)/F(r^3)-u^3/3 exactly; the threshold is precisely its strict positivity condition.
5. IFT supplies finite corrections near that vector. Only positive reciprocal integers epsilon=1/N are used as sources, giving exactly N primary copies and two extra Bernoulli factors. Noninteger multiplicity appears solely in the analytic auxiliary map. Each actual cell remains fresh; assigning repeated parameter values is allowed within the freely parameterized physical model.
6. The primary/secondary leading odds stay positive, their nodes stay interior, tertiary odds stay positive because f0>0, and the baseline stays positive because a>0. The positive baseline can be divided among the finitely many physical short arms/connectors using the inherited source compiler. No zero-length or external mixture source is admitted.
7. At a sufficiently small fixed positive reciprocal integer, the physical six-variable derivative is epsilon^2 times an invertible matrix tending to the limiting one. Thus the exact target lies in actual source interior, not only in closure or at an isolated realization.
8. For r=1/2, a=log 2 and u=6 log 2, the claimed coordinates are algebraic and m_1=1/16. Since log 2>1/2, the uniform threshold holds. The same tuple has a pure paired-critical closure presentation and a different regular actual source, so critical-presentation existence alone cannot be a NO certificate. This does not conflict with the old sufficiently-small-loss rejection theorem.
9. The optional remainder consequence follows from actual additive-semigroup interior-plus-closure absorption. A remainder in the actual closure is an explicit premise; the argument does not replace it with an arbitrary moment cone. The resulting intensity ceiling is necessary for nonattainment, not sufficient for rejection.

## Prior and evidence

The cited provider readbacks were inspected, including the full old dyadic proof and the complete interior/global-closure notes. Their SHA256 and Git blob identities match `providers/LARGE-INTENSITY-PROVIDER-READBACK.json`, SHA256 `b7fca4d05a3ea4362f48471544966af28eb5f8f7e95156a9b049446c3ea5a91b`.

The old odds expansion, sparse-rank/IFT construction, positive source compiler and absorption lemma retain their exact attribution. The new step reviewed here is replacing the residual by an integer primary block plus positive secondary/tertiary corrections at sufficiently large intensity. This is not an exhaustive prior-art or novelty determination.

No source solve, coefficient experiment, QE, extracted N or Lean verification was executed for this review. The unrelated endpoint-resultant pilot is not used as a premise. Interior bounded-intensity/rank-five recognition, coherent hidden joint fibres, other flags and inheritance interfaces, and alternative original cores remain unresolved. Original G3 remains open.
