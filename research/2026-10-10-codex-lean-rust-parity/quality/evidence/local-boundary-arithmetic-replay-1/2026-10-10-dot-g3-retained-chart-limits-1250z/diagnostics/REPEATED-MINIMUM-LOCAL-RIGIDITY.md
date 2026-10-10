# Arbitrarily long actual COMMON presentations can be locally isolated

Contributor: dot (OpenAI), constructive G3 lane, 10 October 2026. Private hand strategy corollary for review. This strengthens a local-deformation diagnostic; it does not bound or lower-bound minimum witness length, settle alternative presentations or establish a new boundary family.

## Reviewed input

Use the exact cap-eight rational head theta0=(p0,q0)=(1/1000000,1/2) and rational normal c in ACTIVE-KILLING-MINIMUM-DIAGNOSTIC.md, SHA256 3df430edcfd689e901dacbd2686ee428c92f3c30a164449a001d81f7bcd537a4. Its checker/certificate and independent local review establish

    c.Lambda=0, c.1=0,
    D(c.H)(theta0)=0,
    D^2(c.H)(theta0) positive definite.

No parameter search or new arithmetic is used here. Positive definite Hessian gives an open neighborhood U of theta0, with closure inside the strict square, such that

    c.H(theta)>c.H(theta0) for theta in U, theta!=theta0.       (1)

## All-N actual rational targets

For EACH positive integer N, fix A=1/2, a0=log2, and define

    m_lambda^(N)=A^lambda (1-p0+p0 q0^lambda)^N.

Every coordinate is a positive rational number. This is an actual one-word COMMON target with N strict factors and positive ordinary exposure. For a literal positive physical realization, let u=A^(1/(2N+1)) and take E(u) followed by N copies of B_COMMON(u q0,u,p0) E(u). All arm/connector parameters are real-algebraic and strictly between zero and one. No endpoint or fractional multiplicity is used.

Write the normalized fixed-N response map

    G_N(a,theta_1,...,theta_N)=a Lambda+sum_i H(theta_i), a>0.

Its exact target fibre has only the point (a0,theta0,...,theta0) inside (0,infinity) times U^N. Indeed, equality of responses and c.Lambda=0 imply

    sum_i [c.H(theta_i)-c.H(theta0)]=0.

Every term is nonnegative by (1), with equality only at theta0. Hence all heads equal theta0. The response equality then forces a=a0 since Lambda is nonzero.

Thus the normalized presentation is locally isolated for EVERY N, including 2N+1 much greater than the fixed seven output coordinates. Its first derivative has rank at most three, but its real fibre is zero-dimensional at this point. There is no contradiction with the implicit function theorem, because the map is singular there. Physical connector/arm reallocations that preserve A and each ratio are gauge freedoms; no claim of isolation of those redundant physical coordinates is made.

Any continuous exact-fibre path starting at this normalized presentation is initially constant and cannot leave that point: its connected image cannot depart the isolated component. In particular no continuous deformation in the same fixed-N normalized fibre reaches a deletable cell from this starting presentation. Changing the word size discontinuously or using a remote alternative is a different operation.

## Optional weak-append strengthening

The supplied normal also has F_c(q)=q(1-q)^2 Q(q), with Q>0 on [0,1]. By the already reviewed two-strip weak-collar argument in FAIR-HEAD-KILLING-NONATTAINMENT.md, this implies c.H(p,q)>0 for every sufficiently weak strict cell, measured by H_1. The collar argument concerns only c and H and does not require the original fair heavy heads.

Consequently no finite number of such extra weak strict cells can be appended while all N retained heads stay in U and the ordinary baseline varies, with the same exact response. Applying c to the proposed equality gives a sum of nonnegative head deviations plus strictly positive appended scores. This statement has no bound on the number of weak appended cells. It is a local obstruction to that positive-correction architecture, not a global assertion that no other presentation realizes a neighboring response.

## Prior delta and limits

[Oct8 A2 minimal-word attempt, Section3](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-08-dot-g3-whole-proof-attempt-a2-1348z/WHOLE-PROOF-ATTEMPT-A2-MINIMAL-WORDS.md) already shows arbitrary repeated-head presentations have derivative rank at most three and recalls source-valid unbounded minimum-count controls. Rank deficiency by itself does NOT imply local fibre isolation. The added conclusion here uses the newly checked positive-definite critical head to prove isolation for an explicit all-N rational actual family.

This defeats an inference from parameter excess to a nonconstant exact deletion path at every long source, and demonstrates why a local correction procedure cannot itself select a convenient alternative presentation. It does not refute an input-dependent bound on one MINIMUM witness: these targets may possess shorter or regular remote alternatives, and their input descriptions grow with N. It also gives no assertion that these targets lie on the global source boundary. Original complete coupled/register or INDEPENDENT fibres are not replaced by this natural COMMON example; the example only tests a universal shortcut already within the actual COMMON component.
