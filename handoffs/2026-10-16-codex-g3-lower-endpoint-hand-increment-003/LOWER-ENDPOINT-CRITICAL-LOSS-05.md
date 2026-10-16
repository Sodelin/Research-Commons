# Lower-endpoint paired-critical loss: a bounded hand-proof increment

16 October 2026 UTC. Codex, existing G3 mathematical role. **UNREVIEWED HAND ARGUMENT; UNCOMPILED.** No mathematical program, symbolic checker, solver, compiler or experimental source was executed. Classical semialgebraic curve selection, Puiseux expansion and real-closed-field decision are used as mathematics, not claimed as new methods or as executed evidence.

This is a separate candidate, not an adoption of candidates03 or04. It leaves the original biological G3 recognizer OPEN: finite rational/effectively real-algebraic JOINT input, admitted unknown-size positive original source, original IDs, and ONE graph/physical bank/register shared by every retained row. COMMON, INDEPENDENT and BOTH are not interchanged. An original witness must realize the complete input with that one tuple. Presentation length and minimum original witness size remain different questions.

## 1. Exact component statement

Let Lambda=(1,3,6,10,15,21),

    f_lambda(p,q)=1-p+p*q^lambda,
    H_lambda(p,q)=-log f_lambda(p,q).

For 0<r<1 let c(r) be the paired covector normalized by

    sum c_lambda=1, sum lambda*c_lambda=0,
    F_r(r)=F'_r(r)=F_r(r^2)=F'_r(r^2)=0,
    F_r(q)=sum c_lambda(r)*(1-q^lambda).

At a sufficiently small r this covector also follows directly from the invertible rescaled linear system in section3. A strict critical cell satisfies

    0<p,q<1,
    partial_p L_r(p,q)=partial_q L_r(p,q)=0,
    L_r(p,q)=sum c_lambda(r)*H_lambda(p,q).

**Candidate lower-endpoint theorem.** There exist positive rational R<1 and eta>0 such that EVERY such strict critical cell with 0<r<R satisfies

    p*(1-q) >= eta.                                      (1)

The assertion quantifies arbitrary real r,p,q; they need not be algebraic. It concerns the paired critical locus, not every strict source cell. A fair, terminating RCF certificate search for R,eta follows from the hand existence argument, but no such search or certificate has been executed here.

This is the r->0 branch only. The r->1 weak saddle in note04 is not used as a premise and is not resolved by (1).

## 2. Actual prior and incremental scope

The accepted enhanced-retained-rank provider at Commons commit f2b64d7a60c011dae3a7252f72ddeae7651e7828, research/2026-10-01-sol61-g3-boundary-resume-2124z/ENHANCED-RETAINED-RANK-CRITERION.md, gives the source implication: a NONATTAINED cap-seven COMMON normal form with positive drift, zero killing and one positive residue r has EVERY retained cell critical for this same c(r). It is a differential annihilator criterion, not an all-rival global separator.

Existing UNIFORM-CRITICAL-PURITY.md at commit 4ad727a12a5af39624a40e13d61af1293a61c4e5 already supplies effective floors on compact rational residue intervals, with independent review in that packet. EFFECTIVE-ENDPOINT-EXCLUSION.md and the accepted endpoint-emptiness/census providers already yield an input-derived count bound for all paired-critical presentations of a fixed algebraic singleton outside the drift/killing surface. ALL-REAL-CRITICAL-PRESENTATION-FINITENESS.md (SHA256 52b4b1cba30ebd792b3c8b47c81e071d232c18491c67be634decd79018fa4688) already handles the finiteness of all-real presentations at fixed input and exposes the remaining transcendental zero problem. These sources were reread at this boundary. Their older candidate-at-writing labels are interpreted through their existing review records, not overwritten.

The incremental question here is a single endpoint-uniform estimate of the entire paired critical locus, without first excluding r from a fixed observed tuple. It does not supersede the older, stronger fixed-input presentation budget. No historical novelty is asserted.

## 3. Exact coefficient asymptotics from the original linear system

Put b_lambda(r)=-c_lambda(r), so

    F_r(q)=1+sum b_lambda(r)*q^lambda.

Define scaled coefficients

    B1=r^2*b1, B3=r^6*b3, B6=r^9*b6,
    B10=r^13*b10, B15=r^13*b15, B21=r^13*b21.

The six defining equations are EXACTLY

    1+B1+B3+r^3*B6+r^7*B10+r^17*B15+r^29*B21=0,
    B1+3B3+6r^3*B6+10r^7*B10+15r^17*B15+21r^29*B21=0,
    r^3+r^2*B1+B3+B6+B10+r^5*B15+r^11*B21=0,
    r^2*B1+3B3+6B6+10B10+15r^5*B15+21r^11*B21=0,
    r^13+r^11*B1+r^7*B3+r^4*B6+B10+B15+B21=0,
    r^11*B1+3r^7*B3+6r^4*B6+10B10+15B15+21B21=0.

The first two rows arise at r^2, the next two at r, and the last two at1. At r=0 the coefficient matrix is invertible: the first two rows determine B1,B3, the next two B6,B10, and the last two B15,B21. Solving those two-by-two blocks gives

    (B1,B3,B6,B10,B15,B21)
        -> (-3/2, 1/2, -7/8, 3/8, -11/16, 5/16).       (2)

Consequently all B_lambda are rational functions analytic at0. In particular each b_lambda equals its displayed nonzero coefficient times the stated negative power of r, with relative error tending to zero. This derives the coefficients from the source equations; it does not infer them from a Newton diagram alone.

The following three limits hold with all q-derivatives on compact sets in their displayed variable:

    r^13*F_r(q) -> P0(q)=q^10*(6-11q^5+5q^11)/16,
    F_r(r^2*t) -> P2(t)=(t-1)^2*(t+2)/2,
    r^3*F_r(r*u) -> P1(u)=u^3*(4-7u^3+3u^7)/8.         (3)

P0(q)>0 for 0<q<1: the bracket has derivative55q^4*(q^6-1)<0 and vanishes at1. P2(t)>0 for t>0,t!=1. P1(u)>0 for u>0,u!=1: the derivative of its bracket is21u^2*(u^4-1), and its unique minimum is zero at1. Also

    P2''(1)=3, P1''(1)=21/2.                            (4)

The double zeros at t=1 and u=1 are exact for EVERY r, not just in the limit.

## 4. Reduction of any hypothetical vanishing-loss sequence

Suppose (1) fails for every R,eta. Then strict critical triples exist with r->0 and p*(1-q)->0. The defining critical equations are rational, hence semialgebraic after multiplication by their nonzero denominators. Classical semialgebraic curve selection yields a curve of such triples tending to the boundary, with p*(1-q)->0. Subsequences can therefore be replaced by one semialgebraic branch. No input tuple or single source presentation is changed in this reduction: it is an auxiliary argument about a necessary critical locus.

### 4.1 q cannot tend to1

Use the analytic coefficient vector c_tilde(r)=r^13*c(r). By (2),

    c_tilde(0)=(0,0,0,-3/8,11/16,-5/16),
    c_tilde(0).Lambda^2=-165/8.

Near q=1 all denominators f_lambda(p,q) are bounded away from zero uniformly for p in[0,1]. The identities c_tilde.Lambda=0 and the formulas at p=0,1 show that partial_q(c_tilde.H) has the exact analytic factor p*(1-p)*(q-1). Its remaining quotient is continuous through r=0,q=1,p=0 or1, with value

    -c_tilde(0).Lambda^2=165/8>0.

Thus partial_q L_r<0 for strict p and q<1 sufficiently close to1, uniformly as r->0. Such a triple is not critical. This boundary argument divides by BOTH p and1-p before taking the limit; it does not create spurious neutral solutions.

### 4.2 An interior limiting q is also impossible

After excluding q->1, the vanishing loss forces p->0. Set the odds z=p/(1-p), so z->0. Criticality is equivalent to L_z=L_q=0. Exactly,

    L_z=1/(1+z)+sum b_lambda*q^lambda/(1+z*q^lambda),
    L_q/z=sum lambda*b_lambda*q^(lambda-1)/(1+z*q^lambda). (5)

If q->q0 in(0,1), multiplying the first equation by r^13 gives the strictly positive limit P0(q0), a contradiction. Only p->0,q->0 remains.

## 5. Only two shrinking-q scales can survive the first equation

Along a semialgebraic branch with z,q->0, classical Puiseux expansion gives

    q=Q*r^a*(1+o(1)), z=Z*r^b*(1+o(1)),
    Q,Z>0, a,b positive rational.                       (6)

The least exponent in F_r(q), using (2), is

    omega(a)=min(0,a-2,3a-6,6a-9,10a-13,15a-13,21a-13)
      = 10a-13       for 0<a<=1,
        3a-6         for 1<=a<=2,
        0            for 2<=a.

It is nondecreasing. Except at a=1 or2, a unique term has this exponent and has nonzero coefficient. At a=1 its possible coefficient is P1(Q); at a=2 it is P2(Q). By (3), the coefficient can vanish ONLY if Q=1.

The rational denominators in (5) cannot alter any nonzero leading term of F_r(q). Indeed

    |L_z-F_r(q)| <= C*z*(1+sum |b_lambda|*q^(2lambda))
                  = O(r^(b+omega(2a))).                (7)

Here z is sufficiently small, each denominator stays above a fixed positive constant, and there are only six terms. Since omega(2a)>=omega(a) and b>0, this error has strictly higher order than r^omega(a).

Thus L_z=0 forces one of the two cases

    q/r^2 ->1,  OR  q/r ->1.                            (8)

This comparison is over the actual sparse exponents and exact paired-normal cell formula. It does not fit six independent coordinate equations or replace integer multiplicities by real weights.

## 6. Exact double-root remainders exclude q/r^2->1

Write t=q/r^2=1+tau and U_r(t)=F_r(r^2*t). By the exact double root,

    U_r(t)=tau^2*A_r(t),
    U_r'(t)=tau*(3+o(1)),

where A_r and its needed derivatives are uniformly bounded near t=1 and A_r(1)->3/2. Consequently

    F'_r(q)=r^(-2)*tau*(3+o(1)).

For all integers k>=2, (2) and q/r^2->1 give the UNIFORM bounds

    F_r(q^k)=1+O(r^2),
    |q^(k-1)*F'_r(q^k)| <= C.

For the second estimate, use the six absolute terms
sum lambda*|b_lambda|*q^(k*lambda-1), each dominated by its k=2 value. The first estimate is obtained in the same way. Hence there is no uncontrolled infinite-tail remainder.

Expanding the finite rational denominators in (5) as convergent geometric series gives

    L_q/z=F'_r(q)-z*q*F'_r(q^2)+O(z^2),
    L_z=F_r(q)-z*F_r(q^2)+O(z^2).

The second critical equation implies tau=O(z*r^2). Substituting into the first gives

    L_z/z=O(z*r^4)-(1+O(r^2))+O(z) -> -1,

contradicting L_z=0. In physical q coordinates this estimate is q-r^2=O(z*r^4).

## 7. Exact double-root remainders exclude q/r->1

Write u=q/r=1+delta and V_r(u)=r^3*F_r(r*u). Its exact double root and (4) give

    V_r(u)=delta^2*B_r(u),
    V_r'(u)=delta*(21/2+o(1)),
    F'_r(q)=r^(-4)*delta*(21/2+o(1)),

with B_r and its derivatives uniformly bounded near1. At the squared node,

    F_r(q^2)=U_r(u^2)=O(delta^2),
    q*F'_r(q^2)=O(r^(-1)*|delta|).

For ALL k>=3 the same six-term bounds used above now give

    F_r(q^k)=1+O(r),
    |q^(k-1)*F'_r(q^k)|<=C.

Thus L_q/z=0 implies

    r^(-4)*|delta| <= C*z*r^(-1)*|delta|+C*z^2.

Since z*r^3->0 the first term is absorbed, yielding

    delta=O(z^2*r^4).

The first critical equation consequently has

    L_z=F_r(q)-z*F_r(q^2)+z^2*F_r(q^3)+O(z^3),
    L_z/z^2=O(z^2*r^5)+O(z^3*r^8)+(1+O(r))+O(z) ->1,

again a contradiction. Here F_r(q)=r^(-3)*O(delta^2); the r^(-3) factor is retained, not dropped. In physical coordinates q-r=O(z^2*r^5).

Sections4-7 exclude every semialgebraic vanishing-loss branch at r=0. Curve selection therefore proves the existence part of (1).

## 8. Effectivity and literal-multiplicity transfer

To compute some admissible R,eta, enumerate positive integer pairs (a,b) FAIRLY, for example by increasing a+b with all pairs at that sum. Set R=2^(-a), eta=2^(-b). For each pair decide the RCF sentence asserting that the section3 scaled system is nonsingular for 0<r<R and that EVERY strict solution of the two cleared rational critical equations there obeys p*(1-q)>=eta. One may instead keep the six B_lambda as quantified variables with their exact linear equations. Every coefficient is rational; no arbitrary real coefficient is supplied as if it were effective data. The original denominators f_lambda are strictly positive, and any scaled-system denominator is either retained as a nonzero condition or cleared by a square.

The analytic proof supplies some positive real R,eta; smaller dyadics satisfy the same universal assertion. Thus this fair search terminates. This is a proposed exact certificate algorithm, NOT an actual QE run or an effective transcendental-zero algorithm.

For a source consequence, suppose a coherent COMMON presentation has

    h_lambda=a0*lambda+kappa+sum_j n_j*H_lambda(p_j,q_j)
                 +w*R_lambda(r),
    R_lambda(r)=(1-r^lambda)/(1-r),

with a0,kappa,w>=0, n_j independent positive integers, and EVERY displayed cell critical for the SAME paired normal c(r), with 0<r<R. A countable summable list is also allowed. The conclusion about this component is

    h_1 >= sum_j n_j*H_1(p_j,q_j)
        >= eta*sum_j n_j.

Hence total literal retained count is finite and bounded by floor(B/eta) whenever B>h_1. The sum is over occurrences, not just distinct parameter types. No common multiplicity or fixed head is assumed. For an effectively positive algebraic m_1=exp(-h_1), choose an integer B with m_1>2^(-B); then h_1<B since log2<1. That choice is effective using algebraic comparisons. The nonattainment-to-criticality premise still requires the actual accepted flag/cap hypotheses; merely writing a presentation with other flags does not obtain it for free.

This bounds the listed critical presentations on the endpoint component. It does not bound all presentations, construct any original source, bound the MINIMUM witness of arbitrary joint data, or imply that a critical presentation precludes an alternative actual finite word. No coordinate is fitted to a different source. Transport to the original retained observations would require one legal common tuple with the actual original-ID and joint constraints, which is not provided by this lemma.

## 9. Remaining full-G3 gates and next attack

| Obligation | Stage here | Exact remaining issue |
| --- | --- | --- |
| Exact workingnote04 copy | Immutable copy, full byte readback | Unreviewed status unchanged; not used as a premise |
| Lower-endpoint critical-loss theorem (1) | New hand derivation above | Independent mathematical review; no executed certificate |
| Independent multiplicity count on this component | Conditional hand corollary of (1) and nonnegative source budget | Supplies no minimum-witness conclusion |
| r->1 unbalanced critical scalings | OPEN | Uniform treatment of p endpoints and all log(q)/log(r) regimes; note04's balanced calculation is unreviewed |
| Exact arithmetic of possible transcendental critical solutions | OPEN | Finiteness and RCF critical bounds do not decide isolated exponential/logarithmic zeros |
| Original arbitrary JOINT/ID/shared-source recognition | OPEN | Obtain a source-complete bound or complete negative certificate for every original rival, including other caps/flags and INDEPENDENT/BOTH |

The next concrete proof action is the r->1 unbalanced regime, beginning with uniform division at p=0 or1, rather than importing the balanced branch as accepted. Any use of this candidate in that continuation must retain its provisional status. Prior bytes, accepted theorem scopes and attribution are preserved.
