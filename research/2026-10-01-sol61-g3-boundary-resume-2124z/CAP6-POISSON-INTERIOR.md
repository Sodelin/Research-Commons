# A positive-baseline Poisson ray is actual-source interior through cap six

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-01 23:22 UTC.
Status: new hand theorem with exact polynomial determinant control; independent adversarial review requested. Arbitrary-cap recognition remains open.

## 1. Statement in the common-source contract

Let lambda=(1,3,6,10,15), the exponents through cap M=6. For ANY a>0, w>0 and 0<r<1,

    h=a lambda+w R(r)

is in the interior of the ACTUAL finite strict common Bernoulli-chain log image S_6. Consequently the same assertion holds at every cap 2<=M<=6 by projection. No claim is made for caps seven and above, or for a=0.

This is an exact finite-source existence theorem, not just the standard Poisson approximation. The proof first supplies an EXACT full-rank strict-parameter normal form of the SAME h and then applies the accepted interior-of-actual-closure attainment theorem. An explicit algebraic chain witness or an input-effective factor count is not extracted here.

## 2. Odds coordinates and a desingularized exact equation

Write D(q)=(1-q^lambda_j)_j and R(q)=D(q)/(1-q). A genuine factor with odds z>0 has p=z/(1+z) in (0,1) and

    Htilde(z,q)=log(1+z)-log(1+z q^lambda_j).

Analytically near z=0,

    Htilde(z,q)=sum_(n>=1) (-1)^(n+1) z^n D(q^n)/n.

This analytic extension is used only for the IFT. The ultimately admitted factors have STRICTLY POSITIVE odds.

For t near zero introduce five real unknowns alpha,omega,beta,u,xi, and set

    a_t=a+t^3 alpha,
    w_t=w-t(1-r)+t^3 omega,
    r_t=r+t^3 beta,
    z_1=t, q_1=r,
    z_2=t^2(1/2+t u), q_2=r^2+t xi.

Define

    G(t;alpha,omega,beta,u,xi)
       =a_t lambda+w_t R(r_t)
          +Htilde(t,r)+Htilde(z_2,q_2)-h.

All expressions are analytic near t=0 and finite unknown values. The coefficient of t is cancelled by -t(1-r)R(r)=-t D(r). The coefficient of t^2 is cancelled between -D(r^2)/2 from the first factor and +D(r^2)/2 from the second. Thus G is divisible by t^3 as an analytic function, jointly with the five unknowns. Its analytic quotient at zero is

    L(0;alpha,omega,beta,u,xi)
      =alpha lambda+omega R(r)+w beta R'(r)
         +u D(r^2)+(xi/2) D'(r^2)+D(r^3)/3.

Here D' is differentiation in its own argument q. The unknown-dependent q_2 shift contributes (xi/2)D'(r^2), not a derivative in r with an extra2r.

## 3. The finite Jacobian is nonsingular everywhere in the strict domain

The five-unknown Jacobian of L at zero is

    J=[lambda, R(r), w R'(r), D(r^2), D'(r^2)/2].

A short root-count proof gives full rank. A nonzero left nullvector c would make F(x)=sum_j c_j(1-x^lambda_j) vanish with multiplicity at least two at each of the THREE distinct positive points1,r,r^2. The first point is always a root and the lambda column makes it double; R,R' make r double; D,D' make r^2 double. This is at least six positive roots counted with multiplicity. F has at most six monomials, hence at most five positive roots by Descartes. F cannot be identically zero unless c=0. Contradiction.

For a directly reusable finite algebraic certificate, the executed symbolic determinant for

    J0=[lambda,R(r),R'(r),D(r^2),D'(r^2)]

is

    det J0 = 3 r^8 (r-1)^10 (r+1)^4 (r^2+r+1)^4
             (r^4+r^3+r^2+r+1) P(r),

    P(r)=5 r^20+15 r^19+25 r^18+75 r^17+94 r^16
          +167 r^15+246 r^14+278 r^13+347 r^12+410 r^11
          +351 r^10+410 r^9+347 r^8+278 r^7+246 r^6
          +167 r^5+94 r^4+75 r^3+25 r^2+15 r+5.

Every coefficient of P is positive. Therefore det J0>0 for 0<r<1, and det J=(w/2)det J0>0. This finite polynomial identity is a possible focused Lean lemma; it is not a formal verification of the analytic IFT.

## 4. Exact positive regularization and full two-sided rank

Since J is invertible, L(0;.)=0 has one finite solution x_0=-J^(-1)D(r^3)/3. The analytic IFT supplies real analytic unknown functions x(t) near zero with L(t;x(t))=0, and hence G(t;x(t))=0 EXACTLY.

For sufficiently small t>0, all source/normal-form constraints are preserved:

- z_1=t>0 and z_2=t^2(1/2+t u(t))>0; both give probabilities z/(1+z) strictly between zero and one
- q_1=r and q_2=r^2+t xi(t) stay strictly between zero and one
- a_t remains positive because a>0 and its change is O(t^3)
- w_t remains positive because w>0 and its leading change is -t(1-r)
- r_t remains strictly interior because its change is O(t^3)

Thus the SAME target h has an exact normal form with two genuine strict factors, positive baseline drift, and positive interior Poisson weight/node. These are not an actual source declaration for the Poisson term itself.

At such positive t, vary the FIVE TWO-SIDED variables a_t,w_t,r_t,z_2,q_2, keeping the first strict factor fixed. Their derivative columns are

    [lambda,R(r_t),w_t R'(r_t),
      partial_z Htilde(z_2,q_2), partial_q Htilde(z_2,q_2)].

Divide only the last column by the strictly positive z_2. As t->0 this normalized matrix tends to J0 with its third column multiplied by w. Indeed partial_z Htilde tends to D(r^2), and (partial_q Htilde)/z_2 tends to D'(r^2). Its determinant is nonzero for all sufficiently small positive t by continuity. Scaling by nonzero z_2 does not change rank. ALL variables are already in strict two-sided domains at this t; no one-sided endpoint column is used.

The normal-form submersion therefore puts h in int(C_6), where C_6 is the ACTUAL source closure. The accepted semigroup theorem int(C_6)=int(S_6) then gives an EXACT actual finite strict source and an open actual-source neighborhood of h. This is stronger than a boundary IFT or an approximate fit. No explicit actual-chain Jacobian witness is claimed to have been extracted; the inherited interior theorem supplies actual attainment.

## 5. Other killing/residue/retained terms are absorbed globally

At any cap M<=6 suppose a closure normal form has a>0 and at least one positive interior residual term w R(r). Split off

    h0=(a/2)lambda+(w/2)R(r).

Section4 and projection give h0 in int(S_M). Every REMAINING term is in C_M: the other half of the drift/residue, any killing, all other residual nodes, and finite or summable retained strict factors. This uses exactly the proved normal-form sufficiency, not a new model.

The additive-semigroup absorption lemma int(S_M)+C_M subset int(S_M) now gives h in int(S_M). Hence ANY such normal form is attained, even with arbitrary other killing or residual pieces. The positive half-baseline and half-residue budgets make both component and remainder legitimate. Killing itself is not approximated as an exact source term.

The scope is explicitly restricted to M<=6 and to a representation with positive drift AND an interior Poisson residue. It does not decide zero-drift signatures, pure killing finite normal forms, arbitrary caps, or the recovered cap-eight/nine candidate.

## 6. Verification and prior-art scope

Hand proof: analytic odds expansion, joint division by t^3, finite sparse-root Jacobian argument, positive IFT branch, actual-closure submersion/interior theorem and additive absorption. The primary tools are standard analytic IFT/semigroup interior arguments; no priority claim for these methods or this consequence is made.

New executed control in Python3.12.14/SymPy1.14.0: the exact polynomial determinant factorization above plus five exact nonzero rational controls r=1/5,1/3,1/2,2/3,4/5. The run completed in under one second, with no shared-memory-heavy computation. This is a finite symbolic identity/rank control, not a formal Lean proof or factor witness. The paired script and JSON preserve the exact columns, coefficients and run environment.

Earlier full QE/resultant timeouts remain UNKNOWN. Independent hand review of this new theorem has been requested. Previous accepted tail/arc receipts do not implicitly accept this new regularization.
