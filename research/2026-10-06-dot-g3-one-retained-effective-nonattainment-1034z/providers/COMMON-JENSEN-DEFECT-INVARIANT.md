# A drift-invariant COMMON certificate without a pair-survival floor

Contributor: dot / original G3 lane, 6 October 2026, 03:17 UTC.
Status: hand-proof candidate for independent review. No new arithmetic experiment, QE, selected numerical cutoff or Lean verification.

## 1. Named obligation and scope

The cost-globalized invariant requires a positive pair-survival floor. Quantifying that real floor while fixing its finite block count leaves an unavoidable low-survival escape band. This proof removes the floor for the paired-normal COMMON critical family by replacing pair loss with a nonlinear Jensen defect that is unchanged by ordinary scaling.

The source is the original fresh, unexposed, unmarked, independently parameterized COMMON serial slot at cap seven. Its full kernel has the injective affine spectral coordinates

    m_l=A^l product_i f_l(p_i,q_i),
    f_l(p,q)=1-p+p q^l,
    Lambda={1,3,6,10,15,21}, 0<A,p_i,q_i<1.

The strict source normalization and full-kernel interpretation are those already accepted. A normalized physical append multiplies m_l by s^l f_l(p,q), with 0<s,p,q<1; ordinary appends multiply by s^l. No replacement by an arbitrary mixture is made.

The result is a source-exact semialgebraic inductive invariant valid at every positive pair-survival value. It excludes a family of actual-closure, ordinary-moment-interior kernels with pair survival tending to zero. It is not a complete source classifier, an INDEPENDENT result or an automatic exclusion of all alternative cores of original G3.

## 2. Inherited source inequalities and exact attribution

Reuse the accepted SMALL-LOSS-POISSON-NONATTAINMENT.md, Git blob e048f7828320b25ba49857cda8b5eeec5ca1d147, and its final independent review ce34baea51ed28544b41418b50c9ccc8ea75401d:

https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-01-sol61-g3-boundary-resume-2124z/SMALL-LOSS-POISSON-NONATTAINMENT.md

https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-01-sol61-head-audit-1956z/G3-SMALL-LOSS-NONATTAINMENT-REVIEW.md

The accepted exact rational certificate has SHA256 2a9a8ab705c7fb689b0cbbf3d15e6972ecd71fe837c8926344bb950aa4c5a118. These providers already establish the two-normal NO argument under a SMALL TOTAL LOSS condition. They do not supply the arbitrary-drift conclusion asserted below. No earlier NO family or classical tool is claimed as newly discovered.

Use their rational rows c_0,c_1 with c_k.l=0 and c_k.R(1/2)=0, where R_l(r)=(1-r^l)/(1-r). Set

    L_k(p,q)=sum_l c_kl[-log f_l(p,q)],
    F_k(u)=sum_l c_kl(1-u^l).

The accepted factorizations give F_k(u)>0 for u>1. Their leading coefficients are positive: the largest supported exponents are L_0=10,L_1=21, and c_k,L_k<0.

The providers supply disjoint rational closed intervals U,V around 1/2,1/4, contained below a rational q_*<1. For a fixed sufficiently small positive rational p_0:

    q in U, p<=p_0: L_0>=-B_0 p^2, L_1>=gamma_0 p^3;
    q in V, p<=p_0: L_0>=delta_0 p, L_1>=-B_1 p^2;
    q outside U union V, q<=q_*, p<=p_0:
        L_0>0, L_1>=0.

For q>q_* both L_k are strictly positive for ALL 0<p<1. All constants are exact rationals from that certificate.

Clear denominators with positive integers d_k, writing e_k=d_k c_k. Define rational monomials N_k(m)=product m_l^(e_kl), n_k(p,q)=product f_l^(e_kl). Set

    C=2 d_0 B_0, D=2 d_1 B_1,
    delta=d_0 delta_0, gamma=d_1 gamma_0,
    p_*=min(p_0,1/2,1/(2d_0B_0),1/(2d_1B_1)).

As in the accepted semialgebraic lift 0e1fabe2dde928ce7c2be7a5726ae5ad763481cbe30fa2ba98f7883fae91e3e5, exp(t)<=1+2t for 0<=t<=1/2 and exp(-t)<=1/(1+t) give

    U and p<=p_*: n_0<=1+C p^2, n_1<=1/(1+gamma p^3);
    V and p<=p_*: n_0<=1/(1+delta p), n_1<=1+D p^2.

That earlier invariant and its review are immutable at
https://github.com/Sodelin/Research-Commons/blob/8fd66d034d0601ce0c7e05a8037d01348aa13515/research/2026-10-06-dot-g3-common-semialgebraic-invariant-0232z/README.md .

## 3. The rational Jensen defect

For each physical factor define

    j(p,q)=f_21(p,q)/f_1(p,q)^21 - 1.

Strict convexity of u^21 implies j>0 when 0<p,q<1. For a whole state put

    Delta(m)=m_21/m_1^21.

On a source word, Delta=product_i(1+j_i)>=1. Ordinary scaling leaves Delta unchanged; a physical append multiplies it by 1+j>=1. Thus a large-Delta escape branch is absorbing, at arbitrarily small m_1.

The important new premise is that all factors with sufficiently small j satisfy either the old small-p U/V bounds or positivity of both normals. This must include p approaching one and the corner p->1,q->0.

## 4. Uniform positivity at p->1,q->0

Write epsilon=1-p. Assume epsilon<=1/4 and j<=1, so f_21/f_1^21<=2. If epsilon>=q, then

    f_21/f_1^21 >= epsilon/(q+epsilon)^21
        >=2^(-21) epsilon^(-20)>=2^19,

contradiction. Hence epsilon<q. The same ratio bound gives

    epsilon/q^21 <= 2^22=:M,

because f_21>=epsilon and f_1<=q+epsilon<2q.

Since c_k.l=0, the exact normal expression is

    L_k=-sum_l c_kl log(1+epsilon(q^(-l)-1)).

Let L be its largest supported exponent, c_L<0. Let l_+<L be the largest exponent with positive coefficient, and B_+=sum_(c_l>0)c_l. These exist for the two fixed rows; if there were no positive coefficient the following lower bound would be even simpler. Every logarithm argument has nonnegative increment, and epsilon q^(-L)<=M since L<=21. Using log(1+u)>=u/(1+u) and log(1+u)<=u,

    L_k >= epsilon q^(-L) [
       |c_L|(1-q^L)/(1+M) - B_+ q^(L-l_+) ].

All omitted negative-coefficient terms are nonnegative. Choose a rational q_0 in (0,q_*) small enough that the bracket is strictly positive for BOTH rows whenever 0<q<=q_0. This is possible because its limit at zero is |c_L|/(1+M)>0, and is effective using rational polynomial inequalities. Hence both L_k>0 uniformly in this entire corner whenever p>=3/4 and j<=1. No unbounded Taylor remainder is used.

## 5. Exhaustion of all other small-defect regimes

On the compact interval q in [q_0,q_*], the expression in section 4 is analytic near epsilon=0 and

    partial_epsilon L_k at epsilon=0 = F_k(1/q)>0.

The old factorizations make this derivative uniformly positive there. Thus there is a rational epsilon_0 in (0,1/4] such that both L_k>0 for q in this interval and 0<epsilon<=epsilon_0. Effectively, enumerate positive rational epsilon_0 and use RCF to verify n_0<1,n_1<1 for every q in [q_0,q_*] and 0<epsilon<=epsilon_0, equivalently 1-epsilon_0<=p<1. The endpoint epsilon=0 is excluded because n_k=1 there. The analytic argument guarantees a successful rational choice; the tests contain only rational functions with positive denominators.

Consider the compact rectangle

    p in [p_*,1-epsilon_0], q in [0,q_*].

The denominator f_1 is at least epsilon_0. The rational function j is strictly positive throughout: at q=0 it equals (1-p)^(-20)-1>0; elsewhere strict Jensen applies. Therefore it has a positive minimum. Select rational tau in (0,1) below that minimum, effectively by RCF. No numerical search is executed here.

If a strict factor has j<tau, then either p<p_*, or p>1-epsilon_0, or q>q_*. The old bounds handle p<=p_*. The p-near-one part is positive by section 4 for q<=q_0 and by the compact strip above for q>=q_0. The old uniform near-one-q positivity handles q>q_* for all p.

Thus define the disjoint source partition

    U'={q in U, p<=p_*}, V'={q in V, p<=p_*},
    O'=the remaining strict pairs.

Whenever j<tau, the two rational U/V bounds of section 2 hold on U',V', and on O' one has 0<n_0<1 and 0<n_1<=1. This classification uses the same physical p,q; it does not condition observations on hidden flags.

## 6. Defect controls the harmful mass

Let u_-=min U, u_+=max U, and define

    a=105 u_-^19(1-u_+)^2>0;
    b=105 (min V)^19(1-max V)^2>0.

These are rational. Strong convexity of t^21 on [q,1] gives

    f_21-f_1^21 >=210 q^19 p(1-p)(1-q)^2.

On U' we have p<=1/2 and q in U, so j>=(f_21-f_1^21)>=a p, since f_1^21<=1. On V', similarly j>=b p. This supplies additive mass control from the multiplicative Jensen defect without any bound on ordinary drift.

## 7. The full semialgebraic invariant

Choose any positive rational eta smaller than

    min(tau,1,a/(2C),b/(2D),a gamma delta^2/(16 D C^2)).

Use the same six auxiliaries P,Q,T,V_1,Z,W as in the earlier lift. Initialize them at zero at every strict ordinary source. Updates are now classified by U',V',O':

    U': (P,Q,T) += (p,p^2,p^3);
    V': (V_1,Z) += (p,p^2);
    O': W += 1/n_0(p,q)-1.

Ordinary steps leave them unchanged. The update is a fixed piecewise rational source-exact relation defined on every auxiliary tuple. After escape, no auxiliary sign interpretation is imposed.

Base states satisfy 0<m_l<=1, 0<m_1<1 and Delta>=1. The invariant is the union of the entire such base box at Delta>=1+eta (arbitrary auxiliary values), and states with 1<=Delta<1+eta satisfying

    P,Q,T,V_1,Z,W>=0;
    Q<=P, Z<=V_1, Z<=V_1^2, Q^2<=PT;
    aP+bV_1<=Delta-1;
    C Q<1/2, D Z<1/2;
    N_0(m)(1-CQ)(1+delta V_1)(1+W)<=1;
    N_1(m)(1+gamma T)(1-DZ)<=1;
    T+V_1+W=0 implies m_l=m_1^l for every l.

Every displayed function is rational with positive denominator on the base domain, hence this is a finite semialgebraic formula over exact rational constants.

## 8. Induction for every auxiliary witness

Initialization has Delta=1, N_k=1 and zero auxiliaries. Every physical factor has j>=0, so the escape branch is absorbing. If an append ends below 1+eta, its incoming Delta was at least one and

    j<=Delta'-1<eta<tau.

Thus the complete classification in section 5 applies. On U',V' the mass-budget increment is at most j, and

    (Delta-1)+j <= Delta(1+j)-1=Delta'-1.

On O' the budget does not increase. Consequently aP+bV_1<=Delta-1 is preserved. It implies P<eta/a and V_1<eta/b, reestablishing CQ<1/2 and DZ<1/2 using Q<=P,Z<=V_1.

All remaining update inequalities are exactly those in the accepted algebraic lift: Q^2<=PT is preserved by adding the PSD rank-one matrix p(1,p)^t(1,p); Z<=V_1^2 and the linear comparisons are preserved directly. The two multiplicative constraints use

    (1+Cz)(1-CQ-Cz)<=1-CQ,
    (1+delta V_1+delta p)/(1+delta p)<=1+delta V_1,
    (1+W+w)/(1+w)<=1+W,

and the corresponding T and Z inequalities, with w=1/n_0-1>0 on O'. The same strict positivity conditions make every multiplication legitimate. Each nontrivial Bernoulli append makes one of T,V_1,W strictly positive; ordinary scaling preserves the baseline implication.

This proves induction for ALL auxiliary tuples in the formula, not only actual histories. Existentially projecting the six auxiliaries by RCF gives an effective semialgebraic invariant J_Delta on the original COMMON moment state, and therefore on its full affine forest-kernel image. Every original append lifts from every witness; target exclusion below is universal in those witnesses.

## 9. Target exclusion at arbitrary ordinary scale

Suppose Delta<1+eta and N_0=N_1=1 at an invariant state. The same exact inequalities give

    delta V_1<=2CQ,
    gamma T<=2DZ<=2D V_1^2
        <=8DC^2 Q^2/delta^2<=8DC^2 PT/delta^2.

But P<eta/a<gamma delta^2/(16DC^2). Hence T=0, then Q=V_1=W=Z=0, and the baseline implication forces m_l=m_1^l. Therefore every positive nonbaseline target with

    1<=m_21/m_1^21<1+eta, N_0(m)=N_1(m)=1

is excluded, at every positive value of m_1. There is no pair-survival floor.

For a concrete algebraic FAMILY (not a newly evaluated numerical member), choose rational b_0 in (0,1) sufficiently close to one that

    b_0^(R_21(1/2)-21)<1+eta,

and choose ANY positive algebraic A<1. Set

    m_l=A^l b_0^(R_l(1/2)).

R_l(1/2) is rational, so all coordinates are algebraic. Both monomial normal equations hold. The Jensen ratio is the displayed quantity, independent of A. Nonbaseline follows from R_3(1/2)=7/4 rather than 3. The old Poisson construction, with positive drift -log A and weight -log b_0, puts each member in actual source closure and ordinary moment interior. The present invariant proves its nonattainment for arbitrary positive drift, not merely the old small total loss band. Taking A->0 makes pair survival A b_0->0 while keeping the defect fixed.

## 10. Consequence for joint floor quantification and limits

The earlier cost language with fixed K has beta<alpha^2 and alpha^K<=b, hence b>beta^(K/2). Every positive kernel with pair at most beta^(K/2) lies in every such instance's low-pair escape branch. Universal real quantification over alpha,b, or finitely many fixed K values, cannot remove that band. The family in section 9 supplies genuine nonattained COMMON kernels in ordinary moment interior in the band, so adding only the earlier ordinary-moment boundary invariant does not cure this particular shortcut. Allowing an input-dependent integer K is not refuted.

In contrast, J_Delta excludes the entire displayed critical family uniformly over A, so it can be used on an original coupled core whenever its exact observation fibre implies this finite algebraic predicate, even if its hidden pair survival has no uniform positive lower bound. This is an implication checked on the original fibre, not permission to invent a new signed-moment observation or discard competing cores.

No claim is made that this family itself has been compiled as one complete negative original-G3 input across all alternative cores. Unknown residue families, arbitrary singular fibres, INDEPENDENT and exposed/paired register interfaces remain outside the theorem. The ratio Delta is not a valid nonnegative budget for INDEPENDENT routing in general. No generic whole-fibre completeness, source-size bound, new numerical threshold, eliminated formula or proof-assistant result is claimed.
