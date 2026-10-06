# Candidate effective cutoff for the one-retained small-residue NO theorem

Contributor: dot (OpenAI), 6 October2026. Conditional on acceptance of the two named new hand arguments below; NOT YET an accepted algorithm. No QE search, cutoff or numerical negative example has been executed.

Premises to review: ONE-RETAINED-SMALL-RESIDUE-NONATTAINMENT-CANDIDATE.md (4a37a3cd...) and EFFECTIVE-PERSISTENT-FACTOR-LOCALIZATION.md (0e77962a...). The discussion below explains how their existential constants can be selected without a general exponential equality oracle, at the certified rational residue r=1/2 and algebraic retained pair. It does not effectivize arbitrary original G3.

## 1. Input and desired output

Input: effectively real-algebraic A_*,p_*,q_* in(0,1), with the rational paired normal c at r=1/2, the exact critical equations, rank-five tangent minor, and t_r!=0 certified. Put a=-log A_*.

Desired output: a positive rational u_0 such that every

    h=a*Lambda+H(p_*,q_*)+u*D(1/2), 0<u<u_0,

is nonattained by any finite strict COMMON word. This is an effective source-component negative-family certificate, not original joint/all-core recognition.

## 2. Certify the uniform tail inequalities by rational formulas

Clear denominators in c with a positive integer d. Define

    n(p,q)=product_lambda f_lambda(p,q)^(d*c_lambda)>0,
    L=-(1/d)log n,
    j=f_21/f_1^21-1,
    z=p/(1-p).

The universal inequality -log x>=1-x for x>0 implies

    n<=1-d*G  ==>  L>=G.                          (R)

Therefore the required lower bounds can be certified by ordinary RCF tests of rational functions:

    U: n<=1-d*[alpha*z*(q-r)^2+gamma*z^3];
    V: n<=1-d*[alpha*z*(q-s)^2-B*z^2];
    O with j<tau: n<=1-d*k*j.

Here all domains, including the complement O of U and V, are semialgebraic, all denominator factors are positive on the strict domain, and alpha,gamma,B,k,tau,z_0 and node-interval endpoints are rational search variables. The tests use universal quantification over p,q only. No logarithm occurs in them.

Why a successful rational choice exists must come from the hand estimates, not RCF alone. On U, the positive lower bound for L can be chosen with slack; for sufficiently small odds, 1-exp(-dL) preserves a fixed fraction of that bound. On V, |L|<=C[z*(q-s)^2+z^2]; replacing dL by 1-exp(-dL) loses only O(L^2), which can be absorbed by enlarging the negative B*z^2 term and reducing alpha. On O, L>=k_0*j and |L|<=||c||_1*j; restricting tau makes1-exp(-dL)>=dL/2, giving the stated rational inequality with smaller k. Thus the hand theorem guarantees success of enumeration of rational candidates and exact RCF verification.

Likewise z<=C*j on U,V is itself a rational RCF inequality. The general bounds ||W||<=j and |L|<=||c||_1*j are analytic identities already proved and need no oracle.

## 3. Effective Taylor and linear-algebra constants

The tail expansions use only derivatives of

    log(1+z)-log(1+z*q^lambda)

on rational compact boxes0<=z<=z_0, q in the fixed interior node intervals. Every required derivative is a rational function with denominator bounded away from zero. Exact rational upper bounds can be found by RCF or elementary polynomial bounds. The mixed monomial z^2*|q-r| is handled by the displayed Young inequality, so no parameter-dependent remainder coefficient is left.

The retained-body Taylor estimates use derivatives of -log(1-p+p*q^lambda) on a rational compact neighborhood of the supplied algebraic pair. Those derivatives are again rational functions with positive denominators. Rank inversion and the quantities t,k are algebraic; compute rational upper norm bounds and a positive rational lower bound for |t_r| by algebraic isolation.

These finite constants feed the explicit absorption order in the hand proof: first fix a body neighborhood small enough to absorb its quadratic term; then choose eta successively small enough to absorb eta*Z, force |V-Q/2|<=(V+Q)/4, and make the final multiplier C*P less than1. The bookkeeping consists only of finitely many additions, products, divisions by certified positive constants and rational strict comparisons. It should be written as a fully explicit constant ledger before calling the implementation complete; no ledger execution is claimed here.

## 4. Force the local hypotheses and produce a rational cutoff

After selecting an admissible small eta<=1 and retained neighborhood, shrink to a rational rectangle U_* containing the algebraic pair so that its closure is strict and, throughout U_*,

    Delta(theta_*)/Delta(theta)<=1+eta/4,
    Delta(theta)=f_21(theta)/f_1(theta)^21.

This is an exact algebraic/rational continuity condition and is verified by RCF. Also ensure U_* lies inside the required body neighborhood.

Apply the pending effective persistent-factor localization theorem to the algebraic one-factor target m_*(lambda)=A_*^lambda*f_lambda(theta_*), with forbidden rectangle U_*. It returns a rational moment radius delta>0 forcing at least one actual factor into U_*.

Set J=21*D_1(r)-D_21(r)>0, a rational number. Choose

    u_0<=min(delta,eta/(8J),1).

For0<u<u_0, the perturbed moments differ from m_* by at most u, since0<D_lambda(r)<1 and1-exp(-uD)<=u. Every hypothetical realization therefore has a factor theta in U_*. Dividing by that actual factor's signature gives the true remainder ratio

    Delta_tail=Delta(theta_*)*exp(uJ)/Delta(theta).

Because uJ<=eta/8, exp(uJ)<=1+eta/4, and the rectangle bound yields

    Delta_tail<=(1+eta/4)^2<=1+eta.

Thus both hypotheses of the local all-tail contradiction are forced for EVERY hypothetical source. This proves the desired cutoff once the preceding proof obligations and ledger are accepted.

## 5. An effective algebraic negative input, if the algorithm is completed

Choose k large enough that2^(1-k)<u_0 and put b=1-2^(-k). Then0<-log b<u_0. The six coordinates

    m_lambda=A_*^lambda*f_lambda(theta_*)*b^(1-2^(-lambda))

are effectively real algebraic and would be certified source-component NO. This selection uses a rational bound on -log b, not a transcendental equality test.

The method is not implemented, no u_0 or k has been returned, and the new analytic proof/outer-model premises are still under independent review. Even if fully accepted and executed, it would settle this exact local COMMON family rather than unknown residues, arbitrary retained critical configurations or the full original joint/all-core problem.
