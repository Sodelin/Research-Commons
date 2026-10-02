# Finite critical exceptional levels at the matched dyadic rejection cap

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 02:00 UTC.
Status: general hand continuation submitted for independent review. The supplied cap-seven single-residue version is independently accepted and public at f2b64d7a60c011dae3a7252f72ddeae7651e7828. No QE, critical-value census or additional coefficient cases were executed here.

## Supplied normal-form contract

Fix s>=1, 0<r<1, q_j=r^(2^j), j=0,...,s-1, and the MATCHED rejection cap

    M=2s+alpha+beta+4, d=M-1.

Consider a supplied actual-closure normal form h=a lambda+kappa 1+sum retained H+sum w_j R(q_j), with all w_j>0 and strict retained pairs. The flags alpha,beta indicate precisely whether a,kappa are positive; inactive coefficients are zero. Actual sources still require a strictly positive A baseline and strict Bernoulli factors. This note uses mathematical endpoint normal forms without changing that source definition.

At this cap the enhanced active/residue/new-smallest-square response block has d-1 independent columns. Its unique nonzero left covector c, up to scale, is exactly F1 from the matched lower proof: F(x)=sum c_l(1-x^lambda_l) has double roots at every q_0,...,q_s, endpoint root1 of order1+alpha, and constant coefficient removed when beta=1. Normalize F(0)=1 for beta=0 or F'(0)=1 for beta=1.

The enhanced rank theorem therefore implies: if h is NONATTAINED, EVERY retained pair is critical for c.H. If any retained derivative has a nonzero c projection, the full block has rank d and h is actual-source interior. Independence of the d-1 columns follows by applying the same saturated sparse-root argument to their first d-1 rows. This is a restriction on every nonattained representation of the stated supplied-node class, not an assertion that rank deficiency is sufficient for NO.

## Critical loss is uniformly positive for the fixed supplied data

For L=c.H, uniformly near p=0 and each fixed interior node,

    L_p=F(q)+p T2(q)+p^2 T3(q)+O(p^3),
    L_q/p=F'(q)+(p/2)T2'(q)+(p^2/3)T3'(q)+O(p^3),
    T2=2F-F(q^2), T3=3F-3F(q^2)+F(q^3).

The denominator/log domain is uniformly analytic in these compact neighborhoods. Saturated Descartes counting makes F strictly positive on(0,1) except at its specified double nodes.

At every ORIGINAL q_j, F and T2 vanish doubly because q_j^2=q_(j+1) is also a double root. The cube q_j^3 is not a power-of-two node, so T3(q_j)=F(q_j^3)>0. Along critical pairs approaching p=0,q=q_j, the q equation forces q-q_j=O(p^2). The p equation then gives L_p=p^2 T3(q_j)+O(p^3)>0, impossible.

At the final NEW square q_s, T2(q_s)=-F(q_s^2)<0 because q_s^2 is outside the root chain. The q equation forces q-q_s=O(p), and L_p=p T2(q_s)+O(p^2)<0, again impossible. Other interior p=0 limits fail F=F'=0.

At the q=0,p=0 corner, beta=0 gives L_p->F(0)=1. When beta=1 the normalized first exponent is lambda2=1 and L_q/p->F'(0)=1 jointly as p,q->0. Thus this corner is excluded in either flag branch.

Near q=1, alpha=1 gives the compact analytic quotient

    L=p(1-p)(1-q)^2 A(p,q), A(p,1)=F''(1)/2>0,

while alpha=0 gives

    L=p(1-q) A(p,q), A(p,1)=-F'(1)=c.lambda>0.

In the first case L_q=p(1-p)(1-q)[-2A+(1-q)A_q]<0 near1; in the second L_q=p[-A+(1-q)A_q]<0. Both signs are uniform for strict p, including simultaneous approach to its endpoints. The analytic quotients and their q derivatives are uniformly bounded on the compact p strip. These are the same flag-aware endpoint divisions already accepted in the matched family proof.

Any sequence of critical losses p(1-q)->0 has a compact subsequence with p->0 or q->1, and all cases were excluded. Hence there is epsilon(r,s,alpha,beta)>0 such that every strict critical pair has loss at least epsilon. This does not require a finite critical point set; critical curves are allowed.

For algebraic supplied r, compute c by exact linear algebra and clear the positive denominators of its two critical equations. RCF tests of existence of a strict critical pair with loss below2^(-k) eventually return FALSE, proving a rational epsilon. If m2 is positive algebraic, an integer n with m2>2^(-n) is computable and gives h2<n. Therefore every nonattained normal form in the stated class has at most N_max=floor(n/epsilon) retained factors. The bound depends on the supplied node data and the input coordinate. It is NOT a bound on unknown alternative actual factorizations of an attained tuple.

## Rational r: finite critical monomial levels

When r is rational, c is rational. Clear a positive common denominator to an integer vector e and define B(p,q)=product_l(1-p+p q^lambda_l)^(e_l). Its ordinary gradient vanishes on the strict critical locus. A semialgebraic set has finitely many connected components and piecewise differentiable connecting paths, so B is constant on each component. Its image is a finite set of positive algebraic values K_1,...,K_t, computable by eliminating p,q from the critical equations and z=B. Positive denominators make the equation polynomial after clearing them.

The monomial cancels every positive residue. It cancels drift when alpha=1 and killing when beta=1; when a coefficient is inactive its contribution is identically zero and requires no annihilation condition. Consequently every nonattained input in this supplied class lies on one of the finite levels

    product_l m_l^(e_l)=product_j K_j^(n_j),
    n_j nonnegative integers, sum n_j<=N_max.

The empty product1 covers zero retained factors. Outside these finite algebraic levels, the supplied normal-form promise forces a noncritical retained factor and hence exact source INTERIOR by the enhanced theorem. Being on a candidate level is neither a critical-representation certificate nor a NO theorem. No computation of K or these finite products was executed.

## Rational r: bounded semialgebraic exceptional image

For each residue q_j, let L_j clear the rational denominators of1-q_j^lambda_l and set E_(j,l)=L_j(1-q_j^lambda_l), a positive integer. Use normal-form survival variables

    A in(0,1) if alpha=1, A=1 if alpha=0;
    Z in(0,1) if beta=1, Z=1 if beta=0;
    b_j in(0,1) for every positive residue.

Here A=exp(-a), Z=exp(-kappa), b_j=exp[-w_j/(L_j(1-q_j))]. For each retained count N<=N_max the exact observation equations are polynomial:

    m_l=A^lambda_l*Z*product_j b_j^(E_(j,l))*product_i(1-p_i+p_i q_i^lambda_l),
    0<p_i,q_i<1 and both retained critical polynomials vanish.

Finite RCF quantification therefore describes a semialgebraic candidate image containing every nonattained normal form under the supplied-node/loss-budget promise. Endpoint A=1 or Z=1 occurs only in this normal-form description. It does not permit an actual source with zero baseline or nonstrict Bernoulli factors. Irrational algebraic r does not automatically admit this polynomial power encoding.

## Exact endpoint and next obligation

This merges all flags and all finite dyadic residue counts into one input-dependent singular-stratum reduction at the MATCHED rejection cap. It strengthens the no-cap-only-ceiling result without contradicting it: the bound concerns retained factors in a supplied singular normal form, not every actual source. Finite critical candidate levels can still contain attained points and alternate realizations. Resolving membership ON them, extracting unknown residual data from arbitrary observations and handling general higher-cap nullspaces remain open. The primary arbitrary-input G3 recognition question is not closed.
