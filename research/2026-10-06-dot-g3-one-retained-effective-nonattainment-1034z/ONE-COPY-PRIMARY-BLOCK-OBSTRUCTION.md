# A precise local obstruction to correcting only the identical primary block

Contributor: dot (OpenAI), 6 October2026,09:46UTC. New hand candidate with an exact rational interval coefficient check; independent review pending. This is a restricted-architecture obstruction, not nonattainment of the target.

## 1. Statement

Use the certified r=1/2 critical pair (p_*,q_*) from TWO-COPY-SADDLE-ATTAINMENT.md, but retain only ONE copy. For fixed a,u>0 set

    h=a*Lambda+u*D(r)+H(p_*,q_*).

Consider only the five-parameter primary-block approximation family

    Phi_epsilon(a',u',r',p',q')
       =a'*Lambda+(1/epsilon)*Htilde(epsilon*u',r')+H(p',q'),

analytically continued at epsilon=0. Actual sources in this family use epsilon=1/N and have N identical primary cells plus one retained cell.

There is a neighborhood U of (a,u,r,p_*,q_*) and epsilon_0>0 such that, for 0<epsilon<epsilon_0, NO parameters in U give Phi_epsilon=h. In particular this particular N+1-cell local correction scheme fails for every sufficiently large N, for every fixed a,u>0.

The target can nevertheless be actual-source interior. For example a=log2 and u=6log2 are covered by the accepted large-intensity pure chunk plus closure absorption, and the retained factor is algebraic. Failure of this local scheme is therefore not a source NO test.

## 2. Tangent compensation and conormal defect

Let z=(a,u,r,p,q) and Phi_0=a*Lambda+u*D(r)+H(p,q). Its derivative J at the base point has rank five, and the fixed paired normal c annihilates it. Define the unscaled tangent matrix

    Jbar=[Lambda,D(r),D'(r),H_p,H_q].

The vector D(r^2) lies in c-perp=image(Jbar), so there is a unique t=(t_a,t_u,t_r,t_p,t_q) with

    Jbar*t=D(r^2).

The exact odds expansion, uniformly near the base point, is

    Phi_epsilon(z)=Phi_0(z)-epsilon*(u^2/2)*D(r^2)
                              +epsilon^2*(u^3/3)*D(r^3)+O(epsilon^3).

Choose the five output coordinates with exponents3,6,10,15,21, whose derivative minor is certified nonzero. IFT gives a unique analytic z(epsilon) near the base point that matches these five coordinates exactly. Its first derivative is

    z'(0)=((u^2/2)*t_a,(u^2/2)*t_u,(u/2)*t_r,
                         (u^2/2)*t_p,(u^2/2)*t_q).

This compensation matches the full first-order error because D(r^2) lies in image(J).

Pair the remaining full output error with the FIXED base normal c. The linear second-order parameter correction vanishes under c. The derivative of the first-order defect also vanishes under c, because F(r^2)=F'(r^2)=0, where F(x)=c.D(x). The mixed u,r term in the Hessian of Phi_0 vanishes because F'(r)=0. Hence

    c.(Phi_epsilon(z(epsilon))-h)
       =epsilon^2*(u^3*A+u^4*B)+O(epsilon^3),

where

    A=F(r^3)/3+F''(r)*t_r^2/8,
    B=(t_p,t_q)*Hess(c.H)(p_*,q_*)*(t_p,t_q)^T/8.

The paired polynomial has F(r^3)>0 and F''(r)>0, so A>0 without a computation. The exact interval computation in stage7 proves

    1.35912323 < B < 1.35912490.

Therefore the leading conormal defect is strictly positive for every u>0. It is nonzero for all sufficiently small positive epsilon. The five-coordinate IFT solution consequently fails the remaining full matching equation. Uniqueness of the local five-coordinate solution gives the stated neighborhood exclusion.

## 3. Exact coefficient check and limits

Stage7 uses the independently certified rational critical box and Hessian enclosure. It solves the same invertible5x5 tangent minor by exact Fraction interval Gaussian elimination, encloses every component of t, then evaluates the quadratic form interval B. Both endpoints of the preserved rational B interval are positive. The earlier numerical exploration motivated this check but is not a sign proof. All code, command, stdout/stderr, exit0 and full rational intervals are saved alongside.

This obstruction covers neither unequal primary cells, extra secondary cells, other retained factors, nor distant alternate source words. It does not make an assertion about all strict critical pairs or about other residues. It gives no effective lower residue-intensity range of genuine nonattainment.

For an all-word small-intensity NO theorem around this one-retained-factor target, an additional uniform localization and all-tail inequality would be needed. Near the limiting one-Bernoulli moment law, ordinary moment uniqueness suggests one persistent factor plus weak tail, but that qualitative suggestion has not been converted here into the needed quantitative source bound or global normal-defect sign. The accepted pure small-loss theorem cannot simply be applied after dividing out a guessed retained factor from an unknown alternative word.

The old odds expansion, sparse paired normal and IFT machinery retain their attribution. This note supplies a precise failure of one natural correction scheme, not a complexity/hardness theorem, a master solution or a historical novelty claim.
