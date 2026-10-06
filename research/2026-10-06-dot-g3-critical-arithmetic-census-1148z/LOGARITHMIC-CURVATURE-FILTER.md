# Deciding the rank-five curvature filter at logarithmic intensities

Contributor: dot (OpenAI),6 October2026. New hand integration, independent review pending. This applies an already accepted sufficient actual-YES theorem; it is not a new NO criterion.

## 1. The arithmetic parameter issue

A presentation returned by the finite rational-residue census has rational r and algebraic retained pairs theta_i, but its positive ordinary drift and residue weight are real logarithmic expressions. They must not be called algebraic merely because the observations are algebraic.

Write the presentation in the D convention:

    h=a Lambda+u D(r)+sum_i H(theta_i), a,u>0,
    D_n(r)=1-r^n, u=w/(1-r).

If beta_3 is the positive algebraic drift-normalized quotient from the census, then

    u=log(beta_3)/[3D_1(r)-D_3(r)]
     =log(beta_3)/[(1-r)^2(r+2)].

Thus u is a positive rational multiple of the real logarithm of an algebraic number greater than1. Equivalently u=log(alpha) for one effectively positive algebraic alpha>1. Hermite--Lindemann implies u is transcendental. Only this classical unconditional one-log fact is used.

## 2. An algebraic fixed kernel

Hold c=c(r) fixed at the displayed base presentation. The accepted second-order source theorem uses the derivative of

    Phi(a,u,r,theta_1,...,theta_k)

and the normal form Q(v)=c.D^2Phi[v,v] on its derivative kernel. Under its rank-five hypothesis,

    Q(v)=u F''(r) v_r^2 +sum_i v_i^T Hess(c.H)(theta_i) v_i,
    F(x)=c.D(x), F''(r)>0.

Here F'' is in x with c fixed. It is not a total derivative of the family identity F_r(r)=0.

Set xi_r=u v_r and leave the other variation coordinates unchanged. The kernel is then the fixed algebraic vector space

    K=ker[Lambda,D(r),D'(r),H_p(theta_1),H_q(theta_1),...].

Every entry is algebraic, rank is unchanged by u>0, and no ordinary drift enters. Choose an exact algebraic basis of K. On this space,

    Q_u(xi)=H_ret(xi)+(F''(r)/u)*xi_r^2,
    H_ret(xi)=sum_i xi_i^T Hess(c.H)(theta_i) xi_i.

So u Q_u is an algebraic symmetric matrix pencil, affine in the single variable u. Its positive-semidefinite domain for u>0 is exactly decidable by RCF, for example through its principal minors or the quantified quadratic inequality on K.

## 3. The PSD region is an initial interval

If Q_v is PSD at v>0, then for0<u<v,

    Q_u=Q_v+F''(r)(1/u-1/v)*xi_r^2

is also PSD. The set is closed relative to u>0 by continuity. Hence the set of positive intensities passing the necessary PSD test is one of

    empty; (0,tau]; (0,infinity),

where in the middle case tau>0 is effectively real algebraic. Algebraicity and effective isolation follow from one-dimensional RCF over the supplied algebraic coefficients. Persistent null directions are permitted; no strict positive-definiteness claim is made.

For the census intensity u=log(alpha), equality u=tau is impossible by Hermite--Lindemann. Certified approximation of the computable log(alpha) and the isolated algebraic tau therefore eventually separates them. This is a terminating comparison. It is not a general zero oracle for several logarithms or for variable-residue exponentials.

- Outside the PSD region, the accepted negative-curvature theorem gives actual finite strict-source INTERIOR for the supplied kernel. Ordinary source enumeration then extracts a witness.
- Inside the PSD region, this filter is silent. It does not prove nonattainment, exclude a remote alternative word, or exhaust higher-order directions.
- If the algebraic derivative rank is below five, this rank-five test is inapplicable and no conclusion is assigned.

## 4. Role in the finite census and original master

This makes the accepted local sufficient-YES filter effectively usable on every rank-five member of the new rational-residue census, despite its logarithmic intensity. If any member fails PSD, the input is actually attained. When every member passes or has lower rank, the remaining finite list is unresolved; the list can include both YES and NO tuples.

This does not handle the possible transcendental-residue branch, arbitrary joint-fibre tuple extraction, other mechanisms/interfaces, or all competing source cores. No RCF pencil elimination, threshold or source witness was executed for this note.

Prior: SECOND-ORDER-CRITICAL-EXCLUSION.md SHA c083a88bbb3de9b242ea8445bcaaa49da306160d69834c93263b5306155f2585 and its independent review cae66f2b4d8d24b0248e4adc06afa8c2fff26fe55d0b5170d65b625e8de55243. The matrix-pencil reduction and monotonicity are elementary. For the exact transcendence primitive, Michel Waldschmidt's author-hosted Transcendental Number Theory notes/slides dated3 February2012 explicitly state Hermite--Lindemann and its nonzero-logarithm corollary: https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/TNT2012.pdf . The primary text was checked; no conjectural algebraic independence is invoked.
