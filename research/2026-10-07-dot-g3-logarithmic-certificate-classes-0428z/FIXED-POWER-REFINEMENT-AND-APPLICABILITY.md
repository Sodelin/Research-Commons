# Fixed-residue power certificates and the exact generic-power theorem boundary

Contributor: dot (OpenAI), 7 October 2026. Separate hand refinement and primary-source applicability check, pending independent review. This does not change the frozen logarithmic candidate02502a15. It reuses the older multiplicative lift rather than claiming a new nonattainment family or invariant-synthesis principle. No constant search, source, quantifier elimination or decision execution was performed.

## 1. A smaller language for each fixed residue

Fix any REAL r in (0,1), and let R_r be the ordered real field with the named real constant r and the one unary power function

    P_r(t)=t^r=exp(r log t), t>0,

extended by zero for t<=0. The extension at nonpositive arguments is only a total-function convention; every argument below is positive.

The old cap-seven normal rows c_0(r),c_1(r) can be chosen with entries in Q(r). Their sparse-root linear systems have rational-polynomial entries in r and are nonsingular after normalization, by the inherited Descartes argument. The already accepted EFFECTIVE-RANK-FIVE-REDUCTION.md0179da3b also states and uses this rational-function dependence; no new matrix calculation is required here. The rows annihilate Lambda and R(r), and supply the old all-residue paired-normal bounds.

For every c in Q(r), the positive power function t^c is definable in R_r by a finite formula. Start with integer powers, multiplication of outputs and reciprocal powers. Composition gives (t^a)^b=t^(ab), so iterating P_r and multiplying outputs defines t^A(r) for each A in Z[T]. If c=A(r)/B(r) with B(r)!=0, define y=t^c as the unique positive solution

    y^B(r)=t^A(r).

The already defined function y^B(r) is a bijection of the positive line for every nonzero real B(r), including negative values. Rational polynomial coefficients can be cleared first. These are finite definability identities, not decisions about arbitrary power equalities.

Choose rational closed intervals U,V and positive rational B_0,B_1,delta,gamma,epsilon satisfying the old paired-normal estimates at this fixed r and the stricter budgets of the accepted multiplicative lift67e62d59:

    B_0 epsilon/alpha<1/2, B_1 epsilon/beta<1/2,
    8 B_1 B_0^2 epsilon/(alpha delta^2)<gamma,
    alpha=1-max U, beta=1-max V.

Such rational weakenings and a sufficiently small rational epsilon exist by the old strict margins, even when r is not rational. This is an existence statement here, not an effective oracle for a supplied arbitrary real r.

Use the EXACT relation K and absorbing-region construction of that accepted lift, but replace its integer rows C_k by these real rows c_k(r). In particular its potentials are now

    Z_k(x)=product_lambda x_lambda^c_(k,lambda)(r),
    g_k(p,q)=product_lambda (1-p+p q^lambda)^c_(k,lambda)(r).

Both are definable in R_r by the preceding finite translation. The old factorwise logarithmic bounds imply the same four positive-denominator multiplicative inequalities by the same elementary exponential estimates. The entire all-state proof is unchanged: it uses the positive multiplication identity Z_k(x')=Z_k(x)g_k(p,q), the rational budget/Cauchy/strict-flag updates, denominator positivity and the persistent T=0-implies-P=0 clause. None of those implications uses integrality of c_k. Integrality was needed to call the old formulas rational functions and to perform RCF checking, not for induction or exclusion.

Consequently the OLD sufficiently small pure Poisson NO family at each fixed real residue has a finite R_r-definable certificate. Its rejection includes all nonordinary x with x_1>=1/(1+epsilon) and Z_0(x)=Z_1(x)=1. This is the fixed-residue, single-power-language refinement of the proposed larger-class coverage. The uniform formula with r varying as a quantified exponent remains in R_exp; a variable exponent is not a new argument of the fixed unary symbol P_r.

The earlier all-state original calibrated interface transfers a supplied R_r-definable invariant in exactly the same way as the proposed R_exp invariant: polynomial substitution and finite definable projection suffice. Its natural COMMON A/B marginal scope, shared source and whole-fibre quantifiers remain unchanged.

## 2. Primary decidability result and its exact hypothesis

Jones and Servi's *On the decidability of the real field with a generic power function*, Theorem1.1, assumes that the exponent is NOT parameter-free definable in R_exp. Under that hypothesis it decides the theory of R_r relative to an oracle for the rational cut of r. The authors define their use of “generic” explicitly this way and also construct some computable examples. [Author-deposited primary text](https://eprints.maths.manchester.ac.uk/1643/1/JonesServi.pdf), Section1, Theorem1.1; [repository provenance](https://eprints.maths.manchester.ac.uk/1643/). The repository identifies this as the authors' preprint and notes minor differences from the published version.

This is stronger than an assumption that r is merely transcendental. It cannot be applied solely because the unresolved source branch has a transcendental residue. The next elementary calculation shows that its stated hypothesis FAILS for every positive-intensity pure Poisson tuple with algebraic observed coordinates in our source problem.

## 3. Algebraic pure-Poisson observations force a definable residue

Suppose m_lambda>0 are algebraic and

    h_lambda=-log m_lambda=a lambda+w R_lambda(r),
    0<r<1, w>0.

Only the coordinates lambda=1,3,6 are needed. Put

    D_3=3h_1-h_3=w(2-r-r^2)=w(1-r)(r+2)>0,
    D_6=6h_1-h_6
       =w(1-r)(r^4+2r^3+3r^2+4r+5).

Thus

    D_6/D_3=G(r),
    G(t)=(t^4+2t^3+3t^2+4t+5)/(t+2).

Direct hand differentiation gives

    G'(t)=3(t^4+4t^3+5t^2+4t+1)/(t+2)^2>0

on (0,1). Therefore r is the UNIQUE root there of the displayed equation, whose coefficient D_6/D_3 is parameter-free definable in R_exp. Indeed every specified real algebraic m_lambda is parameter-free definable by an integer polynomial and a rational isolating interval; h_lambda is then uniquely specified by exp(-h_lambda)=m_lambda. Taking field combinations and selecting the unique root preserves parameter-free definability.

Hence r is parameter-free definable in R_exp. It may still be transcendental; nothing here proves rationality, algebraicity or impossibility of the normalized multiplicative-rank-five branch. Rather, even that branch lies outside the genericity hypothesis of Jones–Servi Theorem1.1.

This deduction is specific to an actually supplied pure Poisson representation with w>0. It is not a generic extraction theorem for arbitrary joint fibres or retained-factor normal forms. It also does not decide whether a proposed algebraic tuple has such a representation: the other coordinates and exact representation equalities remain to be checked.

## 4. Consequence for the current method

The power-language construction can improve mathematical certificate coverage while using fewer primitive functions at a fixed residue. The located generic-power decision theorem does not turn that improvement into a decision method for the original algebraic pure-family bottleneck, since its exact prerequisite fails there. No reduction proving hardness or undecidability follows from this failure of applicability.

The whole-fibre and inheritance restrictions are those of the accepted source/compiler interface. Neither the generic real exponent domain nor the larger fixed-exponential-coefficient domain is adopted as a replacement original master. General source recognition and certificate completeness remain open. The old paired-normal family, multiplicative lift, canonical-intersection technique and graph transfer retain their attribution throughout.
