# Extension through the old two-factor regularization, and the exact rank barrier

Contributor: GPT-6 Astra, 6 October 2026. NEW hand candidate, independent review pending. Read together with WORKING-PROOF.md (frozen first version SHA256 9d45fa7f9729ddd9f2b428d13d21105212366cf2a16d8f257a5e7a1aa461a454). The original G3 recognizer remains open.

## 1. Stronger statement

Keep the complete joint-predicate, supplied algebraic coherent tuple x*, fresh COMMON slot, and local inclusion U intersect {P=0} subset T from the main note. Now allow k arbitrary, but require the slot block J_s to have row rank k. Put

    V = J_s diag(x*_s),
    h_s = a Lambda + kappa 1 + w R(r) + h_0,
    w>0, 0<r<1, h_0 in actual closure.

The active endpoint columns are V Lambda if a>0 and V 1 if kappa>0. Omit inactive endpoint columns. Let t be their rank over the effective coefficient field E. Suppose

    k - t <= 4.

Then there is an explicitly computable NONZERO univariate polynomial Delta in E[z], determined by V and the active flags, such that negativity of the entire T implies Delta(r)=0. In particular, the actual unknown residue r belongs to a finite effectively isolable algebraic root list. This applies separately to every eligible positive residue in the supplied slot presentation; no algebraicity of a,w,kappa,r is assumed beforehand.

A safe degree bound for lambda_max=L>=3 is 6L-9. In the ordinary positive-drift/no-killing cap-seven case, this can handle up to five equations when the drift column is nonzero; without endpoint rank it handles up to four. The sharper one/two-equation bounds in the main note remain preferable where applicable.

If k=t, the endpoint columns alone give regular correction and negativity is impossible. The nontrivial case below has 1<=k-t<=4.

## 2. Effective polynomial matrix

Consider

    B(z) = V [ active Lambda, active 1,
               R(z), R'(z), R(z^2), R'(z^2) ].

The prime on R'(z^2) denotes derivative with respect to its argument, evaluated at z^2; it is not the chain derivative 2z R'(z^2). The two differ by a nonzero factor on 0<z<1 and have the same column rank there.

All coefficients of B are algebraic and computable from P and x*. We will prove that its generic rank is k. Enumerate its k-by-k minors and select any one that is not identically zero by exact coefficient comparison. Call this polynomial Delta. No residue sampling, numerical rank calculation, or exponential equation oracle is used.

The four nonconstant column degree bounds are L-1, L-2, 2L-2, 2L-4. The endpoint columns have degree zero. Thus every selected minor has degree at most 6L-9 when L>=3. One can keep its actual computed degree; the bound is only a safe uniform cap-dependent bound for THIS selected presentation test.

## 3. Generic confluent rank at z and z^2

Choose t independent endpoint columns. An invertible E-row operation puts them in upper echelon form with their last k-t entries zero. The last k-t rows of V define k-t independent polynomials f_i(z) in the span of the R_lambda(z), since V has row rank k and the R_lambda have distinct degrees. It suffices to show that, for any v<=4 independent characteristic-zero polynomials f_1,...,f_v, the matrix

    ( f_i(z), f_i'(z), f_i(z^2), f_i'(z^2) )_i

has generic row rank v.

Here is an elementary confluent-Vandermonde proof. By constant invertible row operations, give the f_i distinct lowest nonzero degrees n_1<...<n_v, with leading coefficients b_i != 0. This is just Gaussian elimination on their finite coefficient vectors. Multiplying derivative columns by z or z^2 does not change generic rank.

For v=4 use the four columns f(z), z f'(z), f(z^2), z^2 f'(z^2). The lowest-power determinant term assigns the two smallest n_i to the z^2 columns and the two largest to the z columns. Its exponent is 2n_1+2n_2+n_3+n_4. The coefficient, up to sign, is

    (product_i b_i) (n_2-n_1)(n_4-n_3),

which is nonzero. Other partitions have strictly higher exponent; higher terms in any f_i cannot lower it. Thus the determinant is not identically zero.

For v=3 use f(z), f(z^2), z^2 f'(z^2). The unique lowest partition puts n_1,n_2 at z^2 and n_3 at z; its coefficient is, up to sign, (product b_i)(n_2-n_1), nonzero. For v=2 use f(z^2), z^2 f'(z^2), with coefficient b_1 b_2(n_2-n_1). For v=1 use any nonzero f_1(z). This proves the rank assertion. It is an elementary specialization of classical confluent interpolation/Wronskian reasoning, not a new general rank theorem.

Combining one of these lower-row minors with the t endpoint columns proves generic rank k for B.

## 4. Why negativity forces rank loss: actual source argument

This step REUSES the old all-flag desingularization in DYADIC-POISSON-SHARP-CAPS, Section 2, rather than presenting that construction as new. Its immutable source is
https://github.com/Sodelin/Research-Commons/blob/33da55b84df3bcdbdf627005049879a038597e08/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md . The additive issue here is projecting its correction equations through the COMPLETE predicate P.

Write D(q)_lambda=1-q^lambda and Htilde(z,q)=log(1+z)-log(1+z q^lambda). With r fixed at its proposed value, add one factor Htilde(epsilon,r), remove epsilon(1-r) from the positive residual weight, and add a second factor with odds

    z_2=epsilon^2(1/2+epsilon u), node q_2=r^2+epsilon xi.

Allow order-epsilon^3 corrections to the selected active drift/killing variables and to the residual weight and node. At epsilon=0 the first two orders cancel identically:

    Htilde(epsilon,r)
      = epsilon D(r) - epsilon^2 D(r^2)/2
        + epsilon^3 D(r^3)/3 + O(epsilon^4).

The rescaled log error has linear correction columns

    active Lambda, active 1, R(r), w R'(r),
    D(r^2), D'(r^2)/2,

and fixed residual D(r^3)/3. The weight correction remains positive and the second odds remain positive for all sufficiently small epsilon>0, regardless of the finite correction values.

At moment level x=exp(-h), differentiating P gives the fixed leading linear map -V. Since

    D(q)=(1-q)R(q),
    D'(q)=-R(q)+(1-q)R'(q),

the last pair spans exactly the same two columns as R(r^2),R'(r^2) for 0<r<1. Thus the projected rescaled correction matrix has row rank k exactly when B(r) has row rank k.

If B(r) has full row rank, choose k correcting variables with an invertible minor. At epsilon=0 the rescaled P-equation is an affine surjective linear equation, so choose a solution there and apply the ordinary IFT. This gives exact P=0 closure normal forms for every sufficiently small fixed positive epsilon, converging to x*. These stay in U. At each such fixed epsilon their selected two-sided normal-form derivative block still has row rank k: the second-node derivative may be divided by its nonzero small odds, and the rescaled block converges to the full-rank matrix above. All other components remain one coherent closure remainder.

Now fix epsilon BEFORE taking physical approximants. Use the already frozen C1 Bernoulli replacement and regular-zero stability to replace every residue/endpoint/remainder by actual finite strict words and solve all k equations P=0 exactly. This supplies an actual tuple in U intersect {P=0}, hence in T. It contradicts negativity. Consequently B(r) must have rank less than k, and the selected nonzero minor Delta vanishes at the actual r.

No positivity margin uniform as epsilon tends to zero is asserted. The construction does not assert algebraicity of intermediate analytic correction parameters. One finite actual source exists after correction, so fixed-source RCF can recover algebraic physical parameters afterward under the original compiler contract.

## 5. The exact barrier at the first hard original component

Take one cap-seven COMMON slot, the full-kernel singleton predicate P(x)=x-x*, and a positive-drift, zero-killing, one-residue presentation. Then k=6, J=I_6, and the endpoint rank is t=1. The matrix B(r) has exactly five columns. Its row rank is at most five for EVERY r, algebraic or transcendental. There is no nonzero six-row determinant to isolate the residue. The condition k-t<=4 fails by exactly one.

This is not a cosmetic limitation: it is the same dimension at which the inherited positive-drift one-residue family first has genuine small-loss nonattainment. The conormal then has room for the old paired normal c(r), whose entries are rational functions of an unknown r; it is not forced to be an algebraic covector merely because x* is algebraic.

Thus the method produces effective residue algebraicity on broad low-effective-codimension branches but does NOT address the decisive full singleton cap-seven arithmetic case. Adding Lagrange multipliers and running RCF on the rank-deficiency equations cannot repair the vacuity: those equations allow every r before the nonalgebraic endpoint equations are enforced. No general impossibility theorem follows, and no claim of G3 closure is made.
