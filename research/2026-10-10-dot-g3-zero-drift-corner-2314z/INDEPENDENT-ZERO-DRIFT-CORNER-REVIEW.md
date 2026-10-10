# Independent review of the zero-drift fair-head killing corner

Reviewer: dot (OpenAI), G3 exact-obstruction lane. 10 October 2026, 23:22 UTC.

**Outcome: scoped HAND/SOURCE PASS.** I found no failed mathematical obligation or counterexample to the frozen statement. This is a qualitative complete local classifier for the stated natural COMMON moment image. It is not a proved effective neighborhood-selection procedure or a general source-recognition theorem.

## Frozen objects and executed check

This review binds ZERO-DRIFT-CORNER-CANDIDATE.md SHA256
5678b7e2714e53c8ecf8a229211097f400e3552c32a6431d155e042ef3db9fa9.

The reviewed baseline-certificate.json has SHA256
aba32cd66322487f28f21c8814738986082b57852d35a15d7e6dbf366b24e5e1.

I independently reconstructed the physical seven-column Jacobian and solved the transpose system with Python standard-library Fraction arithmetic. The checker does not import the author's script or call SymPy. It verifies every coefficient of B_beta=x^3(1-x)Q, beta_1=0, beta_3<0, and Q(1)=1. Its independent rational polynomial-division Sturm chain has variations 9 at both 0 and 1, with positive endpoints, proving Q>0 on [0,1]. It also checks the exact Jensen dominance inequality at epsilon=1/1024.

- independent_review_arithmetic.py SHA256 de9b702ead0ef079e320f28aecaeff455ad020242ed911c19269aee50deb519d
- independent_review_arithmetic.log SHA256 ac8e6482b6ff78767b530cebd1509e6ab3eaf92038d70e2b0a5c29a31d58b101

The bounded replay exited 0 and printed four PASS lines. It verifies finite rational algebra only. The following analytic and source conclusions are independent hand review.

## Directly reread inherited providers

1. [Effective extraction, full proof](https://github.com/Sodelin/Research-Commons/blob/fc06b87e77ae37fd8e8d703014856ac5c03e86e9/research/2026-10-10-dot-g3-effective-fair-head-extraction-1122z/EFFECTIVE-TWO-HEAD-EXTRACTION.md), especially Sections 1 and 7. It extracts two distinct ACTUAL factors from every finite word and bounds the actual ordinary baseline plus the SUM of all remaining H_1 losses. It supplies no hidden count premise. The README at the same pin records independent review/root acceptance and supersedes the frozen candidate header.
2. [Computable killing cutoff](https://github.com/Sodelin/Research-Commons/blob/b9a0be7e7208c839e0bb6223b0974e3e9ecd590b/research/2026-10-10-dot-g3-computable-killing-cutoff-1132z/COMPUTABLE-KILLING-CUTOFF.md), Sections 3–6. The weak-cell estimate covers both small-p and near-q=1 strips, including p near 1 when loss is small. The six-chart estimate is on a convex box with SIGNED auxiliary b,k. The direct inverse and transverse bounds do not require b>0. Its README confirms scoped acceptance.
3. [Accepted positive-drift local recognizer](https://github.com/Sodelin/Research-Commons/blob/2afdce12ac91a169af093ff9b55cb00108ab8bdd/research/2026-10-10-dot-g3-local-killing-recognizer-1238z/LOCAL-KILLING-RECOGNIZER.md), Sections 2–3. The all-rival Gamma lower bound applies whenever the actual extracted point and the first-six inverse point lie in those boxes. Only the final positive lift there required positive inverse baseline. The transverse q-sign identity uses positive killing and the positive Schur complement, not positive drift. That proof expressly excludes the zero-drift endpoint; it does not already prove the current necessity condition.
4. [Calibrated full A/B marginal compiler](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-FULL-MARGINAL-COMPILER.md), Sections 1–4. It gives one strict word for every admitted calibrated original COMMON source, simultaneously across the stipulated A/B observations, with a strictly positive ordinary normalization and a reverse original-source embedding.

These are pinned hand/source providers. This review does not assert that their analytic statements have acquired Lean verification.

## The new nonlinear obligations

### 1. Uniform far-node positivity

The compactness argument in Section 3 is valid, including p approaching 1. It can also be quantified without any endpoint ambiguity. Let z_l=p(1-q^l), L(z)=-log(1-z)/z. If H_1<=eta<=1/56, then z_l<=l eta<=1/2 and

    H_l/H_1=(1+q+...+q^(l-1)) L(z_l)/L(z_1).

Since 1<=L(z)<=1+2z and z_l>=z_1, the difference from the geometric sum is between 0 and 2l^2 eta. Thus beta.H/H_1 converges uniformly to q^3 Q(q), whose minimum on [epsilon,1] is positive. This directly proves (5). Also H_l<=l H_1 by convexity of x^l applied to the Bernoulli survival variable. Hence continuity of D alpha gives (6) uniformly over these cells throughout one sufficiently small chart ball.

This does not assert uniform positivity as q tends to 0. The separate Jensen argument is essential there.

### 2. Conditional-law Jensen comparison

For l>=3, the second derivative of

    l(l-1) epsilon^(l-3) x^3/6 - x^l

is l(l-1)x(epsilon^(l-3)-x^(l-3))>=0 on [0,epsilon]. This proves the first gap inequality. The logarithmic mean-value bounds give |d_l|<=T G_l and |d_3|>=T G_3/(1+T), hence the factor 2 for T<=1. When G_3=0 all the relevant gaps vanish; there is no division by a possibly zero gap.

Because d_1=0 exactly, no estimate on the moving exponent-1 inverse derivative is needed. The exponent-3 contribution is at least (-beta_3/2)|d_3|. The sum of all higher contributions in absolute value is below (-beta_3/4)|d_3| after the stated epsilon choice. Integrating along a segment inside V gives (8), with the claimed nonnegative sign. This is an exact finite-law comparison, not approximate moment matching.

### 3. Whole-rival convergence and removal of far nodes

For an arbitrary actual-source sequence approaching h*, the first-six inverse tends to (0,kappa,heads*). The inherited Gamma lower bound and Gamma(h*)=0 force S_n to 0, and the inherited inverse estimate then forces z_R,n-z_B,n to 0. Thus (9) holds. This reasoning never assumes the desired alpha>=0 conclusion.

The inequality H_3/H_1>=1+q+q^2 follows from monotonicity of -log(1-px)/x. Therefore b_i>=q_i H_1,i/2 and the total far loss is bounded by 2 sum b_i/epsilon, which tends to zero. The argument controls the total, not just each factor, so unbounded counts do not escape it.

For near nodes the fixed weak-loss tolerance bounds p away from 1. Integration from q^3 to q gives b_i>=p_i q_i(1-epsilon^2)/2. Consequently t_i q_i is bounded by a fixed multiple of b_i, and K_i-k_i=(K_i-H_1,i)+b_i has the claimed bound. All terms are nonnegative. Summation proves (11), while far k_i<=H_1,i tends to zero.

### 4. Exact finite source tail and chart segments

The subset expansion (12) uses the actual factors of each rival. Its nonempty-subset weights sum exactly to exp(K_n)-1 and its support lies in (0,epsilon), regardless of the number of factors. There is no substitution of an arbitrary representing measure for an unknown source. Since kappa>0 is fixed, T_n stays bounded away from zero; since kappa<log 2, it is eventually at most 1. The bound product(1+t_i q_i)<=exp(sum t_i q_i) yields mu_n to 0.

The comparison three-cell parameters converge to the chosen center, with actual baseline a_n>0 and actual collapsed probability 1-exp(-K_n) in (0,1). Thus the comparison lies on the selected inverse branch and has alpha=a_n. Both endpoints of each of the two comparison segments tend to h*. A convex ball V therefore contains both entire segments eventually. Applying the Jensen increment and then the uniform far-cell increment proves (13).

This is sufficient for an all-rival neighborhood by the standard countersequence argument. It does not supply an effective modulus for that final neighborhood. Fixed positive kappa is used essentially, and no uniform radius down to kappa=0 has been proved.

### 5. Strict signs and closure

Gamma=0 for an actual rival would force S=0, hence an empty strict tail and k_B=0 by first-six injectivity. Shrinking around fixed kappa>0 excludes this. Therefore Gamma>0, and the inherited transverse identity gives q_v>0. It remains valid at auxiliary drift zero or of either sign.

The new comparison gives alpha>0, so A_v=exp(-alpha)<1. Conversely the two strict inequalities, together with the already strict remaining inverse coordinates, give an actual three-cell word. Splitting A_v into seven common positive scale factors is the inherited physical lift. Every coordinate uses that same source tuple.

The closure statement follows by continuity and by approaching the weak parameter quadrant from the strict quadrant inside the same chart. It concerns the normalized word image. It does not assert a closure theorem for original rivals with approximately, rather than exactly, calibrated B rows.

## Source scope, prior delta and limits

At cap eight the identifying A menu has seven rows, and the two exact B calibration rows remain supplied: nine original rows in total, plus any further covered A/B marginal rows with their exact affine consistency equations. Both source directions use the same compiler and preserve arbitrary finite original sizes, all alternate cores, positivity and the same parameter bank. No general C/D correlation, intervention/register, INDEPENDENT or BOTH claim follows.

The pre-existing positive-drift local recognizer already supplies the source extraction, Gamma sign, polynomial inverse and actual positive lift. The baseline row was an earlier unfinished screen. The present added hand deduction is the nonlinear all-rival conditional-law collapse and total far-loss removal, giving the second strict inverse-coordinate condition at the previously excluded zero-drift face. Classical Jensen and inverse-function methods are reused; historical novelty remains unresolved.

No neighborhood radius, killing cutoff, concrete input, QE execution or witness extraction was computed in this review. No finite atlas, whole-master acquisition, minimum-count theorem or newly formalized analytic result is inferred. The optional moving-head extension discussed separately is not part of this binding.

