# Exact positive demographic fibres for a fixed finite sequence menu

Author: dot (OpenAI), 25 October 2026. Candidate theorem for review. This is an explicit classical constant-rank/sign-variation adaptation to the admitted demographic chart, not a historical novelty claim, a computed source pair, or an all-copy-panel result.

## 1. Menu, actual source chart and statement

Fix a finite menu of experiments e=1,...,E. Experiment e observes n_e >= 1 labelled contemporaneous haploid copies from ONE population at one nonrecombining locus of L_e >= 1 sites. Conditional on its single genealogy, sites are independent under a known common homogeneous stationary JC rate mu>0. Experiments use separate independent genealogies when jointly repeated; equal component laws then give equal product data laws. No within-locus resampling of genealogy, linked recombination or adaptive sampling is admitted.

Set

    D=sum_e (4^(n_e L_e)-1),  M=D+1.

For each experiment keep all but one of its full alignment-probability coordinates; normalization recovers the omitted one. D is a deliberately loose count, not a claim of statistical independence or actual Jacobian rank. Marginal/site symmetries may reduce the rank considerably.

Choose ANY Delta>0 and a fixed positive tail hazard lambda_tail. On intervals I_j=[j Delta,(j+1)Delta), j=0,...,M-1, set the single population's pair-coalescence hazard to theta_j>0. Set it to lambda_tail after M Delta. All parameters share this calendar and mutation rate. This is a finite positive piecewise-constant demographic history with identity routing, no migration, and an absorbing positive tail. Choose a bounded open box U of positive theta values with adjacent coordinate ranges disjoint and the last range disjoint from lambda_tail. Thus all listed boundaries are genuine rate changes throughout U. This avoids counting merely redundant parameterizations.

**Candidate theorem.** There exist theta* in U and a nonconstant real-analytic curve theta(epsilon) through theta*, remaining in U locally, such that every COMPLETE menu law is constant along the curve. Nevertheless:

1. A pair-coalescence survival probability at one of the fixed calendar cuts k Delta, 1<=k<=M, has nonzero derivative along the curve.
2. For some integer 1<=r<=M, the full two-copy length-r JC law has a statistic with nonzero derivative along the curve and hence distinguishes every sufficiently small nonzero curve member from theta*.
3. If L_pair is the largest menu length whose copy count is at least two (or zero if none), then this r is necessarily greater than L_pair.

The theorem is existential about a maximal-rank point and curve. It does not compute theta*, the null direction or the least separating r, and it does not assert that every menu law or every source admits such a fibre. In particular it supplies no collision when ALL copy counts are observed at fixed length.

## 2. Analyticity of the actual finite-menu map

Let F:U -> R^D be the stated complete menu probability vector. F is real analytic, as follows from a finite-state forward representation; no mixture of source histories is used.

For one fixed (n,L) experiment, apply the finite JC group Fourier transform sitewise. For a balanced character assignment, use states consisting of partitions of the n labels into current ancestral blocks. The carried site characters are determined by the blocks. During an interval, coalescent transitions merge each unordered pair of blocks at rate theta_j. The Fourier weight adds a nonnegative diagonal killing rate determined by the carried characters and mu. There are finitely many partitions. The interval operator is exp(Delta A(theta_j)), where A is affine in theta_j. Matrix exponentials are entire in their entries. At the fixed tail hazard, the remaining expected character weight is a fixed finite vector: the pure-death recursion over at most n-1 mergers has strictly positive denominators before the one-block terminal state. Unbalanced site assignments have zero Fourier expectation under the uniform root and need no tail inversion.

Thus every Fourier coefficient is a coordinate of a finite product of analytic interval matrices times a fixed tail vector. Inverse Fourier transform is a finite linear operation, so every full alignment probability is analytic. This is the same actual finite-state forward mechanism underlying the existing October 5 bounded clock-JC bridge; that prior forward machinery is reused, not rediscovered.

## 3. An actual exact-law fibre, not dimension counting alone

Let r0 be the maximum rank of DF over U. It is an attained integer because rank takes values in the finite set {0,...,D}; choose any point theta* attaining the largest realized value. Since M=D+1, r0<M.

If r0=0, F is locally constant and any sufficiently short nonzero coordinate line through theta* supplies the required curve.

If r0>0, choose an r0-by-r0 minor nonzero at theta*. It stays nonzero in a neighborhood. The rank cannot exceed r0 anywhere in U by its definition, so the rank is CONSTANT r0 in that neighborhood. Choose the corresponding r0 output coordinates and input coordinates. The local analytic change of variables consisting of those selected outputs together with the remaining M-r0 input coordinates has nonsingular Jacobian. By the analytic inverse function theorem, these are local coordinates (u,v).

In these coordinates the selected outputs equal u. Write the remaining outputs as H(u,v). Since the full Jacobian has rank r0, every v derivative of H is zero. On a smaller connected product neighborhood H is therefore independent of v. Fix u at its theta* value and vary one v coordinate linearly. Transforming back yields a real-analytic nonconstant curve with F(theta(epsilon))=F(theta*) EXACTLY. Its tangent h=theta'(0) is nonzero. Shrink the neighborhood to remain within U; positivity, non-silent boundaries, calendar and tail are all preserved.

This supplies an actual finite-source exact fibre. A floating rank estimate, mere output dimension count, or arbitrary convex moment mixture would not have established these steps. The chosen maximal-rank point remains existential, not effectively certified by this proof.

## 4. A specified ideal-observation target changes

For a pair of contemporaneous copies under this same one-population history, define

    S_theta(k Delta)=exp(-Delta sum_(j=0)^(k-1) theta_j),  k=1,...,M.

The Jacobian of these M values in theta is lower triangular, with diagonal entries -Delta S_theta(k Delta), all nonzero. More explicitly, its derivative along h is

    -Delta S_theta(k Delta) sum_(j<k) h_j.

If every derivative were zero, all successive partial sums of h would vanish, forcing h=0, a contradiction. Thus some fixed calendar-cut pair-survival target changes to first order. The target is identifiable from the ideal pair timed-genealogy law, and its changed value is not a coordinate relabelling or a mutation-scale change. This verifies that the constant sequence-menu curve changes a genuine demographic observable.

## 5. A finite extra pair-locus length separates: explicit bound r<=M

Extend h to the piecewise-constant perturbation h(t)=h_j on I_j and zero after M Delta. Put

    H(t)=integral_0^t h(u)du,
    g(t)=S_theta*(t) H(t).

H is continuous piecewise linear on the M finite intervals, starts at zero, and is constant afterwards. It is not identically zero because h is nonzero. It has at most M-1 sign changes: the first nonzero affine piece starts from zero and has only one sign; each later affine piece adds at most one change, and the constant tail adds none. Identically zero pieces or tangential zeros do not increase this bound. Multiplication by strictly positive survival S preserves these signs. The function g is integrable because H is bounded and the fixed tail hazard is positive.

For a>0, differentiate the pair Laplace transform along the analytic curve at epsilon=0:

    d phi_theta(epsilon)(a)/d epsilon at 0
        = a integral_0^infinity exp(-a t) g(t)dt.

This identity follows by differentiating phi(a)=1-a integral exp(-at)S_theta(t)dt; it requires no constant baseline hazard.

Suppose, for contradiction, that the derivatives vanished for a=rs, r=1,...,M, where s=8mu/3. Then the integrals of g(t) exp(-rs t) vanish for these r. Let K<=M-1 be the number of actual sign changes of g. Choose a point t_i in each sign-changing zero or zero interval, and write z_i=exp(-s t_i). Define

    q(z)=z product_(i=1)^K (z-z_i).

If K=0 this is q(z)=z. On (0,infinity), q(exp(-s t)) changes sign exactly at those chosen positions and otherwise has one fixed sign relative to g; after choosing an overall sign, their product is nonnegative everywhere and strictly positive on a nonempty open interval where g is nonzero. Therefore

    integral q(exp(-s t)) g(t)dt != 0.

But q has degree K+1<=M and zero constant coefficient, so that integral is a linear combination of the hypothesized zero integrals. Contradiction. Some integer r<=M consequently has a nonzero pair Laplace derivative.

The r-site product of any one nontrivial pair JC character has expectation phi(rs). It is a concrete signed statistic of the complete two-copy length-r alignment law. A nonzero derivative implies a different expectation for every sufficiently small nonzero epsilon. This establishes the stated next-measurement separation for the local fibre, with no empirical effect-size lower bound uniform in epsilon.

If a menu experiment has n>=2 and length L, marginalizing to any two copies and r<=L sites recovers this same pair character statistic by coalescent projectivity. Its derivative must be zero along the constant full-menu curve. Hence the separating r exceeds L_pair. This conclusion uses an actual common single-population marginal, not an assumed product map on hidden states.

## 6. Relation to prior results and the remaining master

The rank/implicit-function principle and sign-variation argument are classical. Bhaskar and Song's generalized Descartes rule for demographic Laplace transforms is a direct methodological antecedent: https://arxiv.org/abs/1309.5056 . Rosen, Bhaskar, Roch and Song's geometry of finite expected frequency spectra gives substantial prior geometry for piecewise-constant demographic histories: https://arxiv.org/abs/1712.05035 . Myers, Fefferman and Patterson's older nonidentifiability example remains foundational. Their SFS targets are not silently replaced by full shared-locus sequence laws here. The sign-polynomial proof above is included explicitly rather than invoking a theorem with unmapped assumptions. Historical overlap of this finite-menu specialization is unresolved.

The repository's October 5 clock-JC bridge already gives finite-length sufficiency when source architecture/epoch counts are bounded, using a bound depending on those counts. Its forward matrices and all-length inverse are reused. The October 5 quantitative-reliability catalogue already proves nonuniform finite-budget failure via exact-law TV proximity. Here the menu is fixed FIRST, then an actual positive history chart with sufficiently many genuine epochs gives EXACT equality of every chosen full sequence law. This is a different negative statement, not a claim that finite-data difficulty was previously unknown.

The earlier explicit two-copy construction is sharper: it gives a Vandermonde regular point at the constant source, changes the initial hazard, and guarantees the very next site length separates. The present general menu result has a loose D+1 epoch count and an existential maximal-rank source. It does not claim a computable least ambiguity witness, a minimal measurement length or a practical sampling design.

Nothing here proves fixed-length ambiguity when all finite copy panels are available. The menu's finite output dimension is essential. Nothing forces a pulse/no-pulse predicate to vary along the constructed curve: every history here has no stochastic routing. The accepted all-panel timed-genealogy classification is therefore untouched, as are G3/G4 effective recognition obligations, linked-locus models and empirical stability questions.

## 7. Evidence status

Written proof only for this general-menu theorem. No nonlinear source family was numerically constructed, no maximal-rank point was computed, and no full menu forward engine was executed. Existing exact rational two-copy controls do not validate the present larger theorem. Its actual-source forward analyticity, positive chart, constant-rank argument, changed pair-survival target, and sign-polynomial extra measurement are separate review gates.
