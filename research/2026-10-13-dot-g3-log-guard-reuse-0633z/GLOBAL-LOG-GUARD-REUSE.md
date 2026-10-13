# Ordinary-neutral global log guards: an already-supplied cone obstruction

13 October 2026, 06:23 UTC. Author: dot, existing exact-attainment lane.
Status: independently reviewed hand derivation and prior-reuse correction;
[scoped review](INDEPENDENT-GLOBAL-LOG-GUARD-REVIEW.md). No new source theorem,
novelty, Lean verification, recognizer or general impossibility is claimed.

Publication projection, 13 October 2026, 06:31 UTC: only status/provenance text
and the review link are changed. Original reviewed SHA256:
`fad77143c57618ce7d806ee4956393c6388f9bb5a0973f71fc44d48cb80cd685`. The mathematical text is unchanged.

## Result and attribution first

The global additive guard proposed in the October 8 alternative-presentation attempt cannot have its desired strict interior-cell zero. This is already a consequence of the accepted October 6 COMMON log-cone theorem. The elementary integral calculation below makes the exact scope and a finite validity test explicit. It does not reopen either the source-interior theorem or G6 approximation, and it does not resolve original G3.

The controlling prior is [EFFECTIVE-FIXED-SIZE-RAY-REALIZATION.md](https://github.com/Sodelin/Research-Commons/blob/e837b8fcaaa0f0ac00e4686214f6951d91a5a282/research/2026-10-06-dot-g3-actual-ray-realization-0915z/EFFECTIVE-FIXED-SIZE-RAY-REALIZATION.md), Git blob `9f95cf4bfdc644767d7035acfa9341cbe4f1d7d2`, source SHA256 `45417d34190ebb34e7ce05cf3f968fd2f5ce5bc6548bfcd8d690baf037323bea`. Section 6 identifies the closed conic hull of actual COMMON log words with the increasing discrete-concavity cone. Its [independent review](https://github.com/Sodelin/Research-Commons/blob/e837b8fcaaa0f0ac00e4686214f6951d91a5a282/research/2026-10-06-dot-g3-actual-ray-realization-0915z/EFFECTIVE-FIXED-SIZE-RAY-REALIZATION-REVIEW.md), Git `dd60381e9e53e1465525664259f09948b466fd71`, explicitly accepts that source-faithful cone statement. The paper and classical convexity mechanisms credited there remain prior work.

The later [October 8 attempt](https://github.com/Sodelin/Research-Commons/blob/e837b8fcaaa0f0ac00e4686214f6951d91a5a282/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/ATTEMPT-2-ALTERNATIVE-PRESENTATIONS.md), Git `73e1c29053152562aed0be735da078758160e33d`, Section 6, left a global ordinary-neutral log-linear guard with a strict cell zero unresolved after exploratory linear programming. The old cone supplier resolves that particular subroute without another optimization or source search. Its other routes and limits remain unchanged.

## 1. Exact class

Let 0 < lambda_1 < ... < lambda_d be distinct exponents, and let c be a real vector satisfying sum_i c_i lambda_i = 0. Original triangular integer exponents are included. The accepted October 6 statement is literally for those original triangular exponents; the arbitrary distinct-positive-real version in this proposition is justified by the standalone integral proof below, not attributed verbatim to that prior. Put

    H_i(p,q) = -log(1-p+p q^lambda_i),   0<p,q<1,
    F_c(p,q) = sum_i c_i H_i(p,q),
    C = sum_i c_i,
    K_c(t) = C max(t,0) - sum_i c_i max(t-lambda_i,0).

The asserted guard must satisfy F_c(p,q)>=0 for EVERY strict normalized Bernoulli cell. Its coefficients may depend on the target, but must be fixed across all cells of the proposed source. Ordinary neutrality makes the positive ordinary baseline contribute zero. Source-specific bounds restricting the cell domain, nonlinear state dependence and conditional guards are not in this class.

**Proposition.** Global nonnegativity of F_c is equivalent to K_c(t)>=0 for every real t. Equivalently, it suffices to test K_c at the finitely many breakpoints 0,lambda_1,...,lambda_d. If these conditions hold and c is nonzero, then F_c(p,q)>0 at EVERY strict cell. Thus a nonzero globally nonnegative ordinary-neutral additive log guard has no strict interior zero.

## 2. Proof, with no source-limit substitution

Let a=log(p/(1-p)), b=-log q>0, and L(x)=log(1+exp x). Then

    F_c(p,q) = C L(a) - sum_i c_i L(a-b lambda_i).

For each fixed t, set a=bt and let b tend to positive infinity. Since 0<=L(x)-max(x,0)<=log 2,

    F_c(p,q)/b -> K_c(t).

Each finite b corresponds to a strict cell. Consequently global F_c>=0 implies K_c>=0. No infinite or endpoint cell is admitted as a witness; this limit tests a necessary inequality only.

Conversely, L''(u)=exp(u)/(1+exp(u))^2 is strictly positive. The exact elementary integral identity

    L(x) = integral_R max(x-u,0) L''(u) du

follows by integrating twice and using L(-infinity)=L'(-infinity)=0. Each integral converges. A finite linear combination and the substitution u=a-bt give

    F_c(p,q) = b^2 integral_R K_c(t) L''(a-bt) dt.

Ordinary neutrality makes K_c vanish for t>=lambda_d; it also vanishes for t<=0. Thus the last integral is over a compact interval. If K_c>=0, it proves F_c>=0. If c is nonzero, K_c cannot be identically zero: its derivative jumps by -c_i at lambda_i. Hence the continuous piecewise-linear K_c is positive on some open interval. Strict positivity of L'' gives F_c>0 for every finite a and b>0.

Finally K_c is linear between successive breakpoints and zero outside their range. Its nonnegativity is therefore equivalent to those finitely many tests. For rational/effectively algebraic exponents and coefficients these tests are exact real-algebraic comparisons. QED.

## 3. Why this is an inherited cone consequence

Every strict Bernoulli log vector H has strictly positive, strictly decreasing consecutive slopes, because its continuous interpolation in lambda is strictly increasing and strictly concave. It is therefore in the interior of the discrete increasing-concavity cone. The accepted October 6 theorem says this cone is the closed conic hull of actual word logs. A nonzero linear functional nonnegative on that cone is strictly positive at every interior point. The ordinary-neutral global guard is just such a functional. This proves the no-zero conclusion immediately from the prior theorem; the displayed integral is a transparent alternative verification and gives its exact finite dual test.

No cone coefficient is interpreted as a physical fractional factor multiplicity. Actual source membership is not equated with membership in its conic hull.

## 4. Consequences for the exact-attainment attack

For an actual finite natural COMMON word h=a Lambda+sum_j H(p_j,q_j), a>0, the guard equals the sum of the cell scores. For nonzero valid c it is zero exactly when the normalized word has no unequal strict Bernoulli factor. Equal-arm physical cells are already ordinary baseline contributions under the inherited normalization. Thus the proposed construction of an attained source-boundary point by a globally nonnegative additive score tight at a strict unequal cell is unavailable.

These guards also cannot reject a valid ordinary sparse moment vector merely because it has no finite original Bernoulli-product realization. For a positive random survival X, h(lambda)=-log E[X^lambda] is concave with h(0)=0; its consecutive slopes are nonnegative and nonincreasing. The old cone theorem therefore makes every valid guard nonnegative on it. For laws with strictly positive observed moments, the statement extends to mass at zero by replacing X with max(X,epsilon) and taking the finite-coordinate limit. The all-zero survival law is excluded because its logarithmic coordinates are undefined. In particular the already accepted algebraic/rational source-closure NO controls inside the ordinary moment body survive every guard in this class.

This does not refute nonlinear semialgebraic inductive certificates, retained-head conditional bounds, source-dependent transported normals, nonadditive observations or guard validity on a properly restricted fibre. It does not prove that all finite attained tuples are source-interior: a nonconvex image can have a boundary with no global linear supporting functional. It says nothing automatic about INDEPENDENT or BOTH kernels.

The original rational/effectively algebraic whole-menu recognizer still requires exact finite attainment or complete exclusion over every original core, one shared source tuple, strict positivity and unbounded private lengths. The October 9 zero-distance stopping gate remains open. The useful change here is a prior-work-based removal of one supposedly unresolved candidate guard search, not a new master theorem or a general algorithmic lower bound.

## 5. Checks and next gate

The exact October 6 proof/review, October 8 attempted guard, October 9 recognizer and October 10 all-real critical-presentation finiteness were directly read. A bounded repository search for softplus/global guards found the earlier hinge/cone supplier; absence of other literal matches is not a semantic completeness claim. No floating check, compiler, source edit, invariant search or external publication was performed.

Independent review should check the sign and b^2 factor in the integral, ordinary-neutral compact support, strictness for c!=0, the attribution to the accepted conic hull, and the distinction between moment-cone validity and original finite-source attainment. A further attack needs a genuinely nonconic boundary mechanism or an input-only exact classification of the remaining coupled critical fibres. Repeating global additive LP searches is not that step.
