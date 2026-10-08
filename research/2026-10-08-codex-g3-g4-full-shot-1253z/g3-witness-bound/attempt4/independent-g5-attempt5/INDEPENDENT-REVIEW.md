# Independent challenge: G5 weak critical cells and coupled algebraic normals

Reviewer: Codex correspondence lane, 8 October 2026. Contributor reviewed: Codex G5. **SCOPED HAND/SOURCE ACCEPT** of the weak-cell uniform-floor counterexample and the CONDITIONAL one-presentation cone/algebraic-normal interface, with mandatory simultaneous-insertion clarification. This is review of another contributor's proofs, not approval of the reviewer's own attempt4. Root independently reviews and owns publication. Original G3/G4 remain OPEN.

Reviewed frozen bodies: ACTUAL-WEAK-CRITICAL-CELLS.md `8f66d5f81a00c58cb1c6352fd84857015bf949cc4cb0f98b8a65a4bb20b2feb9`; COUPLED-ALGEBRAIC-APPEND-NORMAL.md `596655ef18eef4b10e17d561a3bd0a0ad2253b78485f01ce490c55cc5c9c325c`; COMPLETE-INTEGER-WITNESS-ATTEMPT.md `b4e5e80fb810048ffa819fc330775813e2df5b0e906b647c6b85cd05f1b97d7a`; mandatory MANDATORY-JOINT-INSERTION-CLARIFICATION.md `81167fba8fcd680dff17ad46c692d7cce5b6a36a4fc5b2f5e11482c8f549ea2c`; additive ADDITIVE-INTERIOR-PRESENTATION-AND-GLOBAL-GATE.md `8eeeb86c4a03d23f349cdfb84cb1806637ec08236bc7931676f039bb2dd7c0d5`. The accompanying authentication record binds exact selected objects and provider hashes. No mathematical code, compiler, root isolation, symbolic engine or QE was run.

## 1. Sparse interpolation and positivity

For Lambda=(1,3,6,10,15,21), the homogeneous interpolation system removes the constant term by sum c=0. A nonzero six-term positive-power polynomial has at most five positive roots counted with multiplicity. The imposed double roots r=1/2, r²=1/4 and 1 would require six. Thus the rational six-by-six linear system is invertible.

For the normalized solution F0(0)=1 and the same three double roots use all six possible positive zeros of a seven-term sparse polynomial. They are exactly double, with no other positive zeros. Its sign consequently remains positive away from those roots, and F0'' is strictly positive at each root. In particular C=F0(r³)>0 is a rational constant. No computed coefficients or determinant values are needed for this argument.

The varying system has a rational-analytic invertible coefficient matrix near p=0; its quotient Hq/p extends rational-analytically there. Hence c_p is rational when p is sufficiently small rational, bounded and convergent to c0. Its Hp/Hq equations use the SAME actual cell (p,r).

I independently checked the log expansion with c held fixed during differentiation. With Fp(r²)=2Cp and Fp(r³)=C+O(p), its Hp equation gives

    Fp(r)=Cp²+O(p³).

The Hq equation and exact Fp'(r²)=0 give Fp'(r)=O(p²). Substituting into cH gives Cp³/3+O(p⁴)>0. Differentiating the family c_p instead would change these equations, but the submission explicitly avoids that mistake. Clearing a positive rational denominator makes the integer monomial level different from one.

All-q rare positivity is also valid. Around r, the value is at least Cp²/2 whereas shifting to the nearby strong-convexity minimum decreases it by at most O(p⁴). Around r², the exact stationary value 2Cp is positive. Near 1, both Fp(1) and Fp'(1) vanish exactly and the second derivative stays positive. On the remaining compact set, uniform convergence to F0 preserves a positive minimum. These arguments cover q=0 as well; Fp(0)=1. Thus Fp>0 on [0,1), with exactly the double endpoint zero at 1.

## 2. Endpoint challenge and the meaning of a fixed-normal floor

The supplied fixed-normal neutral theorem covers the necessary endpoints. There is also a short independent check specific to this family. Put q=e^(−t) and fix one c=c_p. Since cLambda=0 and F_c''(1)>0,

    partial_t(cH)
      =p'(1−p')F_c''(1)t + O(p'(1−p')t²),

uniformly for the OTHER candidate cell probability p' in [0,1]. Here c is fixed, and p' is not the family parameter. The remainder has the factor p'(1−p') because at either endpoint the ordinary-neutral score vanishes identically, and the finite log functions are analytic uniformly near t=0. Therefore no simultaneous critical cell approaches q=1, including p' approaching 0 or 1.

A neutral approach at q=0 requires p'->0; then cHp tends to sum c=1, so it cannot be critical. An interior q limit with p'->0 would require F_c(q)=0, which strict rare positivity forbids. Hence each FIXED c_p has a positive critical-loss floor. This does not make those floors uniform as c_p varies: the displayed strict critical cell has loss p/2->0 and off-unit value Cp³/3+O(p⁴). Euclidean normalization is a positive scaling and preserves every claimed condition while keeping the normal family compact.

The conclusion refutes a cap-only/normal-compactness loss floor from this local critical incidence. It does not refute a target-derived floor on selected global-boundary presentations or on a minimum witness.

## 3. Original source and interior addendum

The actual source E(1/2) B_COMMON(1/4,1/2,p) E(1/2) has survival X=(1/8)(1/2)^B, B~Bernoulli(p). Thus every required cap-seven moment is rational for rational p, and all are produced by one strictly positive physical tuple. The lower-survival parent has probability p. Connectors, both literal arms and the original private insertion admission are retained. There is no zero physical arm or externally mixed source.

The additive threefold repetition uses three DISTINCT once-drawn COMMON coins, independent across sites. It gives four distinct strict atoms and rational moments. A nonnegative sparse polynomial in 1,x,x³,x⁶,x¹⁰,x¹⁵,x²¹ vanishing on all four atoms would have at least eight positive roots counted with multiplicity, exceeding six. Thus the ordinary moment profile is interior. The same c_p annihilates all present factor derivatives and ordinary-scale columns. This is a legitimate stronger local-incidence example; it does not establish GLOBAL arbitrary-length source boundary, because a remote regular presentation may exist. The addendum correctly makes that limitation mandatory.

All these sources have explicit one-cell or three-cell witnesses. No unbounded minimum witness or NO input has been supplied.

## 4. Coupled cone-openness and algebraic selection

The conditional cone proof is sound in its stated affine response chart. If the projection of the actual rare cone onto R^d/T fills that quotient, finitely many directions span it as a positive cone and have a strictly positive combination in T. A source-chart displacement cancels that combination. The actual full finite inserted compiler has an onto derivative at the identity boundary, with a kernel vector whose new coin coordinates are positive. Short-arm/connector perturbations of order delta² allow the implicit-function correction O(delta²), leaving every new coin positive to first order. Rank persists at the strict new source, whose local image contains a neighborhood of the target.

The mandatory clarification is necessary and now supplies the exact admission premise: ONE finite simultaneously legal G(x,p,e) must exist for all selected cells, chronological placements, protected IDs, bank constraints and BOTH rows in the positive neighborhood. Separate one-cell admission under arbitrary additional global constraints would not imply it. The original eligible fresh untied grammar supplies it in its own unrestricted finite-size scope; stronger constraint languages must prove it. No such grammar premise is inferred for protected or tied sites.

If the target is not interior in these affine coordinates, T+K is a proper convex cone. A convex cone dense in the whole finite-dimensional space would already contain a neighborhood of zero (choose finitely many points surrounding it) and hence the whole space. Separation therefore supplies cT=0, cD_s(q)>=0. At an algebraic center with actual polynomial q-directions this is an RCF condition, with algebraic nonzero normalized solutions whenever real solutions exist. This is effective algebraic selection on ONE fixed graph/chart; it does not choose the graph, supply a global support normal, or remove nonlinear response identities.

The original complete compiler, parent/ID order, register law, actual prefixes/suffixes and shared parameters are retained. Its INDEPENDENT/BOTH D_s are not silently replaced by a bare additive COMMON H-normal. Higher-order singular charts may still attain open response sets when the first-order test fails. The submission correctly claims no converse to the cone lemma.

## 5. Scope of acceptance

Accepted as hand/source mathematics: the actual rational varying-normal family; all-q positivity and fixed-normal endpoint/floor checks; source-faithful off-unit criticality; the ordinary-interior repetition with its global-boundary limitation; conditional coupled cone-openness and fixed-presentation algebraic separation WITH the simultaneous-admission clarification.

Not accepted or asserted: complete integer witness extraction; input-derived normal degree/height, loss floor or word count; global supporting covectors; global attained-boundary classification; a minimum-witness lower bound; INDEPENDENT bare COMMON-carrier transfer; preservation of BOTH rows by COMMON collapse; a source-complete terminating NO procedure; compiler/machine verification or biological conclusions.

The full attempt's stated fatal premises remain fatal. Number-field multiplicative relations for a SUPPLIED finite algebraic alphabet and supported-node computations do not extract that alphabet or its integer count from arbitrary source input. Classical sparse-root, cone, submersion, RCF and arithmetic tools retain attribution. Historical novelty is not certified by this review.
