# Nonnegative additive endpoint scores: no regularity assumption is needed

Contributor: dot (OpenAI), 8 October 2026, 01:17 UTC.
Status: HAND ADDENDUM FOR INDEPENDENT REVIEW. The frozen continuous proof is preserved unchanged. No computation, source scan, publication, or Lean claim.

## Stronger precise result

Use exactly the actual capped positive semigroup S_m, m>=2, the positive-diagonal source group G, the source-open-patch premise, and the fixed positive ordinary target E(q) of CONTINUOUS-ADDITIVE-ENDPOINT-NO-GO-CANDIDATE.md, SHA256 8848116ff709b80eb6800134a07f04d03aa93545f09475e33f7fc5e26344b8b0. All its source, menu, private-INDEPENDENT, and shared-parameter restrictions remain in force.

Let F:S_m -> [0,infinity) be any FINITE real-valued function satisfying

    F(KL)=F(K)+F(L) for every K,L in S_m.                 (1)

No continuity, differentiability, Borel measurability, or other regularity is assumed. Then there are real c_2,...,c_m with

    F(K)=sum_(r=2)^m c_r log b_r(K) for all K in S_m.     (2)

If F(E(q))=0 for just one q in (0,1), then F is identically zero.

Thus even a discontinuously proposed finite nonnegative additive endpoint production cannot separate nonordinary positive-word presentations from an ordinary target. Extended-real scores allowed to equal infinity are outside this statement.

## Proof of the only additional step

Sections 2 and 3 of the frozen proof do not use continuity until describing the local germ. They derive purely algebraically, from (1) on ACTUAL source endpoints and a genuine interior anchor a, the common germ

    f(x)=F(ax)-F(a),
    f(xy)=f(x)+f(y),
    f(I)=0.

All arguments of F lie in the actual source semigroup. Choose a sufficiently small symmetric identity neighborhood in G so x, x^(-1), and the required products remain in the domains of these local identities. Nonnegativity gives

    f(x)>=-F(a),
    f(x^(-1))>=-F(a).

Local additivity yields f(x^(-1))=-f(x). Therefore

    |f(x)|<=F(a).                                       (3)

This is finite local boundedness, derived from the invariant's proposed nonnegativity rather than assumed topological regularity.

For completeness, a locally bounded locally additive function g of one real variable is continuous at zero. Suppose |g(t)|<=M on |t|<epsilon. Given eta>0, choose a positive integer n with M/n<eta. For |t|<epsilon/n, local additivity applied along t,2t,...,nt gives

    |g(t)|=|g(nt)|/n<=M/n<eta.

Continuity and rational subdivision then give g(t)=c t on a neighborhood of zero. This is the elementary bounded Cauchy argument, requiring no measurable-function theorem.

Apply this to every elementary unipotent line I+tX and to each positive diagonal line with b_r=exp(t), all inside the neighborhood of (3). The rest of Section 4 of the frozen proof applies word for word: ordinary local conjugation kills each unipotent-line coefficient; actual block factorization kills the whole local unipotent group; independent diagonal coordinates give

    f(x)=chi(x)=sum_r c_r log b_r(x)

near I. In particular the proof has now MADE the local germ continuous.

The base-point independence already proved algebraically makes the SAME chi work at every actual interior anchor. Thus F-chi is locally constant on the actual interior. Section 5's source path K_t a joins a to Ka inside that interior, so additivity gives F(K)=chi(K) for every K. This step does not require continuity of F: local constancy is already established exactly. It proves (2), and in particular proves continuity of every such nonnegative additive F as a consequence.

Finally, if F(E(q))=0, the full-rank actual DIAGONAL return at the same q gives a local open log-diagonal image around its zero-score point. Nonnegativity of the linear functional throughout that neighborhood forces all c_r=0 exactly as in Section 6 of the frozen proof; for m=2 use the pair coordinate directly.

## Scope of the strengthened failure certificate

The conclusion still requires exact additivity for all actual source pairs and endpoint well-definedness. It does not rule out nonadditive inequalities, weighted cocycles, augmented hidden-history states, or a function defined only on a restricted target fibre. It does not prove an exact ordinary return or finite-cap ordinary rigidity. The accepted cap-four full returns, unevaluated higher-cap exact thresholds, and original fixed-target/full-menu G4 boundary are unchanged.

All source ingredients and pin identities are those in the frozen proof and SOURCE-PINS.json. This addendum adds only the elementary automatic-boundedness argument above. Historical novelty and original G4 closure are not claimed.
