# A zero-score criterion for an effective whole-fibre source bound

Contributor: dot, G3 recognition lane, in coordination with the G4 forcing lane. 9 October 2026, 16:06 UTC.
Status: conditional HAND theorem submitted for review. This supplies a sufficient certificate format, not certificate existence or coverage for general G3. No historical novelty claim.

## 1. Result and original source contract

A certified nonnegative additive score, forced to vanish on the entire supplied observation fibre, can bound every actual private-word length without requiring finitely many zero cell types or a lower bound on inheritance probabilities. The essential extra hypotheses are a known positive COMMON-clock floor and an explicitly effective, uniform positive weak-cell slope.

The input y is the original finite effectively algebraic menu. Its accepted source-faithful compiler has finitely many retained cores. A core retains one original graph/ID structure, all shared parameters, controls/registers, the complete chronological carrier, and finitely many distinct physical private-word slots. Repeated appearances of the same slot are not independent variables. Fixed finite words at protected sites remain part of the core. The target is the entire joint fibre, not selected hidden marginals.

For each core we require either a sound whole-core NO certificate or finitely many certified pieces covering ALL fitting source assignments in that core. A piece may be described using shared static parameters and the finite endpoint tuple. None is an extra observation. The covering statement must be proved from the actual source grammar and GIVEN y; a proposed partition of sampled completions is insufficient.

On each surviving piece, every unbounded slot must first be proved to be a genuine finite strict equal-arm natural private word of the same physical source. This is supplied by the new tree-edge reduction only at its actual calibration/menu contract. No replacement of an arbitrary INDEPENDENT word by an equal-arm one is assumed here.

## 2. Quantitative certificate data for a piece

Freeze the piece's finite tuple ξ, including any shared parameters on which its scores depend. For every distinct unbounded slot j the following data and statements are certified uniformly for ALL permitted ξ and ALL fitting sources in the piece.

(A) **Resource identity and floor.** The actual word has L_j strict equal-arm cells with arm durations t_ji>0 and coins g_ji in (0,1). Put p_ji=g_ji(1-g_ji) in (0,1/4]. Its COMMON survival is

    c_j = exp[-(τ_j + sum_i t_ji)],   τ_j>0,
    c_j >= b_j >0,

where b_j<1 is an explicitly supplied rational number. Algebraic lower floors may be replaced effectively by smaller positive rational ones. The identity is for the actual word, including all ordinary passages, not an inferred counterfactual clock from an unauthorized channel.

(B) **Same-source additive score.** There is an endpoint quantity Φ_j(W_j;ξ), ordinary-neutral and additive under the actual chronological composition of this word, such that

    Φ_j(W_j;ξ)=sum_i F_j(p_ji,t_ji;ξ).

The equality is proved with the same ξ and physical parameters throughout. It can be a mathematically derived endpoint quantity rather than a new measured row, but its vanishing below must follow from the actual supplied fibre.

(C) **Nonnegativity and exact annihilation.** Every legal strict cell in this piece satisfies F_j>=0. The supplied observation equations imply

    sum_j a_j(ξ) Φ_j(W_j;ξ)=0,     a_j(ξ)>0

for every fitting source. Individual identities Φ_j=0 are a special case. No lower bound on a_j is necessary, but strict positivity for EVERY unbounded slot is necessary. A nearly zero numerical score does not satisfy this hypothesis. Negative terms or independently chosen parameters cannot cancel positive cell scores.

(D) **Effective uniform weak-cell estimate.** There are explicit positive rationals ε_j,σ_j and a nonnegative rational M_j such that

    G_j(p,t;ξ)=F_j(p,t;ξ)/(p t)

on p>0,t>0 extends continuously to 0<=p<=1/4, 0<=t<=ε_j, and

    G_j(p,0;ξ)>=σ_j,
    |G_j(p,t;ξ)-G_j(p,0;ξ)|<=M_j t

on that entire domain, uniformly over ξ. A certified bound |∂_t G_j|<=M_j is sufficient. An explicit alternative computable uniform modulus is equally sufficient, after producing a positive rational δ_j with oscillation at most σ_j/2. Merely knowing a positive pointwise limit or that the coefficients are computable does not meet this requirement. In particular p→0 and p→1/4, and every allowed shared static degeneration, must be included.

Certificate production and verification may use separately proved analytic estimates. This theorem does not supply a generic decision procedure for arbitrary log/exponential inequalities.

## 3. Effective length bound: complete proof

Set

    δ_j=min(ε_j, σ_j/[2(M_j+1)]) >0.

These are rational computations. For 0<t<=δ_j and 0<p<=1/4, (D) implies

    G_j(p,t;ξ)>=σ_j-M_j δ_j>=σ_j/2>0,
    F_j(p,t;ξ)>0.                                      (1)

Every Φ_j is nonnegative by (B) and (C). Since all weights in the finite sum in (C) are strictly positive and its value is exactly zero, every Φ_j=0. Each finite cell sum is therefore zero term by term. Equation (1) forces every actual cell to have t_ji>δ_j. This conclusion includes arbitrarily biased interior coins: no positive lower bound on p_ji was used.

By (A),

    L_j δ_j < sum_i t_ji < -log c_j <= -log b_j < 1/b_j.   (2)

For L_j=0 the required count bound is immediate; the first strict inequality in (2) is used only when L_j>0. The elementary inequality log x<=x-1, with x=1/b_j>1, gives the final coarse rational bound. Thus

    B_j = ceil(1/(b_j δ_j))

is a computable safe integer upper bound for L_j. There is no call comparing an unknown transcendental quantity with zero. The estimate is deliberately loose. In particular no exact evaluation of -log c_j is required.

No finiteness or isolation of the strict zero locus was used. It may contain curves of biased cells. Only its exclusion from a uniform neighbourhood of t=0 matters. A known positive derivative coefficient at t=0 can supply this exclusion only with the quantitative uniform modulus in (D).

## 4. Entire original fibre and terminating RCF consequence

For a covered core piece, combine its finitely many B_j with the inherited finite core/protected-site bound. The source compiler gives a finite catalogue of actual architectures with those slot lengths; ordinary consecutive passages are merged only where the original grammar allows it, preserving protected sites and shared parameters. For a finite cover use the maximum/sum of its resulting bounds as appropriate. Finally take a bound covering every surviving original core. Already excluded cores contribute no candidates.

Every source fitting y lies in one covered piece or an excluded core. An excluded core cannot contain it. On its piece all of its unbounded words obey the derived bounds. Therefore at least one bounded catalogue source fits whenever any original source fits. In fact the certificate has bounded every fitting presentation in its permitted normalized core grammar, which is stronger than needed.

Decide each bounded architecture's ORIGINAL joint feasibility formula by RCF. All observations, original IDs, strict inequalities, mechanisms, chronology, shared controls/registers and root completion remain in that formula. A SAT formula yields an actual source and is YES. If every catalogue formula is UNSAT, the covering/count argument rules out every original source and gives NO.

The RCF stage need not include the logarithmic score or solve for its coefficients. The score is used only in the separately certified mathematical bound; the final catalogue tests the inherited polynomial original-source equations. It never assembles independently fitted slot kernels.

Consequently an algorithm that effectively produces verified data (A)–(D) and the finite all-core cover on every input in a class gives a total recognizer on that class. If such data are merely supplied on some inputs, this is a sound conditional recognition module, not a general terminating algorithm. General certificate existence/coverage is unproved.

## 5. Why positive score is not enough: an exact biased-source control

The zero level in (C) cannot be replaced by an arbitrary fixed positive level when deriving a bound on all presentations. This can be seen directly in actual equal-arm words, with no numerical limit argument.

For each integer N>=1 define

    q_N=4^(-1/N),
    p_N=[(3/2)^(1/N)-1]/[2(4^(1/N)-1)].

Then 0<p_N<1/4. Indeed (3/2)^(1/N)<2^(1/N), so

    p_N < 1/[2(2^(1/N)+1)] <1/4.

Choose either interior algebraic coin g_N solving g_N(1-g_N)=p_N. Take N equal-arm cells with survival q_N and that coin, and split an ordinary survival product Z=1/4 into N+1 strictly positive passages. Every parameter can be chosen algebraic. These are actual finite private source words with

    c=Z q_N^N=1/16,
    b2I/c=product_i [1+2p_N(q_N^(-1)-1)]=3/2,
    b2I=3/32.

The ordinary-neutral score F(p,t)=log[1+2p(exp(t)-1)] is nonnegative, has G=F/(p t) extending with G(p,0)=2 uniformly over p in [0,1/4], and satisfies a uniform derivative estimate on a sufficiently small compact t interval. Yet its fixed total score is log(3/2)>0 for these words of EVERY length N, while their COMMON clock is the same positive 1/16.

Thus a positive clock floor and a positive weak slope do not bound presentation lengths at positive endpoint score. This control concerns the same paired pair coordinates; it does not claim equality of higher forest responses. It does not refute an existential one-witness bound: the N=1 word is already a short witness for this pair profile. It is not a full G3 hardness or nonrecognition example. The construction only diagnoses the precise inference needed by this certificate method.

Likewise replacing F by F minus a target-dependent positive constant per cell changes its global nonnegativity and introduces an unknown count. Subtracting a constant at the word endpoint does not preserve additivity.

## 6. Existing interface obstructions and prior attribution

The observed-clock step is source-specific. The accepted counterfactual-COMMON no-descent result says a universal finite-cap INDEPENDENT endpoint decoder cannot recover the COMMON pair survival of the same physical word. Thus arbitrary INDEPENDENT-only inputs cannot silently acquire hypothesis (A). This does not rule out a separately proved target-specific floor or an actually supplied BOTH row.

The general count-budget principle, fixed-shape RCF, original finite-core compiler, and weak/strong cell accounting are inherited. The active G4 score search suggested the normalized weak-slope certificate; this manuscript states its whole-fibre, shared-parameter and effective-modulus transport. It does not assert a new general compactness theorem or historical novelty.

Prior sources checked:

- `research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md` and its review: original finite cores and exact shared append grammar.
- `research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-witness-bound/PRIOR-MAP.md`: input-effective critical counts, full-fibre limitations and prior budgets.
- `research/2026-10-08-dot-g4-counterfactual-common-boundary-2313z/COUNTERFACTUAL-COMMON-PAIR-NO-DESCENT.md`, freshly read at commit `1c69c9987b7d083d6e4aef6b2c12145336e1bc2c`: no universal missing-mode decoder and failure of positive-gap subtraction.
- New reviewed `CALIBRATED-TREE-EDGE-REDUCTION-AND-FORCING.md` and its mandatory decoder/paired-guard providers: an actual all-core source reduction only under the GIVEN natural BOTH calibration menu. The existing one-fair-cell recognition branch is not reproved here.

Scores confined to the constrained paired equal-arm source domain do not contradict the inherited globally nonnegative ordinary-neutral INDEPENDENT endpoint no-go. The domain restriction and genuinely supplied/derived paired information are essential.

## 7. Actual verification and open obligation

This manuscript is a complete conditional hand proof. No new source-kernel simulation, numerical sign test, interval certificate, QE solve, end-to-end recognizer or Lean compilation was executed. Section 5 is an exact all-N hand construction, not a numerical extrapolation. The active higher-score candidates remain separate and unproved until their continuous-domain signs and uniform estimates are certified.

The full G3 gate remains: construct an effective finite cover satisfying the premises, or another complete mechanism, for every original supplied algebraic fibre. The theorem does not presume this and does not require every target to admit a zero-score certificate. It is sufficient, not necessary, for recognition.
