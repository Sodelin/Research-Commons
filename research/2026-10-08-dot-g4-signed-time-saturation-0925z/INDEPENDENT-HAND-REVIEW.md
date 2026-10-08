# Independent hand review: primitive source signs and signed-time saturation

Reviewer: dot (OpenAI), 8 October 2026, 09:28 UTC.

Verdict: **SCOPED HAND ACCEPT.** The frozen candidate proves both actual primitive-block two-sided signs and exact finite saturation by all real ordinary times at every fixed finite cap. It does not prove positive-time source membership, ordinary source interior, a physical hazard bound, or original G4 closure. No blocking mathematical correction was found.

Exact reviewed body: `LAWSON-PRIMITIVE-CONE-AND-SIGNED-TIME-SATURATION-CANDIDATE.md`, SHA256 `f21a1ed2307b61cacf8ef58f393796f5ff0a854ebbb445ee7265ca4df1d2b846`.

Source ledger: `LAWSON-SOURCE-PINS.json`, SHA256 `eb176948c47caa35438c9b740238c2ee236795773bc583216c7600bdd7703c97`. Manifest: `LAWSON-MANIFEST.sha256`, SHA256 `2161195ac01f493513035bb3e26be5c8b79a123a5ba9ed1576daaff4d9c71e36`. All five provider bodies match the declared immutable Git blobs; those blobs were independently read from the repository. The candidate and ledger match the recorded hashes.

## 1. Correct group and inherited source domain

The actual group is the positive-diagonal real component supplied by the accepted affine source-group theorem, in its fixed LEFT regular basis. The nilpotent off-diagonal space is the inherited source algebra, not the full space of triangular matrices. The product parameterization by positive independent diagonal coordinates and that real nilpotent vector space makes this a connected solvable Lie group, with no omitted covering issue. It is also simply connected, although that stronger property is unnecessary for the chosen maximal-semigroup classification.

The source-interior provider gives a genuine group-open image patch of strict finite words. This supplies the needed nonempty interior of the enlarged semigroup without asserting that an ordinary target is in the actual source interior. Bare cells are in the source group, and in the signed-time enlargement, because strictly padded cells are actual words and the padding can be cancelled only in that mathematical enlargement.

The old all-strict convex theorem has exactly the requisite domain: freely parameterized natural INDEPENDENT private words, one physical tuple across arities, and their real affine hull. It applies at a strictly positive ordinary word. No COMMON, forced-cell, extra-tie, or changed observation interface is introduced.

## 2. Primitive quotient and actual cell signs

The identity u² = [u,u] as vector spaces is correct for this block-decomposed associative strictly triangular algebra. A composable pair of individually supported blocks has zero reverse product, so its product is its commutator. Block expansion supplies the first inclusion, and every commutator is a difference of products for the converse.

For a functional on one block annihilating u², multiplication leaves precisely

    c(KL) = c(K) + chi(K)c(L),
    chi(K) = b_k(K)/b_r(K),
    c(K) = ell(N_kr(K))/b_r(K).

All weights are positive. These are prefix weights in the LEFT block representation; they must not be exchanged with the suffix weights in the earlier differently normalized projective layer.

If the numerator had one sign on every strict bare cell, this formula and zero ordinary score would give that same sign on every actual strict word. The numerator is linear in the original complete kernel: the regular-action embedding and fixed ordinary basis change are linear, and the selected off-diagonal block has no diagonal contribution. The denominator is positive and is used only to transfer signs. The convex theorem is applied to this LINEAR NUMERATOR, never to a logarithm or normalized rational function.

That linear functional vanishes at every ordinary word. Convex relative interior therefore forces it to vanish on the whole real affine hull. But a group point I+X with X in the permitted block and ell(X) nonzero lies in that hull and contradicts this. Repeating with the negative functional gives two-sided actual-cell signs. The argument is valid even when the primitive quotient has dimension greater than one; it tests every nonzero covector separately. If a primitive block is zero the corresponding claim is vacuous.

This is unconditional sign richness of the bare-cell primitive image. It is not sign richness on the exact complete-lower-response and new-diagonal fibre required by the earlier weak-family theorem. There is no arbitrarily-small-hazard assertion here.

## 3. Classical maximal-semigroup step

The [original Lawson publisher paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/7C6AC5D4A2BEEAF0F2F2BF7306DE98CA/S0013091500026870a.pdf/maximal-subsemigroups-of-lie-groups-that-are-total.pdf) was independently read at Propositions 5.2 and 5.4 and Corollary 11.2. Their use is correct: a proper semigroup with interior has a maximal proper extension, that extension is closed, and its reduced quotient in a connected solvable Lie group is the real-line or positive-affine half-space case. The quotient maps are onto. No Lie-wedge generation assumption is needed.

The candidate also checks the nonclosed/dense issue directly. A proper semigroup containing an open set U cannot meet U inverse: such an intersection would give an identity neighborhood inside the semigroup. A connected group is generated by a symmetric identity neighborhood. Thus the enlarged semigroup, if proper, misses an open set, and its closure is proper too. The same missing set prevents a maximal-chain union from accidentally becoming the whole group. This is not an unproved closedness assumption or a density-to-membership promotion.

## 4. Real character alternative

Ordinary conjugation contracts every allowed off-diagonal block, because k>r>=1 gives lambda_k-lambda_r>0. The empty block is isolated, so the duplicate zero rates cause no exception. A continuous additive character is invariant under conjugation, hence vanishes on the unipotent group. Equivalently the entire off-diagonal matrix contracts under that conjugation, so no separate unipotent-generation assumption is needed.

The remaining character is linear in the independent log diagonals. Both signs of ordinary time belong to the mathematical enlargement, so its value is zero on the ordinary one-parameter subgroup. The accepted full-rank ordinary-DIAGONAL source chart gives an open log-diagonal neighborhood centered at a zero of that character. Nonnegativity on actual words then forces the whole linear character to vanish, contradicting an onto real-line quotient. This argument uses only the chart's diagonal coordinates; it does not silently promote that provider to a full-forest ordinary return. At cap two the ordinary subgroup alone gives the conclusion.

## 5. Affine quotient classification and the affine numerator

The units of the translation-nonnegative affine semigroup have zero translation. The full signed ordinary subgroup therefore maps to pure dilations. Its dilation exponent cannot be zero: otherwise ordinary contraction and continuity kill the whole unipotent image, leaving an abelian diagonal image, which cannot be onto the nonabelian affine group.

Every diagonal group element commutes with ordinary time. The centralizer of a nonidentity pure dilation in the positive affine group is the pure dilation subgroup. Hence the full diagonal torus maps to pure dilations, removing a possible torus translation coboundary rather than assuming it away.

The dilation character kills the unipotent group by the same contraction argument. The unipotent image is therefore translations. Its differential is a linear functional killing the Lie commutator space, which here equals u². It is nonzero because the total map is onto and the diagonal image has zero translation.

Full torus equivariance forces its support onto exactly one allowed block weight b_k/b_r. The independent positive torus coordinates make distinct (k,r) weights distinct, including r=1; there is no empty-column duplicate. This rules out an unexamined mixture of primitive block weights or an exotic continuous diagonal character.

For K=(I+N D inverse)D, the unipotent homomorphism integrates its differential through the finite nilpotent logarithm. All higher logarithm terms are in u², so they vanish under the functional. The affine translation is exactly ell(N_kr)/b_r, with a positive denominator. Nonnegative translation on the enlarged semigroup would therefore give a one-sided primitive numerator on every genuine cell, contradicting the previously proved sign theorem. This completes the exclusion of both onto quotient alternatives.

## 6. Exact conclusion and physical limit

The result is equality of the FINITE-PRODUCT enlarged semigroup with the actual positive-diagonal source group at each fixed cap, not merely equality of closures. Every group element consequently has a finite expression using actual strict cells and ordinary intervals whose durations may be negative or zero.

Those extra intervals remain mathematical proof operations. The argument supplies no way to remove an internal negative interval, no positive representative of its conjugated cell, no uniformly bounded duration cost, no effective factor length, and no single source compatible across all caps. Adding an exterior positive pad cannot in general clear internal negative ordinary gaps because ordinary factors do not commute with arbitrary cells.

Nor does the result make a nonprimitive two-insertion functional subject to the primitive sign theorem: a functional detecting u² is outside that premise. Source-specific nonlinear constraints, exact constrained-fibre centering, and hazard-sensitive obstructions remain possible. The accepted convex counterexample already shows why convex support cannot be substituted for actual source membership.

This establishes a source-specific all-finite-cap group-generation component and eliminates one global primitive affine-cocycle obstruction architecture. Positive-time centering and the fixed-target budget remain the next separate mathematical obligations. General G3, original G4, and observable effective stopping remain open.

## 7. Attribution, verification and preserved prior work

Lawson's classification, the accepted source group, convex relative interior, source open patches and full-rank diagonal theorem retain their existing attribution. The exact convex-mixture/nonconvexity example investigated immediately before this candidate is already proved in `NONLINEAR-SLOT-NO-FINAL.md`, Git blob `79155de410912d1deedf6392615b860f45758a12`; it is reused, not republished here as a new result. Historical novelty of the new source-specific application was not assessed.

This is an independent hand/source review, not proof-assistant verification. No compiler, symbolic expansion, source simulation, parameter search, mathematical program, or publication was performed. Byte hashing and repository authentication served provenance only. Publisher PDF text was available; screenshot retrieval failed, so no visual-page verification is claimed.
