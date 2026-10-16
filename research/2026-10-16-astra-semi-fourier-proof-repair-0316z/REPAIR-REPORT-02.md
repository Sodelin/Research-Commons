# Fourier intensity proof repair r2

16 October 2026, 03:16 UTC. Lean source owner. **SOURCE CANDIDATE, UNCOMPILED; focused independent review pending.**

This isolated candidate responds to the supplied actual FourierIntensity compiler diagnostics at original lines 68, 87, 95 and 105. It succeeds the prior static closure-API candidate for future source selection only. The earlier source and all prior/used execution evidence remain preserved. This contribution repairs proof applications, not mathematical statements or attribution.

## Exact selection

Baseline: `b1874403c4c45435104cdf17424b957106637495`, `FourierIntensity.lean`, 5,963 bytes, SHA256 `ca54ff7c457432db4bf5512908a90feb21b2c4a479553814fb7a9cb2e7b93c4e`. Successor: 6316 bytes, SHA256 `ac9b07a5b354fc1c9dbc71f6b418cbc2949650e67da0a8ca6a5c9e275c076c01`. Unified patch: 2233 bytes, SHA256 `e37e45c842af52b2354d230f6709aa9513067aa5e7cf191e62f7bdbf16b20a95`, 3 hunks.

The complete binary cyclic-grid, N-positive, labelled Fourier/intensity statements are unchanged. No imports, options, assumptions, definitions, theorem/lemma headers or namespace are changed. The explicit `K := intensityStabilizer N` closure repair remains verbatim. FiniteOrbit and CyclicGrid repairs are retained at their existing pins in the manifest; their held files were rehashed unchanged.

## Four diagnostic repairs

1. **Parseval, line 68.** The supplied simplification result had changed conjugated real spins into unconjugated spins before reducing their product. Use `simpa only` with the existing `complexSpin_mul_conj` theorem, followed by finite constant-sum/cardinality, natural scalar multiplication and `pow_two`. This preserves the product-with-conjugate shape until it becomes one. The proof still derives total power from the same existing `dft_parseval_complex`; no normalization assumption is added.
2. **Translation integrand, line 87.** State both sides of the summand equality explicitly with `j + t`, eliminating the `shiftSite` structure coercion and let-bound function by definitional reduction. Then rewrite associativity, the character addition law and the unchanged ring identity `he`. This replaces the unsuccessful simplification of an unreduced equivalence application.
3. **Translation reindexing, line 95.** Replace the under-specified `.sum_comp` rewrite, which left a finite-support side condition, by an explicit `Fintype.sum_equiv` equality with equivalence `shiftSite t`, both summands supplied, and reflexive pointwise equality. Apply multiplication by the same character using `congrArg`. This is a finite full-domain reindexing with no additional support hypothesis.
4. **Inversion, line 105.** First rewrite the conjugated DFT with `conjugate_dft` and the unchanged real-spin identity `hc`. Then apply `congrFun (ZMod.dft_comp_neg (fun i => complexSpin (x i))) k` directly. The explicit input avoids higher-order rewrite-pattern inference under `fun i => complexSpin (x (-i))`.

## Inspected pinned APIs and verification

All supporting Mathlib files listed in the manifest were read at commit `0df444a360eaa60ab8c11dca51a86af692955474` and their complete held bytes were matched to its Git tree. `Mathlib/Analysis/Fourier/ZMod.lean:173` declares `dft_comp_neg (Φ) : dft (fun j => Φ (-j)) = fun k => dft Φ (-k)`. `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:742` supplies `Fintype.sum_equiv` via the `to_additive` declaration of `prod_equiv`, with explicit `e`, `f`, `g` and pointwise equality. `Mathlib/Algebra/Group/AddChar.lean:113` is `map_add_eq_mul`; `Mathlib/Algebra/Ring/Defs.lean:188` is `nsmul_eq_mul`. The retained CyclicGrid source supplies `complexSpin_mul_conj` and the definition of `shiftSite` used here.

Exact inverse replacements recover all baseline bytes. Independently replaying the unified patch produces the successor. A source-text check confirms all declaration prefixes and definitions unchanged; every edit is inside three existing proof bodies. No `sorry`, `admit`, `axiom` or `unsafe` token is introduced. Public packet metadata was screened for private routing/host/path identifiers.

## Evidence limits and remaining gap

The actual diagnostic evidence is supplied through the established review route, not a new personal raw-log read: complete stdout 2,645 bytes / SHA256 `5173f22be3172f2420ff5686f43e2e734ddbd13f186510a241465ae4e5b518a9`; command receipt 2,608 bytes / SHA256 `c713d668980a16c6849fbe8470dbeadddb7af4895c03b474d503452575ecb7bf`. The supplied outcome was compiler exit 1 with no runner stop/error; these are actual diagnostics, unlike the earlier static closure finding. Later independent modules may have separate outcomes; this packet makes no claim about them.

This source repair has run no compiler, checker, solver or acquisition. Successful elaboration of these exact proof applications, later dependent modules, printed endpoint types/axioms and final custody remain unestablished here. Focused independent source review is next; any later desktop check needs its own fresh selected finite record through the existing sole operator. No active or used leaf was edited, no consumed record replayed, and no canonical package or biological/materials/G3/G4 result is adopted by publishing this candidate.
