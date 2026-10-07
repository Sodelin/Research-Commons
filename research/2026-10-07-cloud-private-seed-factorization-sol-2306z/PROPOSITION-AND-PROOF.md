# Natural private seed and erased initialization factorization

Contributor/publisher: Codex, delegated G6 source author, 7 October 2026. **Hand-derived from exact source definitions; proposed Lean consumer UNCHECKED; independent review pending.** The private-register inputs themselves are source-semantic accepted and compiler UNCHECKED. No compiler or provider/workflow/current165-input change occurred here.

Fix the original graph N, its strict original hybrid probability assignment p, original sample map `Copy → X`, and a set P of original vertices. No hidden parameters, rates, sample locations, boundary operations or probability assignment are refitted. The actual register seed has one Boolean per ORIGINAL hybrid. It does not have one common bit per copy or current owner.

Write A for `{h : Hybrid N // h.val ∈ P}` and B for `{h : Hybrid N // h.val ∉ P}`. Their measures μA and μB are the products of `bitMeasure(originalGamma p h)` at those exact sites. The existing bit-probability proof supplies both product probabilities. Empty A or B is allowed; the empty function space still has its product probability one. No default `Copy`, graph vertex or hybrid is selected.

The actual original register measure μ is `Measure.pi` of these same Bernoulli factors over all `Hybrid N`. The concrete subtype-product measurable equivalence e maps an original seed c to `(c|A,c|B)`. Pinned Mathlib `measurePreserving_piEquivPiSubtypeProd` gives

```
μ.map e = μA.prod μB.
```

This equality is derived from the actual product measure. It is not an assumed law of an entering Code or a supplied PMF factorization. The original `NativeCoinSeed = (X × Hybrid N) → Bool` belongs to a distinct native independent-owner route law; it is not substituted for the once-drawn COMMON register.

For an outside assignment b, define its vertex register to be false on P, b at outside original hybrids, and false at all nonhybrids. Let Iout(b) be the existing admitted `initialCode` built from that register. For a full original seed c, let I(c) be the same original initialization built from `originalRegister N c`.

The original `initial` constructor sets all copies live, identity ancestors, leaf genealogies, original sampled-tip locations and empty history. The register is its only seed-dependent data. Its existing source-validity proof is preserved. The admitted snapshot encoding retains that register and encodes the identical live genealogies/populations. Consequently, the root's source-valid erasure E satisfies pointwise

```
E(I(c)) = Iout(c|B).
```

The draft proves the stronger arbitrary-register initializer identity first, through subtype and Snapshot extensionality. The hybrid/nonhybrid and private/outside cases then identify the actual outside register. All erased private slots become false; this is a deterministic latent-register projection, not a redraw of their source coins.

Apply the measurable map `(a,b) ↦ (a,Iout(b))` to the subtype-product law. Its composition with e is exactly `c ↦ (c|A,E(I(c)))` by the pointwise initializer identity. The actual product/map theorem therefore yields

```
μ.map (c ↦ (c|A,E(I(c))))
  = μA.prod (μB.map Iout).
```

This is the concrete joint seed/Code factorization. Private bits are internal latent variables in this statement; they are not declared observed labels or biological itineraries. Original outside bits, admitted initialization and full Copy-labelled Code remain correlated exactly through the original initializer.

The actual `originalRegisterPMF` is μ.toPMF mapped through `originalRegister`. Define the natural initial Code law by mapping that existing PMF through `initialCode`. The outside initial Code law is μB.toPMF mapped through Iout. Both toMeasure identities use the existing proved probabilities and the measurable finite source maps. Marginalizing the preceding joint product with `Prod.snd` gives

```
naturalInitialCodeLaw.map E = outsideInitialCodeLaw.
```

The omitted private factor has mass one by its actual probability proof. No successful-path event, null-fibre division, conditioning on private bits, or arbitrary initial-law independence is inserted.

Finally, for an original operation word ops satisfying the root's explicit `NoPrivateWordRead N P ops`, the already source-derived program erasure says for every admitted s,

```
(sourceProgram ops s).map E = sourceProgram ops (E(s)).
```

Map/bind algebra and the proved natural-initial marginal then give the concrete source-connected consumer

```
(naturalInitialCodeLaw.bind sourceProgram(ops)).map E
  = outsideInitialCodeLaw.bind sourceProgram(ops).
```

The operation restriction is syntactic, not a desired output-law equation. This is an actual endpoint PMF marginal for the unchanged graph/rate bank and source operations. A conditional future whose erased law depends only on the outside initial Code can similarly be appended to the proved joint product: each fixed outside fibre uses that actual source program. The broader joint causal-bin/history assembly is not implemented by this endpoint marginal and is not claimed here.

[PrivateSeedFactorization.lean](PrivateSeedFactorization.lean) contains nine concrete theorem bodies. Their source contracts, exact inputs and new declarations are recorded in [SOURCE-PINS.json](SOURCE-PINS.json). The real subtype-product and product-map API is used; no independence or desired row law is a premise. All proof terms remain compiler UNCHECKED.

The chronological prefix/suffix constructor must still prove `NoPrivateWordRead` from actual original dates and retained boundary phases. Literal marked-record/old-bin correlation, causal run clock assembly, private active-population exit, the common cross-graph decorated carrier, numerical backend, control/menu/pruning and the full G6 endpoint remain separate gates. No theorem about an arbitrary correlated entering past, arbitrary observable private seed, posterior reweighting, or unrestricted G3 recognition/terminal NO follows from this seed consumer.
