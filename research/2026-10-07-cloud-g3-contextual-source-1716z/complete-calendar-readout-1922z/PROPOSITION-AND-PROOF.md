# Actual correlated calendar tags, complete tail and the same genealogy

Contributor: Codex, delegated G3/source-bridge lane, 7 October 2026. **HAND CANDIDATE; accompanying Lean draft UNCHECKED.** No compiler, source simulation or numerical kernel evaluation ran by this lane. Original source providers are attributed to dot and the original source authors. The finite probability-measure conversion is the existing pinned Mathlib theorem, not a new normalization result.

The goal is a concrete joint law of the source's final genealogy and its old/new bin tags. A terminal source-state marginal alone discards earlier graft ages. Conversely, a tag matrix alone does not determine a binary tree when graft tags repeat. The construction below retains endpoint Code jointly with the tag matrix, and proves that the decoder acts on each SAME actual live genealogy. It begins with the actual calendar measure, rather than a freely supplied law asserted to have the desired properties.

## 1. Exact source contract and two different conclusions

Use the original finite rooted binary source `N`, finite copy/sample carrier, original admitted source Code `s`, positive physical pair rates `r`, a finite list `ops` of admitted `ProgramStep N`, an absolute start age `o`, and a real entering matrix `M₀`. Let `leafAge` record the original sample dates and assume

    ForestDecorates leafAge M₀ (state s).                       (D₀)

This is a physical entering-decoration invariant, not a desired output law or decoder premise. The initialized original source discharges it from `initial_forest_decorates` and `snapshot_preserves_decorates`: the initial old matrix is `M₀(x,y)=leafAge(x)`, and `initialCode` is the admitted snapshot of the actual singleton forest. Arbitrary real placeholders between distinct entering trees are bookkeeping only. They are not admitted as physical coalescence ages.

Let `Tag` be finite with its discrete measurable space, and let `bin : ℝ → Tag` be measurable. This covers the original finite cut-bin readout. First we derive source-faithful complete-calendar binning and actual live-tree decoding for ANY `ops` and `o` under the unchanged actual `completeCalendarTraceLaw`. No tail-bin, ancestral support or chronology premise is required for that consistency statement.

The stronger finite endpoint/tag-kernel formula uses two additional, explicit premises:

    ∀ d ∈ support(sourceProgram N r ops s), AncestralRoot N d;   (R)
    o_tail := o + programDuration(ops) ≥ T,
    bin(a)=b_tail whenever a>T.                                (L)

Here `T` is the last fixed observation cut. The original initialized compiled calendar proves (R) from its actual routing support theorem with the supplied original registry, register, hybrid parameters/modes and rates. It does not automatically prove (L) for an arbitrary observation menu. If its demographic programme ends before the last observation cut, a timed-law-preserving ancestral extension remains a separate obligation. An endpoint harmonicity theorem alone is insufficient to justify that extension for old ages or bin tags.

## 2. The complete tag fold is exactly the same real fold binned

Define `segmentTags` on the original `SegmentRecord`: an interval folds its own literal flagged clock record using the already verified `foldTags`; a boundary retains the old tag matrix. Define `calendarTags` with exactly the original `calendarMatrix` recursion: take the stored head destination, advance the offset by `segmentOffset`, carry that head's tags, and process the unchanged tail records. Finally

    completeTags(z)
      = foldTags(bin, card Copy, z.1, o_tail,
          calendarTags(z.past), z.tail.2),

with initial tags `B₀=bin∘M₀`. These definitions are given verbatim in the separate author draft. They add no source, transition, successful flag or new record law.

For EVERY raw segment/calendar/complete record, including unsuccessful prefixes and padding,

    bin ∘ segmentMatrix = segmentTags,
    bin ∘ calendarMatrix = calendarTags,
    bin ∘ completeMatrix = completeTags.                       (Q)

The interval equality is the verified parent's `map_actual_age_fold`. A boundary is an identity on matrices/tags. Induction over the literal program list proves the calendar equality while carrying the same stored Code, offset and old matrix. Applying the same verified fold quotient once to the conditional tail proves the complete equality. This argument does not classify arbitrary raw records as legal source histories; it only proves equality of their two total fold interpretations.

## 3. Under the actual complete law, the decoder reads the actual tree

Write `μ=completeCalendarTraceLaw N r ops s`, `e(z)=completeEnd N ops z`, and `M*(z)=completeMatrix N ops s o M₀ z`. The existing `actual_complete_matrix_decorates` derives from (D₀)

    ForestDecorates leafAge M*(z) (state e(z))                  (D*)

for μ-almost every SAME complete record. Its source proof restricts the actual calendar past to each exact endpoint fibre and carries that past's own real matrix into the actual tail. Past tags are not replaced by independently drawn marginals.

Fix such a record and a live representative `l`. Validity of `e(z)` supplies the well-labelled actual tree `t=(state e(z)).genealogy l`. From (D*) take its real decoration `d_t`, whose pair ages agree with `M*` on that tree's leaf pairs. The repaired, actually verified finite-tag decoder gives

    decodeTags(completeTags(z), t) = mapBinDecoration(bin,t,d_t).

Indeed (Q) changes the matrix input to `bin∘M*`, and the proved `decodeTags_bin_of_pair_agreement` applies to this actual tree and its leaf-pair agreement. The old real decoder also proves uniqueness: `d_t=decode(M*,t)`. No arbitrary choice of a tree, fitted chronology, tag-decoder equality or source law is assumed.

The decoded tagged tree erases to EXACTLY `t` by `underlying_toTaggedTree`. Equal bin tags do not contract binary grafts, reorder ancestry, change leaf IDs, or identify different trees with the same pair partition. All earlier subtrees are those retained by the actual source. The generic statement establishes decoration consistency; strict chronological support for the original physical calendar remains the separate proved original timed-support provider.

The internal state `(Code,B)` carries raw tags even between unjoined ancestral blocks. Its physical pair readout must use the SAME Code: `observedPairTag(e,B;x,y)=some(B(x,y))` if the endpoint ancestors agree, and `none` otherwise. Equivalently decode only each live genealogy on its own leaves. No absent pair is converted into a physical age by binning an arbitrary placeholder. On diagonals the invariant gives the original `bin(leafAge x)`; these are sampled leaf dates, not graft tags. These finite joined/absent tests are measurable. The empty forest needs no chosen Copy or artificial tree.

## 4. Actual calendar endpoint/past-tag law and its PMF admission

Let `P=actualCalendarTraceLaw N r ops s`, `E(p)=calendarEnd N ops s p`, and `C_B(p)=calendarTags N bin ops s o B₀ p`. Define the actual joint pushforward MEASURE

    Γ_measure = P.map(p ↦ (E(p),C_B(p)))

on `F = Code N sample × (Copy → Copy → Tag)`. It retains dependence between the endpoint, its original register/state/tree fields, and all carried past tags.

This map is measurable. `calendar_end_measurable` proves the first coordinate. For the second, (Q) identifies it with pointwise binning of the actual real `calendarMatrix`; `calendar_matrix_measurable` and measurable `bin` prove each finite copy-pair coordinate, and finite products prove the matrix and joint map measurable. This also derives measurability of every unnormalized endpoint/tag fibre used below. The raw complete readout is similarly measurable from `complete_end_measurable`, `complete_matrix_measurable` and (Q). The accompanying source records these explicit derivations.

The original `actual_calendar_trace_probability` makes `P` a probability measure for every `ops,s`. The proved joint map then gives `IsProbabilityMeasure Γ_measure` by `Measure.isProbabilityMeasure_map`. `F` is finite and discrete: source Code has its existing admitted finite carrier, and the finite copy-pair product of finite tags is finite. In particular `F` is countable and its singletons are measurable. Only NOW define

    Γ = Γ_measure.toPMF.

Pinned Mathlib `Measure.toPMF` sets `Γ(d,B)=Γ_measure{(d,B)}` and derives normalization by the singleton partition: `Σ_(d,B) Γ(d,B)=Γ_measure(univ)=1`. Its theorem `toPMF_toMeasure` gives EXACTLY `Γ.toMeasure=Γ_measure`. The original theorem and its countability, measurable-singleton and probability hypotheses were read and hash-verified at Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`; source SHA256 is `4ef376c0ae18ac15664d1d0a77c075f838bc0d65556ac3bc7e462d651fdae197`. Merely writing `Measure.map` does not create a PMF. No numerical probabilities, effective evaluator, rational enclosure or enumeration runtime is claimed here.

The calendar marginal is inherited exactly:

    Σ_B Γ(d,B) = P{p : E(p)=d} = sourceProgram N r ops s d.       (G)

The first equality follows from the finite tag partition of that fibre and the actual joint-map definition; the second is the proved original `calendar_end_fibre_mass`. Thus Γ has no positive mass over an endpoint that violates the support premise (R). Initial old physical decoration need not be inferred from Γ: it is already attached before the actual source calendar by (D₀) and propagated in (D*).

## 5. Exact finite joint tail law, retaining the original correlation

Let `κ_d=completionKernel N r d`. Define a PMF kernel on the finite joint carrier by the actual completed source endpoint and the actual same-bin update:

    J(d,B) = κ_d.map(e ↦ (e,tagUpdate N d e b_tail B)).

Every row is a probability because κ is an existing PMF and this is its ordinary map. The principal hand proposition is

    μ.map(z ↦ (e(z),completeTags(z))) = (Γ.bind J).toMeasure.    (A)

This is an equality of the actual complete-calendar source readout and a specific finite joint kernel. Γ is derived from the actual correlated calendar law in §4; neither Γ's values nor (A) are inputs.

**Proof.** Expand the unchanged original definition

    μ = Σ_d ((P.restrict{p:E(p)=d}) × ν_d).map(insert d),
    ν_d = completeAncestralTraceLaw N r d.

These are unnormalized calendar fibres; their actual masses remain those in (G), including zero fibres. Under `insert d`, the tail starts from precisely `d`, its old tag matrix is precisely `C_B(p)`, and its absolute offset is the fixed `o_tail`. The independently accepted tail-bin corollary and (L) give, under the actual ν_d, simultaneously for every old B,

    foldTags(bin, SAME tail record, B)
      = tagUpdate N d (SAME raw tail endpoint) b_tail B.

It therefore applies to the correlated `B=C_B(p)` for every retained calendar past; no extra independence of past tags is needed. The output endpoint is still that tail record's full Code. For every d with a nonzero calendar fibre, (G)/(R) gives `AncestralRoot N d`, and the already proved **raw** `complete_ancestral_state_source_law` says the actual ν_d endpoint pushforward is `κ_d.toMeasure`, including empty/singleton carriers. This theorem is in the current selected source closure; no random time is inserted into a fixed-time endpoint law. Zero-mass endpoint fibres vanish and require no root-support assertion.

Consequently each complete-record fibre's measurable joint pushforward is

    ((P.restrict{E=d}) × κ_d.toMeasure).map
      ((p,e) ↦ (e,tagUpdate N d e b_tail C_B(p))).

Partition the finite tag state B in the past variable. On its `(d,B)` fibre the output map depends on p only through that B, so the past fibre mass is exactly `Γ(d,B)`. Finite measure addition/product/map identities therefore give, for every output atom `(e,B')`,

    μ{z : e(z)=e, completeTags(z)=B'}
      = Σ_(d,B) Γ(d,B) · κ_d(e) ·
          1_{B'=tagUpdate N d e b_tail B}.

This is the actual finite `Γ.bind J` mass formula. All maps are measurable (§4), all measures are finite probabilities before taking products, and finite sums justify the partition identities. Equality on the finite discrete carrier's singleton atoms proves (A); PMF normalization follows from Γ and J, without conditioning on a success flag or dividing by an endpoint-fibre mass. ∎

Projecting (A) onto endpoint Code gives the existing completed source PMF: (G) reduces the endpoint mass to `(sourceProgram N r ops s).bind κ`. This checks compatibility with the original `completed_calendar_endpoint_law`. The same law's tag marginal retains Γ's correlation; substituting an independently sampled tag marginal or a representative matrix depending only on endpoint d is not justified. Different actual merger ages can have the same stored genealogy Code and different past bin tags.

Combining (A) with §3 yields actual decoded live-tree/observed-pair laws by measurable deterministic readout on the finite carrier `(e,B')`. Its finite image supplies a finite observation carrier without asserting that every arbitrary tagged binary tree is finite in number. The tree output uses each actual live genealogy and the proved decoder, not a tree reconstructed from the pair-tag partition. Actual decorated child-swap transport uses the verified decoder's stated age-decorated relation; arbitrary symmetric matrices still have no general nested-swap quotient claim.

## 6. What this advances and what it leaves open

The actual law (A), physical tree decoder attachment and explicit Γ probability admission address the old correlated-calendar readout gap at this scoped hand level. The optional Lean draft contains the literal quotient, source-connected actual decoder and Γ measurability/probability lemmas; it does **not** implement (A), PMF conversion, tree-image readout or the tail-bin hand proof. No new compiler is requested while the separate literal-prefix successor is active.

The original physical `actual_original_faithful_output` is a separately pinned provider identifying its chronological timed observation with the SAME endpoint/matrix observation; it supplies a later original-calendar readout interface. Generic (D₀) alone does not establish that physical chronological theorem. Any import outside the current selected closure needs its own declared frozen dependency context.

Finite calendar Γ probabilities are proved to exist and normalize; they have not been computed or certified by an effective backend. General bins spanning several program intervals, timed extension when (L) fails, actual finite-tag whole-bank/menu readout and selected-label pruning, fixed-original-ID controls, across-graph positive reconstruction and the full G6 statistical/robustness endpoint retain their own obligations. Original unbounded-source G3 exact recognition and terminal NO completeness remain open.
