# Independent control protocol: code audit

Reviewed the actual `control_protocol.py` in `/workspace/scratch/c82ede027ea7/research/2026-09-30-independent-control-1810z`. No prototype edits made by this reviewer. The root agent made the validation and runtime-API fixes during review; the current versions were independently rechecked. This reviewer added the authorized narrow `correlated_checks.py` and its `correlated-checks.json` output.

## Verdict

No defect found in the admitted-network quartet recursion or the synchronization policy. The exact quartet checks support the implementation; they do not establish the full gene-law theorem. That theorem still rests on the stated coupling argument, sampling declaration, and ideal persistent per-locus control premise.

## Findings closed by independent replay

1. **Quartet requests now respect the declared sample.** The former counterexample compiled `triangle()` with copies `A:0, B:1, C:1, D:1`, then asked the verifier to sample ABCD. It silently returned natural rather than common CF because A had not been declared sampled. `CompiledRow` now stores the declaration and both quartet verifiers reject that request. Independent replay confirmed the rejection and confirmed that two compatible zero-copy declarations and one declaration with two A copies still give the common one-copy-per-distinct-taxon marginal. Copies greater than one are compatible: the quartet chooses one of the declared copies per taxon, while the compiler's counts conservatively bound the full sample.

2. **Direct `cf` now validates the admitted domain.** Previously survival `Fraction(2)` on H->W yielded `(-1/5,3/5,3/5)`, and float survival 0.9 yielded floats. The current public entry point invokes `structural_checks`; independent replay confirmed both invalid values now raise `ValueError`.

3. **The cap and graph-free runtime boundary are explicit.** Independent replay confirmed caps `-1`, `True`, `1.5`, and `'12'` raise `ValueError`. The new `sample_identifier_environment` needs only row IDs and rational parental probabilities, without a Network. Its product mode passed the exact p=2/7 stub check `[0,0,1,1,1,1,1]`; its correlated mode preserved fixed bits and assigned one shared fair bit to all free IDs with exactly one `randrange(2)` call. This API still assumes an externally validated original ID/parent map and actuation contract.

## Mechanism review

- At a hybrid, the three cases are correct: fixed sends the whole current mask to the indicated original incoming edge; shared mixes all-to-edge-0 with weight p and all-to-edge-1 with weight 1-p; independent enumerates every subset with its product Bernoulli weight. Fixed controls take precedence over `shared`, which is coherent even if the sets overlap.
- The edge contribution uses the Kingman first-merger survival `x**choose(k,2)` and distributes the first pair uniformly among `choose(k,2)` pairs. Absorbing probability after one merger is sufficient for quartet topology. A later independent merger in a disjoint population can only involve the complementary pair and therefore yields the same split. No full-gene-law claim follows from this absorption.
- Descendant counting unions reachable taxon labels before summing declared copies; it does not multiply a taxon's count by the number of paths. A hybrid with at most one declared descendant copy cannot receive two unmerged lineages. Fixed sites need no randomization. The graph-free policy synchronizes every remaining free ID.
- The sample draw uses bit 0 with probability p. For p=2/7, a deterministic randrange stub returning 0 through 6 yielded `[0,0,1,1,1,1,1]`.
- `sample_environment` emits at most r settings and makes at most r RNG calls without expanding completions. Interpret O(r) in that operation-count sense. Arbitrarily large rational denominators entail additional random-bit/arithmetic cost. Exhaustive quartet verification remains separate and capped (default 12 sites, at most 4096 completions).
- The `graph_known=False` verification/compiler branch accepts and structurally inspects a complete Network. The separate `sample_identifier_environment` is the actual graph-free runtime interface using IDs and probabilities alone.

## Focused executable evidence

- Twelve original fixtures: n=4,5,6,7, each with 0,1,2 pendant bigons. Five fixed/free patterns and all four-taxon subsets gave **840** comparisons in which the mixed direct law, all-common target, graph-known completion mixture, and graph-free completion mixture were exactly equal.
- Three asymmetric variants at n=4,5,7 used varying rational edge survivals and inheritance probabilities 2/7, 3/8, 4/9. Three control patterns and all quartets gave **123** additional exact comparisons. This removes the symmetric parent-law masking present at H in the basic fixture.
- Two compatible zero-copy sampling declarations on a five-taxon fixture passed: one omitted E and checked ABCD; the other omitted A and checked BCDE. The selected synchronization sites changed as the declared descendants changed.
- The natural negative example exactly matched `triangle_formula`: `(59/200,141/400,141/400)`. Its min-subtracted vector is `(0,23/400,23/400)`, supporting the two absent quartet resolutions. The synchronized law is `(23/50,27/100,27/100)`, with contrast `(19/100,0,0)`.
- For one neutral pendant bigon, both rows fixing J0 to 0 or 1 and leaving H natural preserved the same negative natural CF. Compiling either row synchronized H and returned the common law.
- Expected failures occurred for duplicate requested taxa, unknown fixed/shared IDs, boolean fixed bits, incomplete or unknown row IDs, boolean row values, incomplete/negative/boolean sample counts, and an insufficient verification cap.

## New one-coin support checks

`correlated_checks.py` is credited to this independent code-audit agent. It imports the existing `gadget`, `single_menu`, and `partial_array` by file path. It tests only two prescribed source-admitted fixtures: r=3 with pendant A and C cherries (n=6), and r=4 with A, C, and B cherries (n=7). Every positive edge has rational survival 1/2, every natural parental probability is 1/2, and every taxon has one sampled copy. The cherry attachments preserve the original gadget's written outer-face admission and the implemented structural checks passed.

- All **24** global switches across the two fixtures were used for an independent edge-cut tree oracle. Across their 15 and 35 quartets this gives **680** switching/quartet oracle cases.
- Both menus on both fixtures gave **420** correlated row/quartet readouts, checked against **840** conditional tree-mixture oracle calculations.
- All **100** menu/quartet support comparisons passed: the union of positive min-subtracted CF coordinates equals the original displayed quartet support. For every present quartet resolution, the maximum menu contrast was at least **1/4**; each fixture/menu's attained minimum was exactly 1/4. This verifies the stated finite g=1/2, tau=ln(2) threshold on these fixtures only.
- The runtime sampler emitted one or two distinct configurations per row and made zero or one fair-coin RNG call. Every additionally synchronized site's marginal edge-0 weight was exactly 1/2. The identifier-only correlated sampler agreed on those controls and preserved fixed settings.
- **50** readouts differed from the product common-inheritance CF, all in the r=4 single menu. For example, q=(A0,A1,B0,C0) and row HA=None, HC=None, H2=0, H3=None yielded correlated `(29/32,3/64,3/64)` versus product common `(175/192,17/384,17/384)`. The support claim passed despite that deliberate law difference.

No broad network census, formal proof, joint gene-law enumeration, or physical intervention was performed. The one-coin mechanism is a correlated support-only repair; these checks do not equate it to the product common-inheritance full law.

## Admission and scope

The triangle/bigon/outgroup-tree fixtures passed the implemented degree, unique-root, root-LSA, hybrid-child-cut, and interior-rational-parameter checks. Outer-labeled planarity is deliberately external. The fixture has an explicit outer embedding: the triangle is outer, the parallel-arc bigons are pendant along the outgroup branch, and all pendant tree/leaf attachments may be placed in the exterior. The checks must not be described as a generic outer-planarity validator.

The full-law coupling is compatible with the policy: synchronize every site that could receive at least two sampled lineages; match the one possible lineage's natural Bernoulli choice to the common site's bit at each remaining site; share the coalescent randomness conditional on routing. Fresh independent environments per locus and persistent forcing for every lineage at the site are essential premises. The prototype computes only distinct-taxon quartet marginals and should continue to label the full-law conclusion as a proof obligation addressed by hand, not a tested general theorem.
