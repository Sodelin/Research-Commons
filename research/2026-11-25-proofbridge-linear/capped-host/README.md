# Capped universal-host claim: reuse crossing, isolate the interval step

Claim `CB-ALEXANDER-001` stays pending as a whole. Its [written proof](https://github.com/Sodelin/Research-Commons/blob/7206e66a8de0b04725924e32df822eca530b1143/research/2026-10-09-dot-alexander-capped-universality-2055z/CAPPED-UNIVERSAL-HOST.md) concerns an adjacency-only obstruction in a fixed balanced child-cap class, not the nearby countable-host theorem.

- **Reused:** the existing `InfiniteConservation.crossing_upper` for naturally ordered populations. Rebuilt three original source modules at [the Alexander repository pin](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/tree/e2502c82ab9a77c00543932f775a71e5374221f7/lean/SamuelAlexanderResearch) and imported the bound in `CappedHostComponents.lean`.
- **Bridge lemma:** `commonBag` checks that a finite nonempty pairwise-intersecting family of integer-indexed bag intervals has one common index: choose an interval with the largest left endpoint. The two disjoint singleton intervals are a checked negative control for dropping overlap.
- **Still open in Lean for this card:** transport from real dates to natural chronological order, construction and size of actual bags, grid-cross hitting lower bound, eligible disjoint union preserving the infinite-word language, and final quantifiers including the fixed-gender version. No whole claim or novelty assertion.

[Source pins and fresh receipts](components.receipt.json).

## Next tactics for the five lanes

1. **Typed input:** Give each gap its own exact statement and premise IDs. Start with the interface from real birthdates to the existing natural-order model. Keep both statements side by side so an indexing convention cannot silently strengthen the claim.
2. **Lean:** Reuse the compiled crossing bound and the checked interval lemma. Write only the provider-consumer glue and verify types at each step; add a control that omits the chronology or overlap assumption.
3. **SMT:** Start in adversarial mode. Use small integer models to look for missing hypotheses in proposed bag or root recurrences. Where a decisive linear subgoal appears, pass the exact witness to Lean. Do not treat bounded solver failure as a graph or language proof.
4. **Batch:** Keep two lanes of execution inside the same queue policy: fast supported typed certificates and targeted, explicitly pinned import/interface rechecks. Quarantine unsupported work with a machine-readable blocker, not a repeated compile attempt. Don't compile a retained dependency closure unless affected.
5. **Discovery:** Rank by cheapest verified path: exact registered binding first; missing interface second; genuinely new proof third. Record dependencies and missing obligations individually, preserving the old exact claim scope.
