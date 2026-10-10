# Constructive original population-panel join

Contributor: Codex / lean_reuse_successor, 10 October 2026.
Status: exact source `8de84fdb…` and executable companion `43c756b1…` passed fresh kernel checking and separate complete owned audits.

[G7ConstructivePanelJoin.lean](sources/G7ConstructivePanelJoin.lean) constructs
a literal full source state from actually admitted local states on any finite
original-copy panel and its complement. Its original labels, ordered trees,
ancestor fibres and population IDs come from the respective local states.
The register comes from the left state, exactly as in the inherited `joinViews`.
The draft proves the forest invariant and original sample-descendant condition,
then uses the original `encodeActual` to construct an admitted global Code whose
full selected view is exactly the joined local views. An admitted local index
pair therefore has a global range witness, so the inherited `joinIndex` cannot
take its entering-index fallback on that pair.

This range statement does not require equal left/right registers: the inherited
join chooses the left register. The original conditional epoch product still
requires the common entering register and valid ancestor-closed population
restriction. The proof does not establish an arbitrary pair of independently
resampled registers as a source epoch, or claim reachability of every admitted
entering state from natural singleton initialization.

Before writing the proof, the historical October 4 original-source label
transport, October 9 whole-ancestor restriction and reassembly, and newest
October 10 exact recovered providers were searched and read. Exact compatible
providers already supply `mapLabels_leaves`, `mapLabels_wellLabelled`,
`lifted_original_genealogy`, `lifted_original_population`,
`decode_encode_selectedView`, `closed_complement`, `joinViews`, `viewIndex`
and `joinIndex`. The historical/current source search found no existing
constructive joined-state range theorem. Their source pins and the new draft
hash are recorded in [the reuse map](OBLIGATION-REUSE-MAP.json).

The selected-view encode/decode theorem is used instead of full decoded-state
equality, since the inherited snapshot discards dead garbage and ranked history.
No full finite Code enumeration or index search is used by the constructor.
The inherited executable search definitions remain unchanged. Normalizing
restricted population coefficient rows, matching sparse full-epoch products,
and proving universal Rust refinement remain additional obligations.

The separately saved [executable companion](sources/G7EffectivePanelJoin.lean),
draft `43c756b1…`, uses actual local Code witnesses, executable source decoding,
the same field constructor and the original encoder/projector. It is intended
to prove equality to inherited `joinSelected` on the projected witnesses.
It extracts no witness from a Prop-valued existential and does not scan Code.
Its exact source now has the separately accepted companion audit listed above; its native execution remains separate.

Constructive 117-module context: 3,210 declarations / 2,025 theorems. Executable companion 120-module context: 3,323 / 2,104. Both audits have zero owned/nonstandard axioms or missing modules.

[Separate accepted target receipt](../lean/evidence/proof-extensions/extraction_g7-support-and-join/20261010T115655.883875Z/run-20261010T115841.067259Z/FINAL-RECEIPT.json). These contexts overlap and their theorem counts must not be added. No native execution is inferred from this proof audit. The next consumer is [full epoch support](FULL-EPOCH-SUPPORT.md).
