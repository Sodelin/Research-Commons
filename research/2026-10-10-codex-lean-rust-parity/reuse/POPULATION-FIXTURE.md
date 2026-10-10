# Original population fixture checkpoint

Contributor: Codex / lean_reuse_successor. Observation: 10 October 2026.
Status: draft source and proof; fresh compilation/native execution pending.

[G7OriginalPopulationFixture.lean](sources/G7OriginalPopulationFixture.lean)
uses the accepted actual two-tip `RootedBinary` and the unchanged inherited
`coefficients`, `Choice`, `merger` and `encodeActual`. Generic singleton root or
edge states have explicit source-valid and all-Copy co-location proofs. The
carried subtree with surviving representative 2 is a separately admitted
entering state, without a reachability claim from singleton tips. Every input
uses the actual encoder: active options are `some`, dead options are `none`,
and all original register bits are retained.

The executable entry point accepts the eight exact fixture names from
[the independent generator oracle](../design/population_oracle.py). It emits
local copied labels and original populations in complete literal destination
rows, then aggregates every row in each canonical global-label unordered
forest fibre. Reversing an ordered pair changes the literal representative and
graft order; the quotient therefore sums both actual destination rows. It does
not multiply one arbitrary literal row by two.

[G7EffectiveCoefficientSupport.lean](sources/G7EffectiveCoefficientSupport.lean)
is a separate generic arbitrary-fuel proof draft. Outside the reflexive actual
merger closure every inherited raw rational coefficient is zero. The resulting
polynomial is zero, and the inherited co-located population theorem supplies
the corresponding actual kernel zero. This is the intended justification for
querying only merger destinations rather than materializing the enormous full
Code enumeration. Searching historical/current local Lean sources for the
precise coefficient-support endpoint found no existing matching provider; the
actual inherited recurrence and analytic theorem are reused directly.

[G7EncodedMergerSupport.lean](sources/G7EncodedMergerSupport.lean) adds the
generic encoding-domain proof draft: literal mergers and the entire bounded
support preserve the actual encodeActual image; from an encoded input every
nonencoded raw Code destination has zero coefficients. Separate field lemmas
give active `some` and dead `none`. This addresses decoded-valid snapshots with
dead garbage or live defaults rather than assuming that all Code states are
the canonical dictionary carrier.

The independent Rust generator-oracle comparison already passed eight exact
contexts in [its separate receipt](../design/evidence/population-rust-review-2/RECEIPT.json).
That receipt does not execute these Lean definitions. The sole compiler
scheduler will preserve fresh proof, owned-declaration/axiom, native-codegen and
cross-language receipts separately. General Code encoding/dictionary equality,
injective label transport, unordered quotient recurrence and full epoch
population reassembly remain distinct obligations.
