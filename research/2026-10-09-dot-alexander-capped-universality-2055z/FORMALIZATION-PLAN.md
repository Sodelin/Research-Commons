# Formalization obligations and existing providers

9 October 2026. This is a dependency plan, not a build certificate.

The new capped-host corollary is presently written-proof reviewed. Its precise original-model formalization should reuse the following rather than reproduce degree conservation:

- `InfiniteConservation.crossing_upper`, in `lean/SamuelAlexanderResearch/InfiniteConservation.lean`, Git blob `c78572a03f66054d5629661172692dc65b2913c1` in Sodelin/Work-on-Samuel-Alexander-Research-. For the actual `InfiniteLabeledPopulation k k`, it proves every actual crossing count is at most `k * fullRootCount p`. The full theorem body was read on 9 October; no new compiler replay occurred in this packet.
- The same module's `conservation`, `no_parent_at_or_after`, and finite support identities retain source-derived degrees and edges.
- Existing population reindexing must supply the map from the real-birthdate original population to the natural chronological interface. Its exact endpoint and all transports still need to be bound in this new proof.
- Existing `CapTwo.cap_two_avoider` / `avoiding_population_exists_iff` supply the binary nonempty class, with the documented original fixed-gender predicates. Their compilation evidence is historical, not newly replayed here.

New obligations, all required for the final result:

1. Define actual active-vertex bags from the original edges. Derive cardinality <= crossingCount + 1, interval supports and edge coverage. Do not assume an abstract width certificate.
2. Formalize the finite row/column cross intersection and interval Helly argument. Conclude no injective adjacency embedding of an n-grid when n exceeds the actual host bag bound.
3. Construct the finite padded grid population with real dates, missing-label root parents, actual finite child covers and row-striped fixed source genders. Prove all fields from the actual graph.
4. Construct the disjoint union with the actual infinite avoider. Derive the new root set and population conditions, and prove equality of infinite-word languages via finite-component acyclicity.
5. Compose those results into the full universal-host negation with the host chosen first, the grid size derived from its actual root count, and the rival within the same balanced child-cap class.
6. Audit every owned theorem/axiom, independently review the source statement, and record exact source/dependency hashes and executed commands.

Do not substitute supplied bag bounds, a generic graph embedding obstruction, or an abstract language-preservation assumption for these source obligations. Do not label the final result Lean-verified before all six stages compose. Connected-only, no-terminal, fixed-root-budget, countable-family and edge-to-path embedding variants remain outside the statement.
