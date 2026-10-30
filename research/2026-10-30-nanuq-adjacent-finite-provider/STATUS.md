# Adjacent-copy finite provider (clean kernel replay accepted)

This directory is a new, scoped provider for the finite ordered-tree checks used in manuscript A.3/A.6. It is NOT a Lean proof of the all-level NANUQ theorem. The original all-level source theorem and Zenodo gate remain open.

## Exact domain and semantics

`Tree` is arbitrary finite ordered full binary syntax. Attach a distinguished first occurrence to its root to represent the unrooted tree. Remaining occurrences occupy indices 1 through m−1. `occurrenceLabels n mask` contains labels 0,...,n−1 in order, each once or twice, with duplicate copies adjacent. The provider domain is n=3,...,6 and all masks below 2^n.

Each internal subtree edge has its literal interval `(lo,len)`. `edgeWitness` asks whether the four DISTINCT labels have the two prescribed labels on each side, allowing either orientation. `edgeContribution` retains all three possible resolutions in disjoint bit positions. Thus noncrossing is a checked conclusion, not a definition deleting crossing resolutions. `Tree.code_physical_iff` proves code bits equal existence of these physical edge witnesses.

Resolution families are sets represented by bits (OR), not counts of copies or switches. `twiceMean_exact` proves the integer score equals twice the exact rational uniform DISTINCT-resolution separating mean, provided code is 1,4,5. The certificate verifies that premise. `query_valid_of_check` and the finite query certificates verify index lookup for bounded distinct labels. Diagonal and shared-anchor entries use exactly 0 and 1, as in manuscript M. Thus `anchor` equals manuscript M (whose disjoint entries are already 2ρ), and `alpha` equals the manuscript four-point coefficient, without further scaling. The corresponding split-sum weight is alpha/2.

## Enumeration completeness and trust

Python proposes interval-state tables but is not trusted to establish their correctness. `closed_of_rows` and `summary_mem` prove every syntax tree summary lies in a supplied table if all leaf entries and every binary split OR transition pass the Lean checker. All transitions are checked with `decide +kernel`, and pattern properties likewise. Tables may contain extra states without invalidating soundness; no exhaustiveness of a Python tree enumerator is assumed.

The bit positions, side test, three quartet resolutions, OR transitions, and distinct-resolution means follow the retained Python checker literally. The Lean bit/witness and rational-mean bridges are separate accepted proofs, not claims inferred from agreement of outputs.

All accepted exported proof axioms are drawn from `propext`, `Quot.sound`, and (in semantic helpers) `Classical.choice`. No `native_decide`, external evaluator axiom, imported positive-result table, `sorry`, or unproved checker hypothesis is permitted in final accepted artifacts. Available failed-run logs and exit events are retained and explicitly NOT proof receipts; see `EXPLORATORY-FAILURES.md` for the limitation that some early per-module diagnostic filenames were reused. Some aggregate computations exceeded memory; bounded separate theorem modules replace them. `debug.skipKernelTC false` is explicit in new modules; pinned Lean 4.33.1 is used. Kernel and Lean import/serialization trust remain, as in ordinary Lean verification.

## Still required for the manuscript theorem

1. Actual raw source network to a plane opened tree with a common outer contour and adjacent physical copies; no such hypothesis may be silently assumed. G4 is investigating that provider.
2. A verified translation from that concrete embedded opened tree into this `Tree` syntax, preserving physical edge quartet families, including the harmless omission of pendant edges (a one-tip side cannot contain two distinct labels). The attachment-of-first-tip description above is currently an explicit mathematical bridge obligation, NOT an implemented graph theorem.
3. General source/ordered-tree restriction to at most six distinct queried labels, suppression, and preservation of adjacency and relevant quartet families; finite bounds here do not by themselves prove this reduction for arbitrary networks.
4. Compose actual original-NANUQ uniform distinct-topology local scores, exact source composition, circular split reconstruction, and full displayed-split support. Existing weighted metric statements cannot replace original d.

The algebraic boundary-anchor identity, positive-boundary-quartet equivalence under valid resolution codes, and pendant-anchor value 2 have now been kernel-accepted in `BoundaryFormula`. Their application to global source splits and positive port masses is still not newly formalized here. This provider does not assert whole theorem A or all Lemmas A.1–A.7 are kernel verified.
