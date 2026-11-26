# ProofBridge effectiveness review after the shared bag proof

## Decision

Keep the current architecture. It has stored, checked, and reused a complete **subargument** of Alexander-001. It has not yet proved the whole theorem, made arbitrary prose portable, or demonstrated an end-to-end authoring speed gain.

## What changed since the earlier audit

- The [natural-order grid obstruction](capped-host/RESTORE.md) now runs from the actual host graph to the common bag to the final count. A source-only recovery archive was rebuilt with the pinned compiler. Source and dependencies are recoverable even if the old install is lost; live scheduler state is separate.
- [Word preservation under padding](capped-host/PADDING-LANGUAGE.md) is Lean-checked under no cross edges and a bounded rising rank. A one-vertex loop shows why finiteness alone is insufficient. This isolates a smaller verification obligation for the actual grid.
- A [grid-minor transfer](capped-host/MINOR-TRANSFER.md) has a checked width-projection step. The full branch-set argument is not Lean-checked. Do not count it as a second theorem closure.
- Still open in Lean: construct the eligible capped grid with the exact label semantics, including the fixed-source-gender variant; transport the real-date model; assemble the exact full result.

## Direct comparison on the same contract

The branch projection was checked both by importing the existing grid lower bound and by inlining that same reasoning. An independent consumer type-checked both proofs against the same exact contract. Both have the same axiom report. Five trials gave median times of 0.781 s for inline, 0.726 s for checked import with the provider already built, and 1.502 s for rebuilding that provider and checking the import. The inline file had 54 nonblank lines; the importing consumer had 19, excluding the provider. This shows less duplicated source at the consumer, not less total initial authoring. The small warm timing difference is not robust evidence of a meaningful speedup. The cold import was slower in this small case; the earlier larger closure benchmark is not contradicted. [Reproducible comparison](capped-host/audit_projection.py) · [Receipt](capped-host/projection-ablation.receipt.json).

## Lane assessment

1. **Typed handoff:** Passed the original five-premise to three-premise relay. Strong at scope preservation for prepared statements; no automatic port of a full prose proof.
2. **Lean:** Passed the reused theorem checks and rejected the weaker provider. Strongest value here is changing one interface without reauthoring dependencies, not raw compile time.
3. **SMT:** Repeated exact scale-two integer rounding with independently checked Lean proofs. Useful bounded arithmetic; not a general search for new mathematical structure.
4. **Batch:** Resumable typed worker test passed again. The two-job scheduled pilot and clean rebuild establish feasibility, not continuously checking every new proof on main or rebuilding across lost hosting.
5. **Discovery:** Rejoined the exact scoped results and preserved authored status. The prior 13 registered reuses among 70 historical IDs remain evidence of avoided duplicate work, not 13 fresh Lean builds or a count of novel results.

## How to decide if the extra elegance paid off

For the next exact interface, capture statement formulation, discovery, authoring, repair, checking, and queue wait separately; keep a simple direct route. To test transfer, give fresh direct and reuse attempts the same exact held-out claim and budget, then independently replay the result. On later claims, only count actual successful imports or avoided rewrites. Do not turn beauty, lines of Lean, or scheduled activity into a success metric on their own. The decisive next milestone is one end-to-end exact Alexander-001 theorem, not another tool format.
