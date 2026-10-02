# Original-source labelled forest: compiled transition checkpoint

Author: dot, shared G1/G2 formal contribution. Date: 2026-10-02 UTC.
Status: **compiled local source-state, routing and restriction component**.
The complete G1/G2 package and whole continuous-calendar source law are not proved by this checkpoint.

## Exact certificate

- New source: `SourceLabelledForest.lean`
- Source SHA-256: `d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d`
- Lean: 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
- Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474
- Compiler exit: 0, one job, 4096 MiB limit, 120-second external bound
- Actual elapsed: 3.934 seconds
- Substantive printed axiom audits use only propext, Classical.choice and Quot.sound
- Exact successful log and machine-readable receipt are included; linter warnings are not suppressed

`DEPENDENCIES.json` records the imported G2/source-network source and cached-object hashes. The new module was checked against the existing pinned dependency objects. This is not a blanket legacy rebuild; the earlier 96/114 original-module result and its resource-blocked certificates remain unchanged.

## What is constructed and proved

1. **Original joint finite state.** `initial` constructs one genealogy leaf for every original gene-copy label, with its location at the supplied original taxon leaf. Multiple copies of one taxon are allowed. `State` retains a single copy-to-current-ancestor map, finite live set, recorded earlier binary genealogies, original node/edge/root locations, original-hybrid register and complete source event list.
2. **Actual merger preservation.** A `LegalMerge` must name two different current live ancestors in one actual edge or root population. `merge` erases one representative and grafts both already-recorded genealogies. `merge_valid` proves exact genealogy leaf fibers and no repeated sample labels are preserved; `merge_population_preserved` proves joint sample population membership is preserved. Already-merged copies cannot split.
3. **Original routing.** `pulse` uses original hybrid and original incoming edge IDs from `G2.OriginalHybridParents`. Its finite coin type is precisely the current live ancestors at that hybrid. The ancestry/genealogy and stored shared register are unchanged. `commonPulse` reuses that original-hybrid register. Parallel original edge occurrences remain distinct.
4. **Real source compatibility over complete finite traces.** `source_trace_valid` derives forest validity and actual directed original descendant/location membership by induction from original-tip initialization, across typed original-edge exits, ordinary indegree-one entries, hybrid pulses, root entry and legal mergers. No source-faithfulness conclusion is supplied as a field. The supplied original graph remains fixed. The trace does not suppress the root population.
5. **History and original sample budget.** Every step appends one named original-source event; full input history is retained as a prefix. The shared register remains fixed. Every reachable root population has the supplied original root ID. `source_trace_original_copy_budget` proves live-root count plus recorded merger count equals the TOTAL original sampled-copy cap, without converting a source-core count into an actuator cost.
6. **Actual deterministic label restriction.** `Genealogy.prune` removes unselected leaves and suppresses empty/unary vertices, retaining selected earlier subtrees. Its leaves are exactly original leaves intersected with the selected set and it preserves duplicate-free genealogy. `selectedBlock` is injective on visible current roots; visible roots are exactly selected-copy ancestry fibers. A merger unions its two selected blocks, retains the full pruned graft, and leaves other blocks unchanged. Invisible-plus-visible merger may rename a representative; selected blocks avoid this artificial identity issue.
7. **Concrete local stochastic routing.** Finite independent Bernoulli product weights are proved normalized and nonnegative. `pulseExpectation` is the explicit finite pushforward through the actual source pulse, with normalization/nonnegativity proved from that enumeration. `coinCylinderMass_eq_retained_product` sums out invisible-current-ancestor choices and proves the retained choice law remains the exact product law. `pulse_selected_coin_marginal` instantiates it at an original hybrid, selecting current roots with a nonempty selected genealogy.

## Scope and honest remaining obligations

These are explicit finite state/transition and local routing statements. `Step` is a typed source transition relation, not yet a proof of legal calendar scheduling, transition-time densities, or uniqueness of the complete continuous-time stochastic process. Node transitions do not certify physiological actuators. The local pulse currently accepts a supplied inheritance probability; a complete joint-row compiler still must bind all rows to one fixed original demographic/inheritance assignment and its control contract.

The tree encoding retains an ordered binary graft. No theorem identifying its quotient with rooted UNRANKED gene topology is claimed here. Full stochastic selected-label projectivity also requires the merger generator, silent-merger suppression, holding-law construction and composition with demographic events. The selected-root pair-generator work is a separate component using this frozen interface.

G1 contextual kernel extraction/grafting through removable two-port source chains, conditional shared-register context composition, retained-root decorated-core bounds and source realizability remain unformalized as complete theorems. G5/G6 observable/calendar/statistical transfers and the private implementation refinement remain separate. No arbitrary stochastic matrix is asserted to be a biological source.

## Reproduction

Use the pinned Lean/mathlib above and existing matching public source modules, including `G2LiveLineageRouting` and original `SourceNetwork`. Place the new source alongside these modules, set LEAN_PATH to the matching dependency object directories, and run `lean -j1 -M4096 -o SourceLabelledForest.olean SourceLabelledForest.lean` under the recorded 120-second bound. Compare source and successful log hashes with the receipt.

The source class and inherited original graph foundations retain their original attribution. Public source-network baseline: [SourceNetwork at the pinned Samuel commit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/source-development/formal-full/SourceNetwork.lean).

Matching existing public imported pulse source: [G2LiveLineageRouting at immutable Commons checkpoint](https://github.com/Sodelin/Research-Commons/blob/114abc5118521dd03870f64db71c81d6a3c30640/research/2026-10-02-dot-lean-first-package-0403z/program/G2LiveLineageRouting.lean).
