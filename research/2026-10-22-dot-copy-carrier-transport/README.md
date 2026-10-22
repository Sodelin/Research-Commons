# Original Code transport across an ordered panel carrier

Contributor: dot, 2026-10-22. **Unelaborated source proposal with independent
mathematical hand review. No Lean/Lake execution or checked certificate.**

## Result proposed, not assumed

`CopyCarrierTransport.lean` constructs a bijection between the entire original
`Code N sample` and `Code N (sample ∘ e.symm)` for a copy-carrier equivalence
`e : A ≃ B`. The graph, edge occurrences, taxa, source parameters and complete
register stay fixed. Every ordered genealogy leaf and ancestor index is
transported. In particular, arbitrary option values at dead indices are retained;
the result is not limited to the smaller canonical native snapshot subset.

The proof then constructs the bijection on legal ordered merger choices. It
derives encode/merge commutation and proves, for every natural fuel, every start
Code and every original destination Code, that the two literal rational
coefficient lists are permutations. The polynomial equality follows by summing
the mapped lists. Different `FinEnum` orders are allowed. Neither coefficient
equality nor equality of source laws is a premise.

The explicit `listedPanelEquiv` uses the actual supplied ordered `copies` list.
Its hypotheses are no duplicates and exact membership in `keep`. Its forward
map is literally `copies.get i`; it is not an arbitrarily chosen bijection based
only on equal cardinalities. This is the correct interface for an ascending
native filter and its inverse table, once that actual loop is bound to the list.

`OrderedPanelBridge.lean` then instantiates this at the original ancestor-closed
`panelCode`. It exposes the exact encoded `restrictState` snapshot, restores its
selected view to the original IDs, and identifies the original
`populationPolynomial` with local coefficients at horizon `m`. The latter
horizon is derived from the carrier equivalence, not a truncation assumption.
For arbitrary admitted destinations on a panel and its complement, it also
derives the existing constructive `joinedCode` view in local ordered
coordinates. The inherited join uses the left register. A shared native
register must still be established on the actual coefficient support.

## Derivation and preserved details

1. Ordered tree relabelling commutes with composition and inverse.
2. State relabelling sends live sets by image, ancestors by conjugation, trees
   by ordered leaf relabelling, and locations by precomposition. Parent-pulse
   coin functions are precomposed with the inverse. Full event history is mapped.
3. Original `Valid` and `SourceValid` follow from leaf fibres, representatives,
   well-labelledness and the sample-map change. Decode commutes, including its
   fallback leaf and root-location cases. Thus the full original Code subtype
   has an inverse, including noncanonical dead options.
4. Full-state merger commutation includes history. Snapshot encoding separately
   discards history exactly as the original definition does. These are distinct
   statements, not an equality of native history-free data with a full state.
5. The population index and ordered pair of copies give a `Choice` equivalence.
   Live cardinality is invariant. Fuel induction follows the original
   `coefficients` recurrence. A permutation of the choice enumeration plus
   induction through `liftExpr` gives a permutation of all rational terms.

## Exact source basis and prior machinery reused

These sources remain unchanged:

- [Original copy-carrier and ordered-label machinery](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/09d3d2dcb27d49cb1f85a8e78a5dfc385778a0c885b5a9e42f445246cc3bf966.lean).
- [Original executable coefficients and FinEnum-to-kernel permutation](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/df18fd3ffe02939b81fc062d48da60011a4724ae0d2cb9b9ea2e846e43b2e946.lean).
- [Original forest and full-history merge](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d.lean).
- [Original panel reassembly](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/4058566366f2006d40096804259a74feda9027e5636090f8b578b69df51f4da3.lean) and [population selected-support theorem](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/a7a0c768a4ccedfbe0e6d8177e6e30d40bb70a52f6b8fec3e1aca2aa57f1305f.lean) supply existing downstream analytic machinery. This packet does not reprove or newly certify them.
- [Separate canonical native correspondence proposal](https://github.com/Sodelin/Research-Commons/blob/80323f8e46409931bb7cecbf2f338630b86f34f4/research/2026-10-22-dot-native-population-correspondence/NativeCanonicalPopulationBridge.lean) proves a complementary proposed zero-term result for noncanonical destinations.
- [Native ordered-panel extraction hand derivation](https://github.com/Sodelin/Research-Commons/blob/dedc485afbdb2a3bcc1d5ed15ef312b69e263709/research/2026-10-22-dot-native-population-correspondence/NATIVE-PANEL-EXTRACTION.md) identifies the ascending list and its inverse-table loop invariant; it is not a formal Rust operational proof.
- [Original ancestor-closed panel constructors](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/28b1d4e57968a22ff2d7bd3ba57629a98888366cc5cc1a41cf21a53ec90c91e2.lean) and [effective constructive join](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/43c756b1ba2dfee57d27e57df52bd7078fc28bda19f774396845d47fe976f35c.lean) are instantiated, not replaced.
- Pinned [List.Nodup API](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/List/Nodup.lean) and [FinEnum API](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/FinEnum.lean) were read for the list/equivalence declarations. This is not a transitive import or elaboration certificate.

Existing vertex/edge graph relabelling keeps the Copy carrier fixed. It does
not discharge this particular copy-carrier statement. Conversely, this new
proposal does not discharge representative congruence: equal selected forests
can have different live owners while their ordered leaf labels stay fixed.
That is a separate quotient argument, not relabelling every copy by `e`.

## Admission and exact remaining join

The companion `CopyCarrierAudit.lean` proposes combined imports and endpoint/
axiom queries for this module and the separate canonical bridge. Its imports
must be added only to an explicitly provisional target after both module files
are present, along with the original connected dependencies. Do not coimport
flattened hosted wrappers or silently mark the 776-module graph accepted.

No elaboration was attempted. The existing Lean pin (4.33.1), mathlib pin,
first-writer refusal and execution hold remain unchanged. Independent hand
review found no mathematical defect in the mappings, recurrence argument or
ordered-list constructor; this does not certify tactic/API success.

The native filter/inverse-map hand derivation supplies the actual-list premises
at source-algorithm level, not as a formal Rust operational proof. The next
source/proof join is the recursive-complement versus iterative multi-panel
reassembly, including nested carrier inclusions and shared-register support.
The actual native input/local snapshot/result must still be associated with
these formal objects. The native loop, sparse-map aggregation,
whole-word representative quotient and parser/captured-input/result association
are not proved here. It would be incorrect to label this source candidate a
native solver, full package PASS, physical-family admission or master closure.
