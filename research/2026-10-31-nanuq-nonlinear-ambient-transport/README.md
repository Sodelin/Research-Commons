# Nonlinear ambient transport for the NANUQ continuous-crosscut join

Own research adapter; kernel-accepted Mathlib-only component, not the full NANUQ theorem.

`AmbientTransport.lean` supplies seven endpoints in `Nanuq.AmbientTransport`:

* `bounded_image`, `bounded_image_iff`: homeomorphisms between proper metric spaces preserve boundedness, without a false Lipschitz assumption. Proof uses compact closure and the inverse map.
* `component_image`: exact image of the ORIGINAL complementary component at the given outside point.
* `inside_predicate_iff`, `outside_predicate_iff`: literal predicates defining supplier `Schoenflies.inside` and `.outside` in pinned `CrosscutCells.lean:74–80`. No new choice of face is introduced.
* `closure_inter_pullback`: exact labelled boundary-incidence equality pulled back under the SAME ambient map.
* `outer_face_transfer`: original outside point, unbounded complementary component and all original labelled closure incidences transported together.

This is the nonlinear step needed by the prescribed Jordan-boundary-map construction. A homeomorphism may reverse orientation; no orientation claim is made. It does not supply the homeomorphism or assert a new embedding has the same order. No supplier module is imported or executed by this packet. Existence/qualification of the relative Schoenflies supplier, the parameter-matching boundary adapter, source full/extracted interface reconciliation, actual bridges/vertex stars and original contour/adjacent-copy order remain open obligations.

Verification: one-module clean replay exit 0 with Lean 4.33.1 and Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. `debug.skipKernelTC false`. All seven explicit axiom checks list only propext, Classical.choice and Quot.sound. No sorry/native_decide/custom axioms. Cached Mathlib dependencies were used; no inherited NANUQ package was rebuilt. Nonsemantic linter warnings about unused ProperSpace section variables are retained in the log. Earlier failed elaboration source/logs remain in the private working evidence directory; only the accepted exact source is in this public packet.

Replay with an already installed exact toolchain/dependency cache:

```
python replay.py /path/to/lean /path/to/output /path/to/mathlib/.lake/build/lib/lean [other dependency lib/lean directories ...]
```

The wrapper is provided for portability; the saved clean replay used the equivalent direct Lean command. Source/object/compiler hashes and exact endpoint counts are in RECEIPT.json. Publication or indexing must retain this component-only status.
