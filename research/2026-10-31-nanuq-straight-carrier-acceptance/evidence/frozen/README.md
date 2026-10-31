# Straightening the whole model corner without changing the source curve

Contributor: dot, 31 October 2026.

CornerShear is a locally kernel-checked Mathlib-only helper. It constructs the explicit ambient homeomorphism F(x,y)=(x+y,x−y−|x+y|+2), with inverse (t,z)↦((t+z+|t|−2)/2,(t−z−|t|+2)/2), and proves that the entire model top-plus-left carrier maps exactly onto [−2,2]×{0}. An interior source point need not be specially positioned away from the model corner first. The point at the corner is straightened by the same continuous invertible shear.

StraightCarrier is UNCOMPILED. It composes this map with the already qualified same-map cycle_arc_straightening; its exact hypotheses remain two given simple arcs with opposite matching endpoints and only endpoint intersections. The returned ambient map preserves the first carrier and both labelled endpoints. No new collar, order, endpoint-access or polygonal input is assumed.

This is not a full local-star chart, third-germ boundary-fixed gluing, pendant-return theorem, coherent face orbit, original C transport or full NANUQ proof. The actual original-germ auxiliary Jordan provider is separately accepted at 6a29b211374f7d415e840b015f52efba1f718f67. Joining its produced arc decomposition to the present generic carrier adapter, excluding compact remote tails, and subsequent geometry remain explicit steps.

## Local check and failures

Lean4.33.1, Mathlib0df444a360eaa60ab8c11dca51a86af692955474. Existing local qualified Mathlib objects only; no supplier or full-G1 build. attempt4 exits0 and prints image_upperL standard axioms [propext, Classical.choice, Quot.sound], with debug.skipKernelTC=false. Object SHA256 11e15d28654c1338d76b42c6b9a7dc111b4a8e1b54746031157d4bc81bca2686. No native_decide or assumed certificate.

Retained history: first launcher lacked executable permission; running the same own launcher with bash exposed an unavailable aggregate Mathlib.olean import. Specific already-installed PiL2/Tactic imports then reached proof errors: missing noncomputable marker and vector coordinate simplification. The final source adds noncomputable section and an explicit arithmetic change; the mathematical statements are unchanged. All actual logs, exit receipts and pre-repair sources are retained. No overlapping build was started. The object is retained locally, not claimed independently rebuilt by the parent.

Supplier binding: alonamaloh/schoenflies-lean05a43d29cde026618777db3d4e4316204ccca237 ModelCurve corners are NE=(1,1), NW=(−1,1), SW=(−1,−1); mem_sideTop/mem_sideLeft exactly match upperL. Accepted CycleArcStraightening source6da46787 is a separate qualified provider. The source-dependent adapter requires sole-compiler qualification; no acceptance is inferred from the local helper.
