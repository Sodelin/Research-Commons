# Original continuous crosscut: same-map all-region composition candidate

Contributor: dot / OpenAI assistant for Nolan and Sodelin Research-Commons.
Status: UNCOMPILED own-source candidate, not a Lean-accepted theorem. Supplier and predecessor acceptance do not establish this composition's elaboration/kernel acceptance.

Target `Nanuq.ContinuousRegionCrosscut.continuous_crosscut_region` has only the original geometric hypotheses: Jordan boundary C; its supplied boundary cut pair A1,A2 between p,q; arbitrary continuous simple arc P; P∩C={p,q}; either specified original complementary region Ω; and P minus endpoints contained in Ω. There is NO original polygonality hypothesis.

The proof straightens P together with the reversed ORIGINAL A1 using one prescribed ambient homeomorphism, then derives the transformed Jordan/arc/cut-pair/region conditions. The accepted polygonal theorem gives two transformed labelled components. The proof pulls both back to the original drawing, retaining exact component exhaustion, disjointness/nonemptiness and closure(Vi)∩C=Ai. No arbitrary plane order, collar certificate, independent edge redrawing, boundedness of Ω or numerical endpoint-fixing assertion is inserted. Proper-plane homeomorphism transport, not orientation preservation, keeps inside/outside correct.

## Exact dependencies

- Three predecessor source joins: immutable source publication ea46c11a38f866250a393067be7bdc22f5273b27, scoped successor acceptance f2c8d9b03d352834d9b22426da51969aa8ac5af3. Directly checked five named types/standard axiom lists; full131audit was reported only, not independently transferred/scanned.
- Mathlib-only AmbientTransport: f01ece9269fa8c93a6e8ee4fd406a422e06dc7c0, `research/2026-10-31-nanuq-nonlinear-ambient-transport/AmbientTransport.lean`, SHAda8602339db6b3c5e33ae4ab428f7ebff680646e7829e7fcb9b7e8307e19c635.
- Public external supplier alonamaloh/schoenflies-lean05a43d29cde026618777db3d4e4316204ccca237, Álvaro Begué, Apache-2.0, in the already qualified proof-only compatibility context; Lean4.33.1 and Mathlib0df444a360eaa60ab8c11dca51a86af692955474.

No external code or held declaration audit is included or reuploaded. No local supplier build occurred. This is a separate small own-source candidate, not a retry/repackage of either blocked evidence packet.

## Original theorem gates remain

This candidate is a topological provider, not a proof of actual graph contour traversal. It retains two-arc/bigon applicability but does not establish bridge or vertex-star neighborhoods, block admission, coherent contour order, actual adjacent hybrid copies, or full original-network NANUQ circularity/support. The supplied original C is never replaced by a newly chosen order. Original distinct-resolution means are unchanged. Current full scope: research/2026-10-31-scope-reconciliation-0207z/CURRENT-SCOPE.md at6d331f9046b5ed74134b6461507f68f93965e62b.
