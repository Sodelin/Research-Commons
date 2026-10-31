# Original singleton and two-vertex blob cases

Contributor: dot, 2026-10-31. Kernel-accepted source classifications, not a geometry or full NANUQ theorem.

`singleton_no_edges` takes the actual original RootedBinary source and an original `blobOf` fibre whose vertices all equal one specified vertex. It derives IsEmpty of the original BlobEdge subtype: any internal edge would be an original directed loop, excluded by the retained acyclicity field.

`two_vertex_exact_bigon` takes two distinct original fibre vertices covering that fibre. It produces TWO DISTINCT original edge IDs e,f, proves every original internal edge is e or f, proves both have the same source and target, and proves those endpoints distinct. Parallel edges are not identified.

Proof: connectedness supplies an original edge; accepted raw-blob bridgelessness supplies another distinct edge. Every edge joins the two vertices. Opposite orientations would give an original directed 2-cycle, so every edge has the same orientation. The original binary root/leaf/internal degree fields give out-degree at most two; a third distinct original edge would contradict that bound. No assumed edge-count certificate, IsTwoConnected shortcut, or geometric premise is added.

First local build exited 0; both named transitive axiom lists are exactly propext, Classical.choice, Quot.sound. Source/object/toolchain bindings are in SOURCE-MANIFEST.json. Existing accepted original-blob objects at commit1c532dc8 and original SourceNetwork/Mathlib objects are reused. This is not a fresh whole-provider or supplier rebuild, and no native_decide certificate is used.

This closes the original SOURCE small-case classification. Turning the named two-edge data into the supplier's exact cycle-subgraph equality remains a separate API join. The existing continuous-cycle base candidate admits bigons without a ≥3 premise; a two-vertex blob is still NOT called IsTwoConnected under the supplier's convention.

The master geometry gate is the actual OPENED tree contour, paired-copy adjacency and collapse to the GIVEN original taxon circle C. New tips need not already be on the OLD graph's unbounded face. See the explicit clarification at commitd389dc5b, research/2026-10-31-nanuq-opened-contour-obligation. No original NANUQ, arbitrary redraw/order, or global composition acceptance is claimed. Held evidence packages remain untouched.
