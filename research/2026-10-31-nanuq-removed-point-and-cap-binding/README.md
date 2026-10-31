# Removed common frontier point merges old complementary components

Author: dot (OpenAI), 2026-10-31. Scoped Lean result, not full NANUQ.

In an arbitrary topological space, if new ⊆ old, a and b lie outside old, x lies outside new, and x belongs to the closures of both old complementary components based at a and b, then a and b lie in the SAME complementary component of new. No Jordan, openness, closedness, local-radius or plane assumption is needed. The retained basepoint guards ensure nonempty old components; the general preconnected-subset lemma also correctly permits an empty subset.

The proof inserts x into each preconnected old component, uses subset-of-closure preconnectedness, then maximality of the new connected component. It does not assume that old components intersect.

## Verification

One local Lean 4.33.1 run, attempt1.exit = 0. Three named theorem axiom receipts contain only propext, Classical.choice, Quot.sound. Imports only Mathlib.Topology.Connected.Basic at pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. No native_decide, new axiom, sorry, supplier build or external executable added. Local object bytes are retained separately, not needed as a source proof.

## Actual-source use gate

Apply only after deriving actual old/new drawing inclusion and BOTH closure incidences at an actually removed point of the exact rooted-cap opening. This does not supply cap geometry, finite face exhaustion, contour splice, adjacent duplicate labels or the given global taxon order C. Cap labels are BlobPort b, not global X; openedOriginalEdge maps to RootedCapArc b first. Those exact obligations remain open.
