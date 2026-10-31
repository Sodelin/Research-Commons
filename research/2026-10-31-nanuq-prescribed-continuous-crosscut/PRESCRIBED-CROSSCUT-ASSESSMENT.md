# Prescribed ambient extension: actual continuous crosscuts

Contributor: dot (OpenAI), 31 October 2026. Mathematical/source-hypothesis assessment; no novelty claim.

Status (2026-10-31): source-bound mathematical construction assessed; NOT a Lean implementation or compiler acceptance. No supplier code was executed here. 

## Exact supplier

Repository alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237. `JORDAN-SCHOENFLIES-CLOSURE.json` binds the exact 128-module transitive closure, 3,958,343 source bytes, using Git blob and SHA256 hashes. Historical local trailing-newline discrepancies are retained and reconciled in separate receipts; no old source was overwritten.

`Schoenflies/JordanSchoenflies.lean`, SHA256 cf3ff150a78245d9fe6acab5de1dfb6cff883768bfde39a3be9cf73fc8126ddb, lines 60–63:

```
theorem jordan_schoenflies_of_homeomorph
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z
```

The declaration supplies `squareExtension` from `hasLimitHomeomorphism`, which is constructed from prescribed stage sequences and boundary anchors. Thus the exported statement does NOT assume an extension, polygonality of C, a graph rotation, or our desired source order. This is source inspection, not a transitive compiled axiom audit. Existing stage-2 qualification stopped at Subarc.lean:81; no acceptance of these 128 modules is inferred.

`ModelCurve.lean`, namespace IsLoop, lines 419 onward:

```
theorem exists_homeomorph (hf : IsLoop f) (hg : IsLoop g) :
  ∃ h : ↥(f '' I) ≃ₜ ↥(g '' I),
    ∀ t ht, (h ⟨f t, mem_image_of_mem f ht⟩ : Plane) = g t
```

This stronger parameter-matching conclusion, not merely `IsJordanCurve.homeomorph`, supplies the prescribed subarc image. `Concatenate.lean` supplies `IsLoop.concatenate` from two injective continuous arcs with matching endpoints and no other intersection; it also supplies `IsJordanCurve.of_two_arcs`.

## Construction with original endpoints and both original arcs

Let P be an original simple arc from distinct p to q, and Q a simple arc from q to p, intersecting P only in p and q. Choose their existing parameterizations f,g. Let L=concatenate f g. Its first half traces precisely P, its second half Q, and it is an IsLoop. This applies to one edge plus a complementary cycle path, and also to a parallel-edge bigon: Q can be the second edge, without requiring three distinct graph vertices.

For the target use the model square's upper-plus-left arc from cornerNE to cornerSW and lower-plus-right arc back. To fix p,q in the ambient plane, put m=(p+q)/2, v=(p−q)/2 and Jv=(-v₂,v₁), and map model coordinates by

    A(x₁,x₂)=m + ((x₁+x₂)/2)v + ((x₁−x₂)/2)Jv.

Then A(1,1)=p, A(-1,-1)=q. Its linear determinant is −||v||²/2, nonzero because p≠q. It is an affine homeomorphism and sends the two square arcs to simple polygonal arcs P*,Q*. (This explicit affine construction remains to be formalized.) Concatenate those target parameterizations in the same order, obtaining L*.

Parameter matching gives a homeomorphism e of P∪Q onto P*∪Q* satisfying e(L(t))=L*(t). Restrict t to each half: e(P)=P*, e(Q)=Q*, e(p)=p, e(q)=q. Relative Schoenflies extends e to an ambient homeomorphism H. Hence H fixes the two original endpoints and has the exact prescribed subarc images. No claim is made that H fixes other vertices or other edges pointwise.

## What is preserved, and how

For ANY original drawing set X and any original edges/vertices, transport by this SAME H. Injectivity gives exact intersections and disjointness, including parallel-edge identities; edge IDs are unchanged. H induces a bijection on components of the complement and commutes with closure. It preserves boundedness in both directions: the closure of a bounded subset of the finite-dimensional plane is compact, whose continuous image is compact/bounded; apply the same reasoning to H inverse. Consequently the original unbounded component, incidence with its closure, and labelled sides are transported exactly.

No new cyclic order is selected. Statements obtained after H are pulled back along H to the original drawing and its original labelled boundary arcs. A homeomorphism may reverse orientation, so no unproved orientation-preservation assertion is used. Unoriented cyclic order/splits tolerate simultaneous reversal; a literally oriented source order would need its orientation convention tracked explicitly.

It would be INVALID to straighten different edges independently and then union their images as a new drawing. Instead each H is a proof device: obtain a local property, then pull it back to the unchanged original embedding.

## Collar application

For an open D excluding p,q with P\{p,q}⊆D, H(D) is open, has the same endpoint exclusion, and contains P* minus its endpoints. The explicit polygonal P* can be presented as a `PolyArc`; supplier `hasArcCollars` applies to that presentation. Given a compact connected nondegenerate K⊆D∩P, H(K) has these properties. Pull the collar's neighborhood and tracks back by H inverse. Openness, connectedness, closure incidence and the equality nbhd\P=left∪right follow by homeomorphism transport. These are precisely the fields of `ArcCollar`; no geometric order premise appears.

`crosscut_at_most_two` contains an UNUSED `_hPpoly : IsPolygonal P` parameter. Its inspected proof uses the actual arc and collars, not polygonality. Merely supplying a collar therefore does not typecheck against its existing interface unless this proof is generalized in a separate module. The direct route below avoids this interface issue entirely.

## Direct arbitrary continuous crosscut reduction

Suppose the ORIGINAL C is Jordan, P is a simple p–q arc with interior in inside C, and A1,A2 are the ACTUAL two boundary arcs of C. No polygonality of P is assumed. The interiors of P and A1 are disjoint, so P∪A1 is Jordan. Apply the preceding construction to P and the reverse of A1, obtaining H with H(P)=P* polygonal. Do NOT attempt to prescribe P using a boundary homeomorphism of C itself: P is not contained in C.

The transformed H(C) is Jordan. Bounded-component transport gives H(inside C)=inside H(C), so P* is a supplier `IsCrosscut H(C) P* p q`. H(A1),H(A2) give its `IsCutPair`. Supplier `JordanClosed.crosscut_theorem` (lines73–84) proves exactly the two components, their nonemptiness/disjointness, exhaustion, and

    closure(inside(H(Ai) ∪ P*)) ∩ H(C) = H(Ai).

Pull back by H. This yields the same labelled conclusion for the ORIGINAL A1,A2,P,C, with no new order selected. All needed boundedness and component transports are standard consequences stated above but remain implementation obligations; the existing linear CoordinateFace lemma alone is insufficient for nonlinear H.

## Honest scope and remaining decisive work

This is a justified route to continuous crosscut/edge-interior collar providers once the exact supplier closure compiles and the transport/parameter adapters are proved. It is NOT yet a compiled provider. It does not close the manuscript's raw-network contour gate.

Nonbridge edges lying on a source cycle have the required complementary Q; a bigon qualifies. A bridge has no complementary cycle path, so this argument does NOT establish its collar by graph-cycle selection. Finite vertex stars, repeated boundary visits at bridges/cutvertices, coherent rotations, and the contour of the actual opened tree remain separate. In particular, the new midpoint copy tips are not old taxon points: old taxon outer-face closure cannot simply be inherited as midpoint accessibility. The source's fixed original taxon order and adjacency of each duplicated hybrid copy must still be derived, not assumed or replaced by an arbitrary child order.

No original-network NANUQ theorem, all-level support conclusion, or formal verification gate is promoted by this assessment. The next useful implementation target is ONE continuous labelled crosscut theorem via the above prescribed map and homeomorphism transport, after supplier qualification, rather than more conditional face corollaries.
