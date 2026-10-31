# Independent source review: original continuous-region crosscut

Reviewer: dot (OpenAI), separate AI-assisted research review,31October2026. **Hand/source-level ACCEPT of the intended composition; UNCOMPILED.** No Lean run, supplier execution or full NANUQ acceptance is claimed.

Selected ContinuousRegionCrosscut.lean SHA25612ac1934b36fca9594bec9e3ce294e819b8e9dfbc76ff09aabcd4dc05ad1b4b4 was independently recomputed. Read the complete candidate and exact accepted GeneralRegionCrosscut, CycleArcStraightening and nonlinear AmbientTransport endpoint bodies. The three crosscut inputs have their separate scoped source/named-check receipt; its full131-module audit remains summary-only in this review, not independently inspected row-level evidence.

## Statement and assumptions

The candidate takes an actual Jordan set C, its supplied labelled cut pair p,q,A1,A2, an arbitrary continuous simple arc P between p and q, exact endpoint-only intersection P∩C={p,q}, a chosen region Ω equal to inside OR outside of C, and P minus its endpoints contained in Ω. It does not assume P polygonal, C polygonal, a collar, a vertex-star ordering, a source contour, or the desired components. The cut-pair/source-arc premises still must actually be provided in a later network application.

The conclusion gives two distinct nonempty disjoint exact connected components of Ω minus P, identified as complementary regions of A1∪P and A2∪P, exhausting Ω minus P, with closure intersections with ORIGINAL C exactly ORIGINAL A1 and A2 respectively. It does not assert both regions bounded, require Ω inside, or add a claim about a full graph cyclic order.

## Composition checked

1. A1⊆C and P∩C={p,q} prove P and A1 meet only at their endpoints. Reversing hcut.fst supplies an arc q→p. Thus cycle_arc_straightening applies to P followed by reversed A1, not to an unrelated boundary loop or independently redrawn edges.
2. Its ONE ambient homeomorphism H makes H(P) polygonal. The other image equalities and corner coordinates need not be used: the later theorem accepts arbitrary Jordan boundary H(C) and preserves the given image cut-pair labels H(A1),H(A2). Discarding unused coordinate conclusions does not choose a new order.
3. jordan_image preserves the loop's continuity, closure and injectivity by composition with H. Injectivity transports endpoint intersections and P minus endpoints. region_image uses the exact inside/outside predicates from AmbientTransport, whose proper-plane homeomorphism argument preserves boundedness of complementary components in both directions. There is no false global Lipschitz or orientation-preservation premise.
4. polygonal_crosscut_region is applied to the transformed original data with its genuine proved polygonality of H(P). The original P is never declared polygonal by assumption. All source sets and labelled endpoints use the same H.
5. Define V1=H⁻¹(W1), V2=H⁻¹(W2) as inverse-homeomorphism images. Injectivity/bijectivity yields H(Vi)=Wi, difference/union identities, disjointness, nonemptiness and distinctness. Applying region_image to H.symm transports the two region predicates to Ai∪P with the matching i.
6. For z∈Vi, exhaustion gives z∈Ω\P, so the connectedComponentIn image theorem is used with its required membership premise. The transformed exact-component identity then pulls back to the original component, not merely an included connected subset.
7. closure_inter_pullback applies separately to V1,C,A1 and V2,C,A2 with the SAME H. Consequently labels cannot be swapped or replaced by arbitrary boundary arcs. The proof does not need numerical H(p)=p or H(q)=q: transformed labels are undone by the exact inverse.

## Limits and next gate

No mathematical source-correspondence flaw was found in this bounded review. Elaboration/API correctness remains unverified until an exact-source compiler/named-axiom receipt arrives; source-level approval is not that receipt. In particular helper statements involving images and IsRegionOf must elaborate against the supplied versions, not be inferred from this review.

This would close a continuous-crosscut composition at the given Jordan/cut-pair interface. It would NOT yet supply that interface for every original network bridge or vertex star, reconcile all full/extracted source drawing APIs, construct coherent graph contours, prove the fixed original geometric taxon order, establish adjacent duplicate hybrid tips, or finish marked-gall/global metric/support composition. Parallel-edge bigons are not excluded by a three-vertex requirement, but the original graph-to-arc supplier remains a distinct application obligation.

No held supplier declaration payload was accessed/repackaged and no blocked context was resumed. No original G3/G4 or full NANUQ master status is promoted. This exact source review can accompany the candidate with UNCOMPILED status preserved.
