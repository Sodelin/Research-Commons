# Boundary-fixed crosscut gluing: exact supplier closure assessment

Status: HAND / API assessment only, no new Lean source or compiler request. The pending StraightCarrier adapter is not assumed qualified. This assessment uses separately accepted ContinuousRegionCrosscut and the qualified upstream closed-interior extension.

## The required theorem

Given a Jordan curve C, two distinct boundary points p,q and its labelled boundary arcs A1,A2, let P,Q be simple crosscuts of the bounded region inside C with those endpoints. An endpoint-fixing homeomorphism m:P→Q should extend to an ambient homeomorphism H of the SAME plane fixing C∪outside C pointwise and carrying P onto Q with the prescribed map. This is stronger than unconstrained Jordan–Schoenflies; it must be constructed, not inferred from that theorem's name.

## Exact existing supplier types

Upstream alonamaloh/schoenflies-lean05a43d29cde026618777db3d4e4316204ccca237, Endgame.lean316:
`closed_interior_extension squareExtension hCi hCi' hfg` returns full-plane functions Fi,Gi with IsHomeoOn on Ci∪inside Ci and Ci'∪inside Ci', and EqOn Fi f Ci. It is NOT already an ambient homeomorphism fixing the outside. squareExtension is discharged by qualified JordanSchoenflies.

Accepted own ContinuousRegionCrosscut.continuous_crosscut_region gives regions Vi of Ai∪P, disjoint with union inside C\P, nonempty, and closure Vi∩C=Ai. It does not literally print the three closed-piece identities below; those must be derived.

## Derive the exact three-piece geometry, with no new input condition

1. Each Vi is bounded because Vi⊆inside C. It cannot be the outside region of Jordan Ci=Ai∪P, since that region is unbounded. Hence Vi=inside Ci. The input arcs and endpoint-only intersection give Ci Jordan by the accepted two-arc theorem.
2. Write Di=Ci∪inside Ci. The partition inside C\P=V1∪V2, P\{p,q}⊆inside C and C=A1∪A2 imply D1∪D2=C∪inside C.
3. D1∩D2=P: the interior regions are disjoint, each misses P and the original boundary C, and C1∩C2=P since A1∩A2={p,q}⊆P.
4. With E=C∪outside C, Di∩E=Ai. These three sets D1,D2,E are closed and cover the whole plane. Do the same for Q, obtaining D1',D2',E with corresponding intersections Q,Ai.

## Boundary and ambient pasting

For each i define boundary map fi on Ci by m on P and identity on Ai, and inverse gi by m⁻¹ on Q and identity on Ai. Endpoint fixing makes the prescriptions agree on Ai∩P. Finite closed pasting on compact arcs gives continuity and the inverse identities, hence IsHomeoOn fi gi Ci Ci'. This is the actual boundary certificate to derive, not an opaque assumed order or access certificate.

Apply closed_interior_extension to both labelled cells. The returned maps Fi agree with m on P and identity on Ai. Their inverses Gi agree with m⁻¹ on Q by their inverse identities and boundary agreement; it must be proved, not silently assumed from EqOn Fi alone. Paste F1,F2 and identity on the three source closed pieces; paste G1,G2 and identity on the corresponding target pieces. Region-on-region mapping, overlap agreement and finite closed pasting show the two global maps continuous and mutually inverse. Endgame.lean422ff provides the analogous two-piece inverse-agreement and global-pasting pattern, not this three-piece conclusion for free.

## Remaining source use

This would straighten a third original germ cut at its first exit from a small half-disk while fixing the diameter and first two germs. Only after excluding the compact residual third-edge tail and other original trace may one shrink to a labelled three-spoke neighborhood. The generic gluing theorem alone does not prove that source localization, coherent orientation, refinement independence, complementary-face orbit identification or original taxon order C. No new hypothesis is added to the admitted drawing.
