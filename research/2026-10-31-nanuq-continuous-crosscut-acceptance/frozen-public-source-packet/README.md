# NANUQ continuous-crosscut joins — three UNCOMPILED source candidates

Own research proof-source candidates for Nolan / Sodelin Research-Commons. These are not Lean-verified results. Underlying supplier acceptance does not imply these compositions elaborate or pass the kernel.

## Exact proposed targets

1. `Nanuq.GeneralRegionCrosscut.polygonal_crosscut_region`: arbitrary Jordan boundary C and genuinely polygonal simple crosscut P in either original complementary region Ω. Proposes two distinct labelled exact components of Ω minus P, their exhaustion/disjointness, and closure intersection with each given boundary subarc. It does NOT assume C polygonal or Ω bounded. Side selection and collars are supplied by existing theorem bodies, not extra order assumptions.
2. `Nanuq.PrescribedLoopAmbient.loop_parameters`: extends the parameter-matched boundary homeomorphism to ONE ambient plane homeomorphism, retaining pointwise agreement and exact images of every parameter subset.
3. `Nanuq.PrescribedLoopAmbient.cycle_arc_straightening`: joins two given cycle arcs, uses the same prescribed ambient map, and identifies both subarc images and individually labelled endpoints with the model square arcs/corners. Includes the parallel-edge bigon case at the two-arc interface. It genuinely proves polygonality of the first image, rather than assuming the original edge polygonal.

Endpoint precision: this H maps original p,q to specified distinct square corners. It does not claim numerical H(p)=p and H(q)=q. All eventual component/order conclusions must be pulled back to the unchanged original drawing and its original labelled endpoints. No new source order is selected and independently redrawn edge images cannot be unioned. Literal numerical endpoint fixing by an affine target is an optional stronger construction, not needed for the original pullback conclusion.

## Dependencies and qualification

External supplier: Álvaro Begué, alonamaloh/schoenflies-lean, upstream05a43d29cde026618777db3d4e4316204ccca237 (Apache-2.0). The qualified compatibility context uses Lean4.33.1 / Mathlib0df444a360eaa60ab8c11dca51a86af692955474 and proof-only Subarc/InitialPair/Endgame repairs. These source candidates import supplier modules but do not include or repackage supplier code or declaration audits. No local supplier execution was performed for this packet.

Imports: GeneralRegionCrosscut imports Schoenflies.JordanClosed; PrescribedLoopAmbient imports Schoenflies.JordanSchoenflies; CycleArcStraightening imports the preceding own PrescribedLoopAmbient. Compile the latter two in that order. Named `#print axioms` commands are present but have NOT yet produced acceptance receipts for these candidates.

## Remaining original theorem gates

The full continuous-crosscut adapter is not yet composed/compiled. Actual source interface reconciliation, bridge neighborhoods, vertex stars, coherent contour traversal, the chosen original geometric taxon order, adjacent duplicated hybrid copies, and full original-network NANUQ circularity/support remain open. No switching-weighted metric replaces the original distinct-resolution mean.

This is a separate small source-only candidate packet. It contains NO bytes from the separately held declaration-audit publication packages. Their permission/status remains independent; this packet does not imply those packages were published or bypass their gate. Index these as candidates only in the existing discoveries catalogue.
