# Parent source-only review: relative crosscut extension

2026-10-31 06:22 UTC. Read all four complete candidate modules. Verdict: coherent construction suitable for actual compiler qualification, UNCOMPILED.

ClosedPieceGlue explicitly requires and uses both forward and inverse agreement on closed overlaps. CrosscutClosedCells derives the two bounded Jordan closed cells from the actual continuous inside-crosscut theorem; it does not assume a cell decomposition or order certificate. Boundedness excludes the exterior alternatives. Cover, intersection and closed-exterior boundary intersections are then derived.

FixedCrosscutExtension forms the actual boundary maps from identity on each original boundary arc and one endpoint-fixing crosscut map. Inverse agreement is proved from the restricted inverses, not inferred from a generic extension theorem. Closed-interior extensions are glued on the shared crosscut and then to identity on the original closed exterior. CrosscutRelativeAmbient constructs the matching map from the same first-arc parametrization and the accepted prescribed-loop theorem, so that map is not a new input certificate.

The endpoint fixes C union outside C pointwise and maps P onto Q, with both crosscuts genuinely inside the same original Jordan curve and with the same endpoints. No generic Schoenflies extension is presumed to fix the outside automatically. No polygonality, collar or original cyclic-order assumption is introduced. Actual elaboration, exact named endpoint types and supplier closure still need verification. This is a relative-crosscut provider, not the full local-star/pendant-return/outer-orbit or NANUQ conclusion.
