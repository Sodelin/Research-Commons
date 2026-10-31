# Arc Jordan-neighborhood target for actual pendant localization

Status: constructive hand route / missing formal supplier, NOT an accepted theorem or an assumed source condition.

The narrow target is: if A is a compact simple planar arc and U is open with A⊆U, there is a Jordan curve C with A⊆inside C and C∪inside C⊆U. No prescribed endpoint straightening is required.

A route using the retained suppliers is as follows.

1. Choose a large ball containing a small neighborhood of A. The unwanted set K inside a slightly larger closed ball but outside U is compact and disjoint from A. For each x∈K, the unconditional arc-complement polygonal-connection theorem joins x to a fixed point beyond the large ball by a compact path avoiding A. A small ball at x can be added without hitting A. Compactness gives finitely many such balls covering K and a positive uniform clearance from A for all these paths/balls. Thus every point of K can still reach infinity while avoiding a sufficiently thin neighborhood of A.

2. Take a sufficiently fine finite union of grid cells covering A in its INTERIOR and lying in that thin neighborhood. Arrange edge connectivity, not merely corner contact; a neighbor padding of cells meeting connected A supplies this, but its exact finite-grid proof is owed. Use the graph consisting of all boundary edges of the selected cells, retaining each grid edge only once. Each cell boundary is a cycle, and gluing an adjacent cell shares a WHOLE edge (two distinct vertices). Along an adjacency spanning tree, the existing two-connected-union theorem therefore makes this auxiliary boundary graph2-connected. It is a finite polygonal drawing. This graph is auxiliary geometry, not a replacement physical network.

3. The qualified face-cycle theorem gives a simple cycle bounding its unbounded face. Covering A by interior cells keeps A away from that outside boundary; all A points are enclosed. The saved clearance paths keep every point of K in the unbounded component of the grid graph complement, so none is enclosed by its outer cycle. The bounding cycle and its inside stay in the large ball, hence avoidance of K ensures the entire closed Jordan domain lies in U, including any holes filled by taking the outer boundary. Merely knowing the grid cells themselves lie in U would NOT suffice: filled holes could otherwise contain unwanted points.

Formal obligations include precise finite grid selection/padding, its edge-connected adjacency, exact 2-connected unions with distinct shared vertices, outer boundary avoidance of A, and the bounded enclosure argument. The existing supplier arc-complement proof uses related square-chain machinery, but no inspected theorem already states this arbitrary-U Jordan-neighborhood conclusion.

For an actual leaf prefix, choose U disjoint from other original trace apart from a controlled continuation near an interior attachment point. The degree-two continued-arm chart can make that continuation straight locally. A further boundary-splice construction is needed to obtain a Jordan localization with exactly ONE attachment crossing. The Jordan-neighborhood theorem alone is not silently promoted to this stronger source condition. If that splice is established, the separate one-ended-slit doubling/folding lemma supplies the local face-return around the leaf. Coherent global face-orbit/C transport still remains.

## Explicit finite grid selection and buffer

Use all CLOSED mesh-h cells meeting A, then add their one-cell Chebyshev neighbor padding. Finiteness follows from compact boundedness, not from a finite number of intersections of the arc with grid lines. The original meeting cells form a connected graph under corner-or-edge adjacency: otherwise their finite unions split connected A into two nonempty disjoint relatively closed pieces. Nonadjacent groups have separated cells, so this is an actual separation argument.

Each padded3×3 block is edge-connected. Padding blocks of corner-or-edge adjacent original cells overlap, so the padded cell collection is edge-connected. It contains the open sup-norm h-neighborhood of A and lies within sup-distance at most2h from A. This supplies the required POSITIVE interior buffer even when A runs along a grid line or passes through grid vertices infinitely often. Choose h below the finitely obtained clearance bounds.

The graph for the 2-connectivity induction is the FULL UNION OF CELL CYCLE SKELETONS, including all interior shared grid edges, not just the exposed polygonal boundary. The latter may have multiple components around holes. An edge-adjacent enumeration of the padded cells exists from their finite connected adjacency graph; every new square cycle shares a full grid edge with the preceding union. Only after proving this full skeleton2-connected and invoking its actual unbounded-face cycle do we select the enclosing Jordan curve.

## Compact obstacle formulation of the clearance step

Choose the far anchor q outside a fixed containing box for all selected grid cells. For each x in compact K, select a path x→q off A and a small CLOSED ball centered at x, disjoint from A. The corresponding OPEN balls cover K; choose finitely many. Their closed balls together with their chosen compact paths form a single compact connected set H disjoint from A, containing K and q. Positive distance between H and A then keeps the whole grid skeleton disjoint from H. Since q lies outside the containing box, H lies in the unbounded component of the complement of every resulting enclosing Jordan cycle, so K does too. This is a finite compact witness, not an assertion that arbitrary pointwise paths have a uniform clearance. The exact grid and Jordan-enclosure implementation remains owed.
