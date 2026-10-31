# Constructive degree-two/three germ route from actual continued arms

Status: mathematical construction, not a compiled Lean theorem. Parent checked the compact-extrema trimming argument. This note strengthens the earlier supplier assessment without assuming polygonal accessibility of an arbitrary continuous endpoint.

## A. Close two ACTUAL continued arms into an auxiliary Jordan curve

Let two distinct original incident edge germs at v be oriented away from v. Choose parameters0<a_i<b_i<1 before either other endpoint. Let A_i be the initial image through a_i and J_i the continuation from a_i through b_i. Put q_i=gamma_i(a_i), r_i=gamma_i(b_i). Faithful original incidence makes A=A_1 union A_2 a simple arc from q_1 to q_2 through v, and makes J_1,J_2 disjoint compact simple arcs. Each J_i meets A precisely at q_i. This still works for parallel original IDs: all cutpoints precede the common far endpoint.

The actual supplier `Schoenflies.arc_complement_poly` applied to A and distinct r_1,r_2 gives a SIMPLE polygonal arc P in A-complement joining r_1,r_2. No endpoint-access premise is used: r_i are OFF A; accessibility from q_i is supplied by the actual continuations J_i.

Choose an injective continuous parametrization p:[0,1]→P with p(0)=r_1, p(1)=r_2. The set S_2={s:p(s) in J_2} is nonempty closed in the compact parameter interval; let s=min S_2. Since r_1 notin J_2, s>0. The set S_1={t in[0,s]:p(t) in J_1} is nonempty compact; let t=max S_1. Disjointness J_1 intersect J_2=empty forces t<s. By the two extremal properties p((t,s)) meets neither J_1 nor J_2.

Let B be J_1 from q_1 to p(t), followed by p([t,s]), followed by J_2 backwards from p(s) to q_2. Access subarcs exist uniquely by injectivity. Each piece is simple; the first and third are disjoint, and the middle meets them only at the intended junctions. Their concatenation is a simple arc. P avoids A and each J_i meets A only at q_i, so B intersect A={q_1,q_2}. Consequently A union B is a Jordan curve containing the two ORIGINAL incident germs at v.

There is no finite-intersection assumption. A polygonal path may meet a continuous access arc infinitely many times; compact minima/maxima remove all unwanted intersections in one operation. The auxiliary B may meet remote portions of other original edges, but it is compact and misses v. Shrinking the eventual local neighborhood excludes B and all such remote intersections. It is not being added as a physical network edge.

## B. Boundary-fixed straightening of a continuous crosscut

The following constructive lemma is needed for the third germ; it is NOT asserted already present as a named supplier.

For a closed Jordan disk Delta, a continuous simple crosscut P from distinct boundary points p,q, and a model crosscut Q with the SAME endpoints, choose any endpoint-matching homeomorphism m:P→Q. Let A_1,A_2 be the boundary arcs between p,q. On each Jordan curve A_i union P prescribe identity on A_i and m on P. Closed-set pasting gives a boundary homeomorphism to A_i union Q. The exact `closed_interior_extension squareExtension` supplier extends each boundary map to its corresponding closed bounded Jordan domain.

The continuous crosscut theorem identifies those two closed domains as covering Delta and meeting in P; the target domains meet in Q. The two maps agree on P and are identity on the outside boundary. Paste them together, and paste the identity on the closed exterior of Delta. Do the same for their inverses. Finite closed pasting gives mutual continuous inverses, hence an ambient homeomorphism H fixing the outside of Delta pointwise and carrying P to Q with the prescribed parametrization. No arbitrary extension is assumed to fix the outside: fixing it is supplied by this explicit two-cell plus exterior gluing.

This derivation needs the closed-region cover/intersection identities and relative pasting to be implemented. The accepted continuous region theorem and proper ambient inside/outside transport provide the exact region data; the pin's Endgame.lean316 `closed_interior_extension` provides the closed-domain homeomorphisms when supplied with the already proved `squareExtension`.

## C. Apply A and B at a degree-three original vertex

Use prescribed Jordan–Schoenflies on A union B to make a neighborhood of v on that Jordan curve a straight line, respecting the two arm labels. A boundary parameter map must place v in the interior of a straight model edge, not silently at an inconvenient square corner. The parameter map can be specified on the two subarcs of A at v and B, just as in the existing prescribed-loop construction; this is another finite boundary-map obligation, not a new assumed order.

The third initial original germ avoids A union B away from v after shrinking (B is compact and misses v). It lies on one side of the straight line. Choose a small half-disk on that side. Along a sufficiently short initial segment, take its FIRST hit of the semicircle, stopping before any remote intersection. The prefix is a continuous crosscut from v on the diameter to q on the semicircle; its interior is in the half-disk. Apply B to carry this prefix to the straight chord[v,q], fixing the diameter and hence the first two germs.

The residual original third-arc tail after q is compact and avoids v. After the ambient homeomorphism it still avoids v; a further small disk therefore excludes it, as well as all nonincident trace and remote pieces. The three retained germs are now three straight rays in that disk. This final shrink is justified by compact separation, not by asserting that the original arc crossed a metric circle only once. Pull back the disk to obtain the required labelled local star neighborhood. The same first construction already treats degree two (no third crosscut needed).

This supplies the constructive HAND route for degree-two and degree-three germs, including singleton blobs without an original cycle: the auxiliary cycle is furnished by actual continued arms. It does not invoke global polygonal redrawing and does not alter the original C.

## D. Remaining degree-one / global association obligation

A degree-one vertex has a unique outgoing dart, so its local rotation is forced. A full endpoint disk-normal-form theorem may be stronger than necessary. What is still needed for the source-facing face-orbit theorem is the actual nonseparating pendant-tip return: the two sides of its one incident edge belong to the same local face, with the correct original label visit. `arc_complement` proves global nonseparation of an isolated simple arc, but it does not by its statement give this LOCAL relative assertion in the presence of the rest of the drawing. A localization/slit argument must be supplied; do not promote global arc-complement connectivity to a local disk theorem without proof.

Likewise, the degree-two/three local charts must be assembled into coherent planar-orientation rotations whose dart successor orbits correspond to the actual complementary components. Refinement independence, one global orientation (not independent flips at vertices), and the unbounded-face selection remain explicit. Only after that supplier is established does the finite bridge-excursion proof give contiguity and actual cap-order compatibility.

## Exact source bindings

Public supplier pin05a43d29cde026618777db3d4e4316204ccca237. Exact retained source hashes are in INSPECTED-SOURCE-HASHES.json. Relevant conclusions were read, not inferred from names. `arc_complement_poly` is unconditional at JordanClosed.lean55; `closed_interior_extension` explicitly takes `SquareExtension`, discharged by JordanSchoenflies.lean; the supplied full-plane Jordan theorem extends only the prescribed boundary, not an unmentioned outside-fixing property.

Current source status: the auxiliary-loop part and its original-ID binding are published as UNCOMPILED candidate ab956dd97b41a7c9d2180c1f1b139b2f4083744a; its qualification is pending. The two-cell gluing and complete local star theorem are not part of that candidate.
