# Original C: finite bridge excursions and the exact geometric supplier

Status: hand-level reduction and supplier assessment, NOT a new Lean theorem. The original manuscript hand theorem remains recorded as proved; this note locates a missing formal transport without changing that theorem. The frozen cap exterior candidate8d372090 has since been qualified after proof-only repairs atf335bfe68f73788cbed9a76838d2ddd2fc407862. That scoped exterior-incidence result does not supply the missing order premise.

## 1. What “induced by this embedding” must mean

Manuscript §3 fixes the original outer-labelled embedding and its induced cyclic taxon order C. Section5/A.4 explicitly uses its outer-face traversal. The faithful `PlanarCurves` and `TaxonOuterFace` records contain point/arc incidence and unbounded-face incidence, but no such traversal. C cannot be an arbitrary permutation added to these records.

Use darts `(original edge ID, orientation)`, with reversal alpha. The positive planar orientation induces a cyclic permutation sigma_v of the outgoing original darts at each vertex. The geometric face successor is phi(d)=sigma_(head d)(alpha(d)), with the opposite convention giving the reversed orientation. A face boundary is an orbit of phi. The desired C is the cyclic sequence of labelled degree-one visits on the orbit belonging to the actual unbounded component, modulo rotation and reversal.

This is a transparent description of the original premise, not permission to choose arbitrary sigma. A formal provider must derive the local rotations and their face-orbit interpretation from the SAME continuous drawing. It must prove that the unbounded component of this connected graph has the one boundary orbit used here and that each outer taxon occurs there. The source graph is connected and has no isolated vertices. Bridges use two distinct darts and can occur twice in the same facial walk; parallel edges retain their distinct IDs.

## 2. Exact finite bridge-excursion argument

Assume the genuine geometric outer orbit W has been supplied, and let e be any original bridge. Delete e, obtaining vertex sides A,B. All other original edges have both ends in a single side. Name the two darts e_AB and e_BA.

For any dart d other than these two, tail(phi(d))=head(d) lies on the same side as tail(d). For e_AB, this side changes A to B; for e_BA it changes B to A. Because W is a finite permutation orbit, it uses any particular dart at most once.

Both bridge sides contain taxa by the original rooted-LSA supplier. All taxa occur on W. Hence W has visits on both sides and must contain both crossing darts. Starting immediately after e_AB and stopping at e_BA gives ONE interval of W whose dart tails lie in B. The complementary interval has all tails in A. There is no extra entry/exit: another crossing would repeat one of the same two darts. In particular every taxon in B, and no taxon in A, is read in that interval.

This proves simultaneously:
- both bridge darts occur on the outer boundary (old-global-frontier incidence at the combinatorial level);
- each bridge taxon side is a cyclic interval of the ORIGINAL C;
- wraparound is harmless: start W at either bridge dart, then take its cyclic equivalence class.

Thus after the genuine geometric orbit exists, neither the old-frontier separating-cycle hand route nor a new exterior-incidence premise is needed to prove bridge-fibre contiguity. This is not a claim that the orbit provider has been formalized.

## 3. Collapse to the actual cap port order

For a fixed original nonleaf blob b, its actual portTaxa fibres are exactly the far sides of its incident original bridges (`GraphPortFibers`), are nonempty (`blobProjection_surjective`), and partition X. Applying §2 gives disjoint nonempty cyclic taxon blocks. Replace each block by its port label p. This defines the collapsed order C_b, including the block crossing an arbitrary chosen index-zero cut.

The stronger required statement is that C_b is the order induced by the LITERAL cap drawing, not merely some convenient port permutation. At the dart level, cap surgery replaces the one outer excursion into each far component by the excursion along the retained bridge prefix to its new degree-one port and back. The local permutation at the original inner endpoint is unchanged because the SAME edge germ is retained. The incoming cap additionally inserts its fresh degree-two root at parameter2/3 along the retained undirected path from inner endpoint to port tip1/3. Degree-two subdivision does not alter any cyclic tip order. It must not be mistaken for a second outer excursion or a new branch.

Deleting the far excursion and inserting the pendant excursion leaves the remaining cyclic word unchanged. Consequently its port-label sequence is exactly C_b, up to the SAME global orientation convention. A circular local port split then lifts to a union of consecutive global blocks, hence a C-circular global split.

Small cases are not discarded: for a singleton blob the original incident dart rotation itself supplies the port cyclic order; its bridges remain distinct. Two-port cyclic order has its usual rotation/reversal degeneracy. For a two-vertex bigon the two original parallel IDs remain different darts; no simple-graph reduction or >=3 IsTwoConnected shortcut is used. The permutation argument itself does not require a nontrivial blob or a cycle boundary.

## 4. Minimal local topological lemma needed

Here is a precise sufficient local supplier, not an added input assumption.

Let k in{1,2,3}, let gamma_i:[0,1]→R² be continuous injections with common gamma_i(0)=v and pairwise intersecting images only at v. Let K be compact, v notin K. For every open neighborhood U of v there must exist a topological closed disk Delta with v in its interior, Delta subset U, Delta disjoint K, and parameters t_i in(0,1), such that

Delta ∩ image(gamma_i) = gamma_i([0,t_i]),
frontier(Delta) ∩ image(gamma_i) = {gamma_i(t_i)},

and the disk with these k initial arms is homeomorphic, preserving each arm ID and v, to a standard k-spoke disk. This may equivalently be supplied by a local ambient chart taking the actual initial arms to radial spokes and excluding all remaining trace. The circle order of the k exit points defines sigma_v using one fixed orientation of the ambient plane. Independent reversal at individual vertices is NOT allowed; choosing an oppositely oriented chart must reverse its chart coordinate convention as well. Reversing the one ambient orientation reverses the final C globally, as permitted by the original theorem.

Why the original drawing fits: at each original vertex, orient each incident original arc outward, truncate before its other endpoint, and place all nonincident arc images, other vertex points, and the compact residual tails in K. Faithful incidence and point injectivity make K avoid v; the chosen initial germs meet only at v. Binary degrees give k<=3; original admission excludes k=0 and loops. For parallel arcs, sufficiently short initial pieces near one endpoint do not meet their common other endpoint, so they remain separate germs. No straight-edge or differentiability premise is used.

The supplier must also prove refinement independence of the resulting cyclic order, and that small sectors glue along original arcs to precisely the actual complementary components. A local chart alone does not yet prove the global face-orbit theorem. Choosing an ordinary Euclidean radius that each continuous arc meets only once is NOT justified: an injective arc can re-enter every small metric circle.

## 5. Actual retained tools and exact remaining gap

Pinned public supplier alonamaloh/schoenflies-lean at05a43d29cde026618777db3d4e4316204ccca237:
- `Schoenflies.arc_complement` (JordanClosed.lean50) proves complement connectivity for every continuous simple arc, with no residual SquaresTwoConnected assumption.
- `arc_complement_poly` (line55) joins two points OFF that arc by a polygonal arc. It does not supply accessibility of arbitrary arc endpoints.
- `jordan_curve_theorem` and prescribed `jordan_schoenflies` provide actual continuous Jordan separation and boundary-homeomorphism extension.
- `AccessibleJoin.exists_simple_arc_of_polyAccessible` requires polygonal accessibility at its endpoints. It cannot silently be applied to arbitrary continuous endpoints.
- Accepted own continuous region crosscut and prescribed two-arc straightening preserve the original drawing sets; neither is a general arbitrary vertex-star normal-form theorem.
- `Graph.unbounded_face_unique` identifies the actual unbounded component, not a boundary dart orbit.
- `HasFaceCycles`/`IsFaceCycle.frontier_eq` give cycle boundaries for finite two-connected drawings, not bridge-repeated walks of the full connected graph.

A plausible source-specific route for nontrivial-blob vertices is to straighten an actual incident cycle, then use a boundary-fixed crosscut straightening on the side containing a third germ. Such a boundary-fixed construction can be sought by gluing two prescribed Jordan-domain maps, but it is not presently a proved supplier. The subsequent CONTINUED-ARM-STAR-CONSTRUCTION note gives a constructive auxiliary-cycle route also for degree-two/three singleton or bridge-only vertices, without assuming an original cycle. Its full local normal-form gluing is not yet formalized, and degree-one local return is still separate. Neither arbitrary polygonal redrawing nor a generic Jordan curve name proves this relative statement.

Accordingly the next topology target is the labelled finite-star local normal form plus its sector/face gluing, with SAME-embedding compatibility. The finite bridge-excursion and literal cap-splice proofs above can then consume its actual output. The cap exterior join is now scoped verified; no order or contour consumer is claimed accepted from it.

### Redrawing API check (not an order supplier)

`Graph.polygonal_redrawing` at Graph/Redrawing.lean424 concludes only existence of an `IsDrawing G redrawing` with polygonal edge carriers. Its body uses `exists_vertexSquares` and `exists_core`. `exists_vertexSquares` excludes OTHER vertices and NONINCIDENT arcs from each square; it does not say each incident arc meets the square boundary once. The core is cut after a LAST visit to the near square and before a FIRST visit to the far square. Thus a core's singleton contact with a square is not a theorem that the discarded original germ stayed inside that square. The returned theorem has no ambient homeomorphism, original rotation, face, or C-preservation clause. These missing conclusions cannot be inferred from “same graph and same vertices.” This confirms why the local relative-germ supplier above remains a genuine obligation.
