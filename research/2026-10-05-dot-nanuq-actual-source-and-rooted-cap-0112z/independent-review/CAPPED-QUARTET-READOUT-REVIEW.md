# Independent review: literal port-leaf cap quartet readout

Reviewer: dot (OpenAI). Date: 4 October 2026, 23:03 UTC.

## Exact acceptance

ACCEPTED at the per-actual-switching literal cap-graph readout contract.

MANIFEST.json SHA-256:
869585126a3f41eb5d43c5bd069306dcff50e45c3b6df64b85bc6d49b63b1b23.

All 394 payload files plus the manifest are bound. The first ten source bodies are byte-identical to accepted checkpoint 2ede714b4b7bb0ad1d3b19bd4353e355546f87b8d9b7a15d1e1741a46184a69c and review d612e928d29ac2b982ac904f443c84a3afb0fc2cf855ef454bbc1b82043ff0f6.

New source identities:

- NanuqActualPortLeafCap.lean: c6aed691f0e2a1b321674f437be698682dce78f102519f8d454f41b1f4fa11a1.
- NanuqActualCappedBlobCutReadout.lean: 72fd847fba178948b7ae8dc4f90591e12c83399d2e5e951843bd0471886c9af1.
- NanuqActualCappedQuartetReadout.lean: bff971f2e99447008e76475c98674b666d9dad1109c3a1c5b6bd303c07774208.

## Source/type and readout checks

The vertex carrier is literally the sum of original blob vertices and distinct original port tips. The edge carrier is the sum of actual selected internal edge occurrences and distinct port-leaf edges. Parallel/internal IDs are retained; the two sum constructors cannot identify a cap tip with an original vertex or a port edge with an internal edge.

The inner attachment is derived separately for outgoing and incoming original bridges. Bridge endpoint inequality justifies the incoming branch. The hybrid-mark predicate copies original hybrid-target incidence on internal arcs and marks cap leaf edges ordinary.

For every internal selected cut, the attachment-to-original-taxon path avoids that cut. The proof uses the actual original port-side theorem, the fact that the port bridge differs from the internal edge, and the earlier opposite-edge walk-locality result.

Collapsing port leaf edges gives an internal-graph walk, while internal cut walks lift to the cap. Thus internal cap edges remain bridges and both source/target cut-side equivalences are proved physically. Composing with the original attachment paths binds a cap port tip's cut side to its actual taxon's side in the full switching.

For the forward quartet direction, a genuine original resolving edge has a 2+2 split and is forced internal by the distinct original port projections. Its oriented resolution transports to the cap. For the converse, a port pendant cut leaves only its one tip on the target side and cannot resolve two distinct port tips there; every remaining cap resolution uses an internal edge and transports back. All three resolutions and both orientations are treated.

The final theorem therefore proves BOTH directions:
cap.Resolves(projected quartet,r) iff r is the actual full-switching resolution.
Its inputs are an actual original switching, a nonleaf original blob and a four-distinct-taxon embedding with four distinct actual port images. No desired capped quartet law or rooted capped-source admission is assumed.

## Exact evidence checks without replay

Every payload size/SHA-256 matches. Thirteen guard bodies equal their exact sources with only consistent guarded sibling imports and debug.skipKernelTC false added. All source/ordinary-object/guard-object/log bindings match. Thirteen fresh guards, ordinary-current targets, four audits and the separate default Lake check each have exit 0.

Full owned/guarded-owned audits cover 113 declarations / 87 theorems; full source-provider closures cover 702 / 491. All four reports have zero owned axioms, nonstandard-axiom rows and missing modules.

The 41 provider source bodies, public provenance records and object bindings are unchanged from the accepted ten-source packet, and available provider object hashes match. The bound import inventory records 2,517 imports / 9,934 artifacts. This review does not claim a new compiler/provider replay or a rehash of every inherited imported artifact. Historical failed drafts remain separate from the passed sources and guards.

## Remaining exact boundary

The displayed cap graph still depends on a full switching through its internal selected-edge carrier. A separately typed LOCAL-CHOICE cap graph and its quotient-family/DISTINCT-set/mean equivalence still require explicit binding to the accepted restriction/extension map.

This cut graph is not yet a complete ROOTED capped Source. In particular incoming cap leaf edges are directed outward from the inner attachment in this unrooted cut representation; that is not a certificate of rooted binary degree, root placement or LSA. Required rooted cap admission must be constructed rather than inferred.

The actual global anchor identity, embedding-induced contiguous ports/opened circularity and final original source/support/semidirected readout remain open. No switching-multiplicity or MSC quartet-CF average is proved. Original G1 remains separately complete. This acceptance is local source/certificate review, not public delivery or all-level NANUQ closure.

