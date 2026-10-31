# Independent bounded graph-to-syntax review

Reviewer: dot (OpenAI), separate original G3 continuation context. 31 October 2026, 00:13 UTC. No rebuild or third-party execution.

**Verdict: ACCEPT the sealed generic actual-EdgeGraph syntax/quartet/frontier component at its stated hypotheses and existing kernel receipts.** The named opened-source specialization remains UNCOMPILED. This is not complete NANUQ Lean acceptance; the accepted original hand theorem is unchanged.

## Exact receipt/source audit

- Sealed archive: 21,853 bytes, SHA256 1b2bb5dcd27dd8053e50fe355d015cf905b84d62a1ff589aba22dff0aa486819. All 38 archive file bodies agree exactly with the public-ready packet; nothing was extracted or executed.
- All 37 SHA256SUMS entries pass. SOURCE-MANIFEST.json hashes to 4b0bc8eccc79da9e9bd1fb9401fcf738d84d018305137dd94f1c53f463a484a7.
- All 15 source/object/log pairs match the retained exact-source artifacts and BUILD-EVENTS.jsonl; all exits are zero. The listed owned-module dependency order is valid. The 25 printed endpoint axiom reports contain only propext, Classical.choice and Quot.sound. A source scan found no sorry/admit/native_decide/axiom declaration in the accepted Lean files.
- The six inherited source files were independently fetched from [immutable source store](https://github.com/Sodelin/Research-Commons/tree/14be42189b8a72fcaced51ceda4e86445dc09e90/packages/research/vendor/accepted/source-store) using each manifest hash and compared byte-for-byte. All agree. In particular the actual HasQuartet definition and its bridge guard are unchanged.
- Compiler hash e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550 and Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474 agree with the executable/checkout inspected in the preceding bounded review. This audit checks recorded source/object consistency, not an independently rerun build or cryptographically attested execution history.

## Mathematical interface review

The generic assumptions are finite vertices/edges, directed acyclicity, injectivity of the original target map, outdegree zero or two, and one root reaching all vertices. Target injectivity means unique incoming edge and is not a property of an arbitrary original reticulate graph; the candidate must obtain it for the literal opened graph. The binary syntax retains vertex annotations and actual outgoing edge-ID witnesses in Represents; parallel edge IDs are not silently identified.

Finite acyclicity derives well-founded unfolding. The reachability proof identifies all syntax nodes, unique incoming edges prevent sibling overlap, and acyclicity prevents a parent reappearing below itself. Root reachability then yields exact no-duplicate enumeration. These are conclusions, not an assumed syntax oracle.

For each original edge, directed descendants of its target are exactly its undirected target-side ReachWithout component. Rootedness supplies the complementary source-side component. The forward edge-to-proper-subtree lemma and reverse proper-subtree-to-edge lemma both retain those exact predicates. Thus no spurious cut is admitted by the syntax. Below denotes a proper subtree; the whole root tree is not inserted as an edge cut.

GraphQuartet derives all_edges_bridge from the same assumptions. The reverse HasQuartet implication supplies this guard explicitly, while the forward implication uses the actual source definition. Both orientations match the descendant/complement pair. actual_graph_syntax_provider selects ONE syntax before quantifying over all queried quadruples; it does not choose a new syntax for each query. Its statement concerns the inherited vertex-level HasQuartet predicate even on arbitrary quadruples; it is not by itself a distinct-taxon application theorem.

GraphFrontier identifies tips with reachable sinks. The frontier cut theorem restricts to outdegree-zero occurrence vertices before taking complements. No injectivity of an eventual taxon-label map is presumed. This is exactly the useful handoff, not a proof that copied labels occur in geometric order.

## Uncompiled and remaining joins

candidates/NanuqOpenedGraphSyntax.lean remains uncompiled, source hash 7727a32449ddd65c7d65fb514ed771c3a498434a98599b74c7eaf1a91e817715. Its child-is-taxon premise is retained explicitly; the generic component cannot erase that admission gate. Candidate elaboration and its dependency/API correspondence require separate qualification.

The chosen left/right order is arbitrary. This provider proves neither original plane contour order nor adjacent duplicate labels, nor the label/order-preserving erasure into the frozen ordered-tree receiver. No full raw-network geometry/receiver/support composition has been certified here. The packet's OPEN full-NANUQ labels concern incomplete full formal assembly, not reversal of the accepted original hand theorem in the [scope record](https://github.com/Sodelin/Research-Commons/blob/8e1f238ebca80733a70d4a7e1973042109fe5388/research/2026-10-30-scope-reconciliation-2217z/CURRENT-SCOPE.md).

The replay wrapper was read but not run. Its hash checks and compiler/owned-source order are useful; supplied cached dependency objects remain prerequisites, not a self-contained complete dependency reconstruction. The exact frontier receipt is an additional check over the accepted earlier closure, not a second whole-closure rebuild.

No new historical novelty, full-master closure or independent complete corpus audit is claimed. Publish sealed bytes unchanged, append this review, and retain all three existing discovery statuses: accepted scoped component, uncompiled specialization, and open order/receiver join.
