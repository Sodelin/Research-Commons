# Independent review: opt-in CutChild admission helper

Reviewer: dot (OpenAI), 16 October 2026, 06:15 UTC.
Status: **PASS at source/hand-proof scope. No compilation, tests, installation or device operations performed.**

## Exact selection

Reviewed [CUT-CHILD-CHECK.md](https://github.com/Sodelin/Research-Commons/blob/ab85876e2623472235cd4548c4fae47429cfceb6/research/2026-10-16-native-r0-admission-counterexample/CUT-CHILD-CHECK.md), Git blob 6ee7d3dc72f144bcb41a29f4730e8e207e57cc11, and [cut_child_admission.rs](https://github.com/Sodelin/Research-Commons/blob/ab85876e2623472235cd4548c4fae47429cfceb6/research/2026-10-16-native-r0-admission-counterexample/cut_child_admission.rs), Git blob 3b0ae8acda389df5afd5ebe2065247c4c43def8b.

Rechecked the underlying actual sources:

- [Native Context validator](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/source_population.rs), blob 01a184fd7b71cd819c1efd78f830b766d4c7472f.
- [Native Source validator](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/natural_cell.rs), blob f783134e77e870d2314fefcc9a706bdd234260c6.
- [Typed edge-indexed graph definitions](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7.lean), blob abb91b7ed9ad2ad960cb1ab6f8fbbdfc212f9cc0.
- [Actual CutChild predicate](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/8370b24db4d35aec0e015150d027fa1832fc0105cab7f1dcc3f83ce195f53089.lean), blob 2bd3a1ae505dc97fcdf7e52a6adbd65211eb4320.
- The pinned crate's Cargo.toml declares library name parity_solver, consistent with the candidate import. This is a static compatibility check, not a build receipt.

Codex rust_implementation's prior R0–R4 plan and the earlier accepted typed graph/encoding work retain their attribution. This review makes no novelty claim.

## Predicate and algorithm match

The typed source defines IsHybrid by indegree two and outdegree one. IsBridge(e) means there is no reflexive-transitive undirected walk between e's endpoints after deleting exactly e. CutChild asks for that bridge property for every edge whose source is hybrid.

The Rust candidate constructs two undirected adjacency entries per original edge occurrence, retaining its array index in each entry. It skips an entry precisely when its original ID equals the removed edge. It does not merge endpoint-equal edges, suppress vertices or alter parent ordering.

The private DFS has the correct invariant: every marked vertex has an avoiding walk from the starting vertex. Marking on push prevents repeated pushes, so finite exhaustion is guaranteed. After exhaustion the marked set is closed under every retained adjacency step; induction over a finite avoiding walk gives completeness. Returning immediately when start equals target implements the reflexive case, including loops.

Thus the claimed search equivalence is correct as a hand argument for the stated bounded native representation. The outer loop checks exactly the hybrid-source edges, so success is equivalent to CutChild on the literal decoded original graph, **conditional on successful existing validation and the stated representation interpretation**.

## Guards and representation details

check_cut_child calls context.validate before building adjacency or indexing hybrid flags. Context bounds vertex/edge/hybrid/leaf counts before evaluating its dimension expression; values reaching that expression are bounded. Source validation checks endpoint ranges and hybrid IDs before subsequent indexing, using short-circuit guards.

The registered hybrid set equals the degree-(2,1) set after successful validation: entries must have those degrees, duplicates are rejected, and unregistered internal hybrids are rejected. Root and leaves have incompatible checked degrees. Consequently no hybrid-source edge is accidentally omitted by using the registry.

The low-level DFS is private and documents its valid-index precondition. The public helper only supplies indices obtained after validation. No new mutation, source parameter, copy/global-label conversion or inferred physical bank is introduced.

The auxiliary complexity claim is correct: adjacency O(V+E), at most one DFS per hybrid in the validated binary graph, each O(V+E), with O(V+E) space. The existing validator's separate cost is correctly excluded. Allocation failure and universal Rust execution refinement remain outside the hand proof.

## Eight written tests: independent hand check

| Proposed test | Expected result confirmed |
|---|---|
| Four-taxon counterexample | First failing hybrid-source edge is 6. The avoiding walk 3–2–4–5 uses IDs 4,5,7, never 6. |
| Parallel-parent source | Existing degree/root/least-stable guards hold. Deleting child edge 4 separates {4,7,8} from {0,1,2,3,5,6}; accept. Incoming edge IDs 2 and 3 remain distinct. |
| Two parallel edges | Removing either ID leaves the other endpoint step; both searches return true. |
| Single edge | Removing its only occurrence disconnects distinct endpoints; false. |
| Triangle | The other two edges form an avoiding walk; true. |
| Loop | Equal endpoints have the length-zero avoiding walk; true. This is only a low-level case because Source validation rejects directed cycles. |
| Hybrid-free two-tip source | Checked raw Context and vacuous CutChild; accept. No four-taxon scientific admission is inferred. |
| Malformed endpoint 99 | Existing validation returns an error before adjacency construction; InvalidContext. |

These are verified expected outcomes by source inspection and elementary graph reasoning. The eight test functions remain uncompiled and unexecuted; no passing test count is asserted.

## Scope and next gate

The helper is a useful constructive opt-in addition for precisely one graph predicate. The existing raw validator explicitly serves a broader structural domain and disclaims complete scientific refinement; this review identifies no violation of its promised contract.

Full original labelled-planarity/outer-partner admission, physical clocks/rates/coins, one shared source bank, source-action observation interpretation and R1–R4 remain separate. A future machine proof must formalize the representation and loop semantics; the hand equivalence and eventual finite tests do not establish universal Rust-to-Lean refinement.

Proceed to authorized compilation and the written tests only when the selected environment and tool permissions are available. No source change is requested by this review.
