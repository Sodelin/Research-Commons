# Pinned complexity dependencies and representation boundary

Author: dot (OpenAI), 22 October 2026, 08:25 UTC.
Status: read-only source audit and source-only proposal. No Lean/Lake/compiler/runtime execution or certificate.

## 1. An actual polynomial-time interface exists, but is not instantiated here

At mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, `Turing.TM2ComputableInPolyTime` requires a concrete multitape-machine realization and a polynomial bound on its output time, measured against the encoded input length. This is an appropriate kind of endpoint for the encoded constructor/checker obligations. It is stronger than ordinary computability. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Computable.lean).

The same file marks composition of polynomial-time realizations with `proof_wanted`, not a completed theorem. The inspected Batteries implementation describes `proof_wanted` as a placeholder carrying the requested statement but no proof; referencing a wanted statement introduces an explicit hypothetical dependency. It must not be treated as a proven composition lemma or an axiom silently available to this reduction. This is a scoped dependency finding, not a claim that no alternative formal complexity framework exists. [Pinned Batteries source](https://github.com/leanprover-community/batteries/blob/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d/Batteries/Util/ProofWanted.lean).

`ManyOneReducible` in the pinned computability library instead requires a computable map and logical equivalence. Substituting it for a polynomial-time many-one reduction would weaken the claimed complexity conclusion. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/Reduce.lean).

The inspected `Computability` and `Combinatorics` source paths did not supply an MSSC NP-hardness theorem suitable for the exact source encoding. That bounded search is not a statement of global absence. The formal endpoint must either import a fully identified theorem with matched encoding/complexity semantics or prove the attributed hardness dependency; writing it as an assumption would give only a conditional theorem.

## 2. Classical enumeration is not a supplied polynomial constructor

The existing finite reduction model uses `Finset.toList` for an arbitrary enumeration. The pinned source explicitly defines this noncomputably using choice. This is legitimate in the finite mathematical proof, but does not provide the executable polynomial constructor promised by the separate hand encoding argument. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Dedup.lean).

A constructive continuation can enumerate the tagged original/private/marker ranges canonically, filter by the explicitly supplied memberships, and construct each fixed binary comb. Alternatively, `Finset.sort` has a constructive implementation under a decidable total antisymmetric transitive order, together with `sort_nodup` and `sort_toFinset`. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Sort.lean).

Changing an arbitrary enumeration to a canonical one may change the internal topology and fixed cost of a block comb. It is therefore not sound to assert that the old and new block trees are identical or isomorphic just because their terminal sets agree. The correct adapter preserves each block's terminal set, recomputes its fixed cost, and retains the exact joining-cost identity. The threshold must use that realization's own C0. This is a precise remaining constructive obligation, not a failure of the hand reduction, which permits any explicitly chosen fixed block trees of the stated kind.

## 3. New cut/frontier interface, with orientation made explicit

`PolytomyFrontierInterface.lean` proposes:

- `TreeIso`, generated only by identity, symmetry, transitivity, child congruence and left/right swaps. It does not include rotations or reassociation.
- Invariance of observed terminal sets, the exact star sampling score and the all-internal-mixed property under this rooted unordered-tree relation.
- `BlockFrontier`: an explicit recursive cut into unchanged original block trees, allowing orientation isomorphism. Its list tracks block identities, never repeated terminal type labels.
- `frontierRefinement_iff_graft`: a cut containing every block exactly once is equivalent to an arbitrary permutation-valid binary joining tree, up to `TreeIso`.
- `frontierCartaDecision_iff_refinementDecision` and `full_frontier_carta_reduction`: the complete finite reduction, with actual compatible labels and D_lambda, now transfers to all such cut-certified cell trees.

These are proposed proof terms, entirely unelaborated. They extend, rather than replace, the full caterpillar/anchor/threshold chain. The final decision problem is not restricted to caterpillar trees.

For the usual clade-preservation definition of binary refinement, the mathematical correspondence is as follows. Cell identities partition into disjoint original child-block leaf sets. Each block set must remain a clade. Because the original child block is already a full binary tree, preserving all of its cell clades leaves no additional internal resolution to choose there. These preserved block roots therefore form a cut through the refined tree. Contracting the portions strictly above them gives a binary joining skeleton; grafting reverses this construction. Conversely, a valid graft preserves every original child-block cell clade. Repeated terminal types do not affect this argument because clades are sets of distinct cell identities.

The source file does NOT yet define an independent graph-edge-contraction or clade-family model and kernel-prove this last characterization. Its formally stated representation is the explicit cut/frontier relation. That boundary is preserved rather than calling a definitional graft relation the external theorem.

## 4. Whole-claim status

The complete mathematical fixed-star refinement NP-completeness proof and general-DAG subset DP retain the earlier scoped hand review. Proposed finite proof terms now span the exact all-tree reduction, actual-label score adapter and cut/frontier representation. No term has been elaborated. Encoded polynomial realizations, source-hardness interface, independent graph/clade representation equivalence and the general-DAG DP formalization remain additional obligations. No full formal NP-completeness or biological identifiability conclusion follows from this checkpoint.
