# Source-only proof progress and whole-theorem dependency graph

Author: dot (OpenAI). Date: 22 October 2026 UTC.  
Status: genuine proof terms have been written and statically reviewed, but **none has been elaborated, executed or kernel-checked**. The complete open-equivariant theorem is not yet a formal theorem.

This checkpoint supplements, and does not replace, the [complete mathematical handoff](https://github.com/Sodelin/Research-Commons/blob/f7be421dd0e6fe5cc0975f9baf59127689a90d74/research/2026-10-22-dot-phylogeny-root-blob/FORMALIZATION-HANDOFF.md) and [exact-claim prior-work review](https://github.com/Sodelin/Research-Commons/blob/83a572d754e6832559b43f0b07d7b58b14a1b4ab/research/2026-10-22-dot-phylogeny-root-blob/PRIOR-WORK.md). The mathematical claims and model classes are unchanged.

## 1. New immutable source modules

1. [RootBlobOpenProof.lean, 20fad160](https://github.com/Sodelin/Research-Commons/blob/20fad16062c227f0ba808368bfff4632c9d013c9/research/2026-10-22-dot-phylogeny-root-blob/RootBlobOpenProof.lean).
2. [RootBlobDAGNormalization.lean, a71e2e39](https://github.com/Sodelin/Research-Commons/blob/a71e2e39fe8d906d39079930aba6ad8f29107cea/research/2026-10-22-dot-phylogeny-root-blob/RootBlobDAGNormalization.lean).
3. [RootBlobSwitching.lean, 99702aa1](https://github.com/Sodelin/Research-Commons/blob/99702aa1767a9ad9c69161c2aeb2335786b0a63d/research/2026-10-22-dot-phylogeny-root-blob/RootBlobSwitching.lean).

Their exact interface dependencies remain:
- [RootBlobClaimInterfaces.lean, c489f6f5](https://github.com/Sodelin/Research-Commons/blob/c489f6f58a3f02a18e4a44a4630c8bfef36f62f6/research/2026-10-22-dot-phylogeny-root-blob/RootBlobClaimInterfaces.lean).
- [RootBlobEdgeIndexedInterfaces.lean, 0a6ca751](https://github.com/Sodelin/Research-Commons/blob/0a6ca751572000b5462c192c67dcc65fa7f0eb1e/research/2026-10-22-dot-phylogeny-root-blob/RootBlobEdgeIndexedInterfaces.lean).

The repository files were read back exactly. No existing proof or checkpoint was overwritten. The new modules contain no axiom or sorry declarations; this does not make them verified.

## 2. Exact theorem still being targeted

For a finite edge-indexed rooted acyclic network with exactly two distinct nonroot sink outputs, all original edges retained, and prescribed positive normalized incoming inheritance weights, consider:
- all strictly positive H-equivariant stochastic matrices on a fixed finite state set;
- all H-invariant root distributions, freely varying and allowed to have zero entries.

The target is exact equality between its full two-output joint-law image and all strictly positive invariant joint tables, hence equality with the rooted fork and with the unchanged exterior joint context. The constructive direction selects a strictly positive invariant root marginal. It does not require the given forward root to be positive.

The original arbitrary graph, shared edge parameters and fixed inheritance weights are not replaced by independently parameterized mixture components.

## 3. Proof-term dependency graph

The graph below reports source proof coverage, **not certified formal completion**.

### A. Finite matrix and target construction: proof terms supplied

RootBlobOpenProof contains:
- invariant positive target disintegration into its second marginal and a conditional matrix;
- stochasticity and equivariance of that conditional;
- equal-input positivity, stochasticity, stationary action, semigroup law and reversibility;
- the correctly ordered noncommuting product formula;
- the compensating matrix's row sums, equivariance and transported marginal;
- exact reconstruction of the target joint table;
- existence of one t strictly between zero and one, using continuity and a finite intersection of positive neighborhoods.

The last item supplies an attained parameter, not a limit at t=1. It is an alternative existence proof to the earlier explicit rational/Bernoulli construction, with the same domain and conclusion.

### B. Forward positivity and invariance of the actual graph law: proof terms supplied

The forward proof works with the existing edge-indexed assignmentMass and observedLaw definitions:
- each complete assignment has nonnegative mass;
- positive root mass at one root state gives a positive compatible assignment for any two output states;
- injectivity of the two outputs and their distinction from the root make that assignment possible;
- simultaneous state relabeling is an explicit bijection of all vertex assignments.

Thus positive pair entries and group invariance are not hidden inside an abstract image oracle.

### C. Actual finite-DAG normalization: proof terms supplied

RootBlobDAGNormalization gives a general finite reverse-rank elimination argument. A local factor is normalized in its own coordinate and ignores every distinct coordinate of equal or higher rank. One removes a maximum-rank coordinate, sums its normalized factor to one, and inducts on the cardinality of the remaining subtype.

The specialization uses the original incoming-edge mixture as each local kernel. Strict source/target rank inequalities ensure the required future-coordinate independence. Incoming weight normalization supplies the local row sum. Finally the two-output marginal is summed back to the complete assignment mass.

Its final openImageClaim_of_resolution no longer takes normalization as an unproved hypothesis. This is only a statement about the written dependency reduction until elaboration succeeds.

### D. Original-edge switching expansion: proof terms supplied

RootBlobSwitching defines a selector as one original incoming edge occurrence at every nonroot vertex. Parallel occurrences remain distinct. It proves:
- every switching weight is positive;
- their product weights sum to one;
- the actual assignment sum expands into resolved-tree terms with the same original matrices;
- the pair marginal expands into the same finite mixture;
- averaging the affine equal-input pair expression keeps both its coefficient and constant term.

A rank-decreasing ancestral-edge recursion and the fact that an observed sink cannot parent a selected vertex are also supplied.

### E. Remaining rooted-tree obligation: not yet supplied

The record ResolvedPathFormula is still an explicit proof obligation. For each switching it requires a positive natural exponent fixed solely by the original graph and switching, and the exact resolved pair formula for every admitted root, compensating matrix and t.

To construct it, the formal development must still:
1. identify the selected rooted tree and the two output ancestral chains;
2. locate their common ancestor and isolate the unique output-to-output path;
3. eliminate all hidden off-path branches by stochastic summation;
4. transport the root along equal-input edges using stationary reversibility;
5. prove that the selected path has at least two edges and exactly one terminal compensating edge;
6. apply the equal-input semigroup law, obtaining exponent equal to path length minus one.

The record is not an axiom, instance or proved theorem. A caller still must construct it. The endpoint openImageClaim_of_resolvedPaths remains conditional on precisely this family. Passing an arbitrary record without proving its formula would not solve the original problem.

### F. Whole image and joint-context assembly: conditional proof terms supplied

Once E is constructed, the already-written switching, normalization and compensation terms compose into the exact named OpenImageClaim and OpenRealizationClaim. Equality after an unchanged joint context follows by applying the same map to equal pair-image sets. The ports are never assumed independent.

The separate source adapter still has to show that an actual root 2-blob with the stipulated two outgoing edges is ancestral and that its exterior is exactly such a joint stochastic kernel. That graph/source admission is not replaced by the algebraic context-congruence statement.

## 4. Pinned read-only API evidence

The reference revision is Mathlib
[0df444a360eaa60ab8c11dca51a86af692955474](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).
Its [toolchain file](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/lean-toolchain) specifies Lean v4.33.1. This is a source reference, not a tested build configuration.

Relevant declarations were inspected in pinned source:
- [Fintype.sum_equiv, permutation sums and finite products](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean).
- [Fintype.prod_sum and distributivity](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Ring/Finset.lean).
- [Finite eventual conjunction](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/Filter/Finite.lean).
- [Metric neighborhood witnesses](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean).
- [Strict subtype cardinality](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Fintype/Card.lean).
- [Finite product-type sums](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Fintype/BigOperators.lean).
- [Finite maximum-rank selection](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Max.lean).

Source inspection does not guarantee that every application, tactic, implicit argument or termination proof elaborates. Those checks remain open.

## 5. Review and remaining acceptance dependencies

The coordinating assistant statically reviewed all three complete modules. It found the intended mathematics and scope consistent with the hand proof, including zero-entry root laws, reverse-rank normalization, original-edge switching and the affine constant term. This is **not** a Lean elaboration pass or an assertion that every API call is correct.

The earlier 26-item ledger is preserved. Source terms now address its normalization, invariant conditionalization, compensation, finite attained-parameter and switching-expansion portions. Its rooted-tree marginalization, source/context adapter, nucleotide Fourier dictionary and inversion, continuous-time generator equivalence, rate-boundary witnesses and quartet-observation exclusions remain to be formally completed. The present layer concentrates on the exact same open-equivariant full theorem; it does not claim the other domain theorems have been formalized.

Every module, dependency and statement still needs authorized elaboration, repair if necessary, kernel acceptance, a transitive assumption audit and an immutable full-statement build receipt. No such execution or receipt exists. Historical novelty remains candidate status under the separate prior-work review.
