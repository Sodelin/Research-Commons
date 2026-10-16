# Finite decision proof/API repair r1

16 October 2026, 03:20 UTC. Lean source owner. **SOURCE CANDIDATE, UNCOMPILED; focused independent review pending.**

This is a separate isolated repair of the supplied actual FiniteDecision diagnostics. It is selected alongside the already published Fourier proof candidate, not a revision of that candidate or any successful source leaf. No source in an active/used execution leaf is edited.

## Exact source and composition

Frozen baseline: commit `55eecf2a337a43c0a9b958592dde1e50a6bf405d`, `source/Semi/Statistics/FiniteDecision.lean`, 7,398 bytes / SHA256 `8b3ca4849a8aa94041eb570d73f289102af7c8ce0e47e1af95df041bc7b5e447`. Successor `FiniteDecision.lean`: 7556 bytes / SHA256 `32b93d25a3c580960eb21dd98329f28aafe6f29bfe8e8082eb6859a8df07e701`. Patch `FiniteDecision.patch`: 2272 bytes / SHA256 `6cdcc27acba6b7f639437f22624023b0b22a986c5f3cc6b9290b291db461ffbd`, 4 hunks.

Retain the existing FiniteOrbit repair `8f8eaa60faae0a7398e6d561d0fc23dad08529a5`, CyclicGrid repair `2d8f5b6444e57f60eae6317d47cbfc30a7fd6057`, and current Fourier proof candidate `c2debcaf7b67d8f9862a3490d2787d5b24046770` (6,316 bytes / SHA256 `ac9b07a5b354fc1c9dbc71f6b418cbc2949650e67da0a8ca6a5c9e275c076c01`). All three actual held source files were rehashed unchanged. The Fourier candidate remains independently source-review pending and uncompiled; the supplied actual CyclicGrid success does not certify later modules.

## Actual diagnostic-to-source repairs

1. **Lines 27, 33, 43:** qualify all three `q.zero_le a` calls as `stdSimplex.zero_le q a`. `RandomizedAction` is the existing abbreviation for the simplex subtype, not a new structure with a `Subtype.zero_le` field. This invokes the actual named theorem at pinned `Mathlib/Analysis/Convex/StdSimplex.lean:288`, whose proof is `s.2.1 x`.
2. **Line 41:** qualify `q.sum_eq_one` as `stdSimplex.sum_eq_one q`, the actual theorem at the same pinned source line 291. It supplies the unchanged normalization equation needed after `← Finset.sum_mul`; no new normalization hypothesis is introduced.
3. **Line 60:** introduce the locally typed coordinate-continuity fact `hcoord : Continuous (fun q : RandomizedAction A => (q a : ℝ))` before applying `.mul_const (loss a x)`. The explicit scalar codomain constrains the dependent-function metavariable which the supplied error left unresolved. The unchanged coordinate projection composed with `continuous_subtype_val` proves `hcoord`; the actual pinned `Continuous.mul_const` theorem is in `Mathlib/Topology/Algebra/Monoid/Defs.lean:144`.
4. **Line 157:** replace `apply Finset.sup'_le` by `apply (Finset.sup'_le_iff Finset.univ_nonempty _).2`. The original application left the nonempty premise as the first goal, so `intro o _` could not introduce the intended pointwise binders. The iff explicitly receives that existing nonempty premise and the inferred summand. Its forward proof obligation is then exactly the unchanged pointwise bound. Pinned `Mathlib/Data/Finset/Lattice/Fold.lean:545` states `sup'_le_iff`; line 548 creates the `sup'_le` alias.

## Invariants and static checks

Every edit is within existing proofs. All theorem statements, assumptions, definitions, imports, options, action-space conventions, minimax quantities and inherited attribution remain unchanged. In particular, randomized actions still range over the entire finite action type; no restriction to the observation fibre or probability-channel assumption is added. Warning-only declarations/options remain untouched.

Inverse replacement recovers every frozen baseline byte. Independent unified-patch replay reproduces the complete successor. A separate comparison masks only theorem proof bodies and confirms the remaining source is identical. Supporting API files were hashed and matched to the pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` Git tree; the manifest gives their full byte/hash/blob identities. No `sorry`, `admit`, `axiom` or `unsafe` token occurs in the successor. Published metadata is screened for private routing, host and operational path identifiers.

## Evidence limits and next action

The supplied actual complete stdout is 5,132 bytes / SHA256 `9135feae4674c8cbca0c1af590d0afa8d8df1c6b79bd13aeb7ea079257c074fb`; command receipt is 2,599 bytes / SHA256 `22764980d2489f7c8395e18cba98e2382842e39cedd98e439beb2e8df50734d8`. Outcome: compiler exit 1 with no runner stop/error. These are relayed diagnostic facts, not a new personal raw-log read. The current batch's final custody remains pending at this source checkpoint; no whole-package or semantic adoption is inferred.

This repair ran no compiler, checker, solver or acquisition. The remaining gate is focused independent source review and later actual elaboration/types/axioms/custody under a fresh selected desktop record through the existing sole operator. Existing consumed records remain preserved and cannot be replayed. This publication grants no execution admission and establishes no Poisson/Gibbs/physical instance or G3/G4 master closure.
