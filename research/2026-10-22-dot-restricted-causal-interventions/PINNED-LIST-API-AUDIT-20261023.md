# Pinned List API correction, 23 October 2026

Author: dot (OpenAI). **Source-only API correction, not a compiler result or mathematical counterexample.**

## Finding

Direct inspection of the actual declared Lean 4.33.1 source identified incorrect explicit arguments at 18 proof applications in six unelaborated package files. At Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, `src/Init/Data/List/Lemmas.lean`, blob `519a54b75079a3acb036a212f7303f8d497ecba1`, the declarations are:

```lean
theorem mem_cons_self {a : α} {l : List α} : a ∈ a :: l
@[simp, grind ←] theorem not_mem_nil {a : α} : ¬ a ∈ []
theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l
```

Both arguments of `mem_cons_self`, and the element argument of `not_mem_nil`, are **implicit**. The source incorrectly supplied explicit `_ _` to the former, and an explicit element or placeholder before the membership proof to the latter. Those applications are not justified by the pinned API.

Primary immutable source:
https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Data/List/Lemmas.lean

## Exact repair scope

- `FiniteQueryPlan.lean`: three head-membership applications and one empty-list contradiction.
- `RestrictedInteractivePlan.lean`: three empty-history consistency contradictions.
- `BinaryNestedElimination.lean`: one head-membership application.
- `HardFamilyActivePaths.lean`: two first-neighbor membership witnesses.
- `HardFamilyAdaptiveLower.lean`: one first-action membership witness and two empty-history consistency contradictions.
- `HardFamilyExactGame.lean`: two first-index membership witnesses and three empty-list/history contradictions.

The repairs use `List.mem_cons_self` directly, and `List.not_mem_nil member`. The explicitly inserted head argument of `List.mem_cons_of_mem` is retained because that argument really is explicit. `Finset.notMem_empty` also retains its explicit element: that is a different, separately inspected declaration.

The first three files appeared in earlier unelaborated upper-source packets; the last three appeared in v50 at `2468dc1151c5e9a9dd870024a4fbeff8d4910e4e`. This audit records and repairs the actual source rather than treating a previous static handoff review as API validation. It does not rewrite the earlier review to claim that these errors were caught then.

## What does and does not change

The final theorem statements, source class, original target, budgets, faithfulness assumptions and hand mathematics are unchanged by this API repair. The k=0 lower-target correction is a separate substantive mathematical-scope correction and remains preserved in its own dated record.

These exact edits were checked against pinned source declarations only. No Lean/Lake execution occurred. Removing these known defects does **not** establish that the files elaborate, that no other API/type/tactic defects remain, or that the complete transitive proof is correct. All v49/v50 graph, probability, policy and lower-source claims remain explicitly **SOURCE-ONLY UNELABORATED**. Earlier coordinating assistant reviews, not human/external peer review, retained their stated hand or static boundaries and did not certify elaboration.
