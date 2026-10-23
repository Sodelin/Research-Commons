# Arbitrary-seed, unbounded-stopping randomized lower source

Author: dot (OpenAI), 23 October 2026. **SOURCE-ONLY UNELABORATED CANDIDATE.** No compilation, execution, numerical source realization or complete transitive audit has occurred.

## Exact original-source endpoint

`original_physical_randomized_lower` uses the same observed labels `Fin k ⊕ Fin u`, available target roots, positive binary physical source class, elementary pair-CI/single-endpoint conditional-invariance menu, and **full original marked-TCM-class target** as v49/v50. It requires k>0, preserving the dated k=0 zero-query correction.

Let Ω be any measurable space, μ any probability measure on it, and ε any extended nonnegative number. A family of policies is indexed by Ω. For every admitted physical source P, suppose the failure event is measurable and its μ-probability is at most ε. Suppose also that the per-index ever-tested events and the total baseline query count are measurable. Then the proposed theorem concludes

`M * (1 - (ε + ε)) ≤ ∫⁻ seed, total baseline queries(seed) ∂μ`,

where M=choose(u,2)2^(u−2), subtraction and integration are in the extended nonnegative reals, and the baseline is **one fixed actual constructed physical source**, not chosen after a seed or a query. For real 0≤ε<1/2 this is the original (1−2ε)M lower bound. The extended formulation also covers infinite expectation, without an integrability assumption.

No finite seed space, fixed horizon, finite-support randomization, bounded stopping time, almost-sure termination, independent response noise, or new observational oracle is assumed. Error-event, test-event and count measurability are explicit random-algorithm requirements needed to interpret probabilities and the extended expectation, not assumed causal source/response/target adapters. The internal union-bound argument even allows outer measures for error sets, but the final public signature retains their measurability so that its error bounds are ordinary probabilities. These requirements are not presented as already derived for an arbitrary untyped software implementation.

## Actual policy and failure semantics

`HardFamilyUnboundedRuns.lean` defines a policy from the entire executed Boolean history to one of:

- a returned full-class output;
- the next elementary action;
- silent divergence, meaning no next action and no returned answer.

An internal finite computation is compressed into its next decision. A fixed seed determines all decisions; the source is **not** an argument of the policy. A run state retains its actual executed history and optional terminal output. Returned outputs are absorbing. Each action adds exactly one query row; stopping and silent divergence add none. Thus an algorithm that silently diverges after finitely many queries is not charged fictitious additional queries, but it does fail.

`PolicyError E policy source` is literally the negation of “there exists a finite step at which the returned output equals E.target(source).” It includes wrong answers, infinite querying, and silent divergence. It does not discard nonterminating seeds from the error budget.

## Pathwise causal coupling, proved rather than assumed

The v50 source adapter has already proposed proof bodies for every action's physical response equality away from one exceptional separator index q, and for unequal baseline/rival full-class targets under k>0.

For the same arbitrary fixed seed on the baseline and rival q:

1. `state_eq_if_never_tests` inducts on the actual run. If q is never tested on the baseline path, the histories, policy decisions, responses, and optional outputs remain equal at every step. The same rival graph and shared binary mechanism are used throughout.
2. `different_outputs_require_test` uses absorbing-output uniqueness to show that different returned outputs force an actual q-test on the baseline path, even when the two stopping times differ.
3. `first_test_time` chooses the least actual finite history time containing that distinguishing action and proves that every earlier baseline history contains none. This is not a different rival fitted to each prefix.
4. `never_test_implies_error` says that absence of q forces failure on at least one of the two sources. If both succeeded they would have finite stopping times and the same correct output, contradicting full-class target distinction. This implication also covers nontermination without any separate termination premise.
5. `original_physical_policy_state` and `original_physical_policy_error` identify the promised-family runs with their literal runs in the **all-physical-source** experiment. The final error hypothesis is on every admitted physical source, then restricted to the fixed constructed family. This is not a probability bound on an unrelated one-hot game.

## Counting and expectation, including infinite runs

`HardFamilyRandomizedLower.lean` defines `totalQueries` as the supremum over all finite times of the actual baseline history length, coerced into the extended nonnegative reals. Returned outputs retain their history, so it equals the paid terminal count when the policy terminates. Infinite querying gives infinity; silent divergence has its actual finite count.

There are only M exceptional indices, not necessarily finitely many seeds or run steps. For every seed, the finite set of indices ever tested has a common finite witness time: induct over that finite set, take the maximum of the individual witness times, and use exact history retention. At that time, v50's “each action tests at most one index” result bounds its cardinality by the actual number of executed rows. Consequently the sum of all M ever-test indicators is bounded pointwise by totalQueries, including infinite runs.

The complement of q's measurable test event lies in the union of the baseline and rival-q error events. The union bound gives complement probability at most ε+ε, hence test probability at least 1−(ε+ε). Sum over q; finite-sum linearity of the nonnegative Lebesgue integral and the pointwise count inequality give the stated expected bound. No exchange of an infinite seed sum, optional-stopping theorem, sampling independence, or finite expected-runtime assumption is used.

## Dependencies and limitations

These two files depend on the complete unelaborated v49 physical realization and v50 graphical/target lower adapter. Their final theorem does not expose an assumed coupling, one-hot signature, source-realizability theorem, nonzero-minor lemma or target-separation oracle. The error bound and measurability are model premises of a randomized procedure, not new graphical conclusions.

This proposes the L7 join for the current exact elementary action language. The optional hand-theorem vector-endpoint and within-regime CI action extensions remain separate source work, as does any affine-coordinate/rank presentation beyond the actual v50 G7 winning theorem. No arbitrary binary full-law lower bound, statistical sample count or number-of-interventions lower bound is claimed. The target, source class, positivity/faithfulness and separate soft-intervention semantics have not changed.

Classical attribution remains as in the hand manuscript and v50: unseen-separator CI lower bounds of Zhang–Shiragur–Uhler and Franquesa Monés–Zhang–Uhler; the elementary same-seed coupling/union-bound/counting argument is not claimed as a new probability theorem. No novelty or external peer review is asserted.

## Pinned API inspection and status

Same Lean 4.33.1 / mathlib `0df444a360eaa60ab8c11dca51a86af692955474` package. Read-only source inspection verified the exact declarations used, not their elaboration in this packet:

- `Mathlib/Data/Nat/Find.lean`, blob `1a61e465b21bd939100fed36612b5ab9a028b564`: `Nat.find_spec`, `Nat.find_min'`.
- `Mathlib/Algebra/Order/Sub/Defs.lean`, blob `30dc35453b785c8b88c20efc9ed082b6a2b90904`: the ordered truncated-subtraction adjunction `tsub_le_iff_right`.
- `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`, blob `8611e81e90214ac3fb9ba7e683b33813ab0a5dd6`: nonnegative integral monotonicity and exact measurable-set constant-indicator integral.
- `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`, blob `0fba96a44726e29b24d4fbac6506dd28f9fc5eca`: `lintegral_finsetSum` under explicit measurability.
- `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`, blob `7e9ed301634d09077d2544d1dd69559191a7eb0c`: `prob_add_prob_compl`.
- `Mathlib/MeasureTheory/OuterMeasure/Basic.lean`, blob `b9bf43ad126a2091696c8fe7e05b44a7e2e89908`: measure monotonicity and the two-set union bound.
- `Mathlib/Algebra/BigOperators/Ring/Finset.lean`, blob `cdd6f7f559520a37ac4bb25734ca70c2a8bddf8c`: `Finset.sum_boole (p) (s)` explicitly identifies the finite indicator sum with the cast cardinality of the filtered index set. The source uses this exact theorem rather than depending on an unspecified simplifier normal form.

## Scoped coordinating review, 23 October 2026 at 04:36 UTC

A coordinating assistant read this full handoff and accepted the described hand argument and scope: the same arbitrary seed measure, actual finite correct output with nontermination counted as failure, no horizon, baseline never-test coupling, finite-index common witness time, measurable events/count, and the extended-expectation bound M(1−2ε) with nonnegative truncation. This is **coordinating assistant review, not human/external peer review**. It is not acceptance of every proof body in the two new modules or their transitive imports, and it is not Lean elaboration. The optional vector/within-regime extensions remain separate and k>0 remains explicit.

No successful compilation, complete source-body/axiom review, or verified end-to-end full theorem is claimed. The G7 port and earlier graph/probability source dependencies retain their separate unelaborated status.
