# Explicit restricted-query policy and exact G7 adapter

Author: dot (OpenAI), 23 October 2026 UTC.

**Source-only, unelaborated candidates. No Lean/Lake/compiler/solver/backend/CI execution. No machine-verification, extracted execution, novelty or proof-site claim.** This packet continues the original selected soft-intervention theorem; it does not adopt a hard-intervention or statistical-sample target.

## Exact exposed endpoint

The new six source modules are `EffectiveQueryEnumeration`, `G7ResourceGamePort`, `FiniteQueryPlan`, `FullClassQueryGame`, `RestrictedInteractivePlan`, and `RestrictedQueryBudgetBound` under `lean/`.

The actual final source signatures include:

```lean
def effectiveRestrictedPlan {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    Plan (ElementaryAction X T) Bool (Finset (TargetCode X T)) (coordinateBudget T)

theorem effectiveRestrictedPlan_valid {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response) :
    Valid (sourceGame T source response) (effectiveRestrictedPlan T) [] (coordinateBudget T)

theorem effectiveRestrictedPlan_full_target {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X)
    (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ run (originalGame T) (effectiveRestrictedPlan T) D, decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G

theorem coordinate_budget_bound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    2 * coordinateBudget T ≤
      5 * Fintype.card X * (Fintype.card X - 1) * 2 ^ Fintype.card {x : X // ¬ T x}

theorem coordinate_budget_full_coverage {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (allTargets : ∀ x, T x) :
    coordinateBudget T = 5 * (Fintype.card X).choose 2
```

The exact indexed B identity is the already supplied `coordinate_budget_exact`: k(n-1), plus one `2^|U\{x,y}|` term per x<y, plus one `2^|U\{x}|` term per available t and x≠t. Natural subtraction covers n=0. The grouped sharper k,u formulas are not newly formalized here. The displayed full-coverage count is a property of this policy, not a new discovery of HPL's prior quadratic full-coverage result.

## Premises, not derived facts

1. X has supplied finite enumeration and linear-order data; T is decidable. All observed variables remain labeled and retained.
2. Each `FiniteSource X` is an original acyclic directed graph with arbitrary finite latent and selection carriers. Selection vertices are sinks. Their finite cardinalities are not bounded by an input assumption. The source and all named indicator augmentations have the earlier literal graph semantics.
3. `ExactResponse source response` means, for every s and elementary action a, `PositiveAnswer (source s) a ↔ response s a = true`. Invalid coordinates are totalized false, while the actual plan separately proves it asks only legal ones. This is an exact graphical CI/conditional-invariance oracle, not samples or arbitrary binary predicates of full laws.
4. The soft intervention interpretation uses one exogenous sole-child indicator I_t→t for each named available target, the same baseline source and selected event, and fixed shared nontarget/latent/selection mechanisms. The game response is a stationary coordinate of that one source, not a cumulative post-intervention state. Physical distributional realization and the invariance/law-comparison equivalence remain D1–D6 below.
5. Every imported causal proof body and the local G7 compatibility port must still elaborate in the declared pinned package. There is no compiled certificate for this packet or its transitive imports.

There is no assumed `CompleteHistory`, first-arrow/MEC oracle, bounded original hidden carrier, independent indicator realization, decoder correctness axiom, or per-query change of source in the final signatures.

## Facts derived in the source bodies

- Sorted observed labels and injective full bit-word lexicographic keys give actual finite coordinate lists. The definitions do not use `Finset.toList`, `Classical.choose`, `Fintype.equivFin` or `Fintype.ofInjective`. The earlier generic existence enumeration remains separately noncomputable and is not used by `effectiveRestrictedPlan`.
- `collect` is a structurally recursive response-branching `Plan`. It chooses an action before receiving either Boolean response, then prepends exactly that row to the history. `Collected` tracks retained rows, recorded indexed replies, unchanged unqueried coordinates and exact added length. Nodup prevents later overwriting of an earlier index's reply.
- `collect_valid` proves legality for every Boolean branch, even if no source realizes that branch. Resource state is a remaining natural query count: legal means positive budget AND a legal elementary action; update subtracts one. A different response does not reset, enlarge or replace the budget.
- Marginals precede mask-dependent observed and indicator batches. The mask is the actual response complement. The terminal plan computes the previously explicit finite `decodeHistory`, never the noncomputable class specification or an unknown graph's response function.
- Complete history, full selected-MAG sufficiency and the common-source finite registry are imported through their actual earlier proof bodies. Terminal correctness applies to each one source fitting the WHOLE final history. Empty version spaces require no fictitious source witness.
- `classTarget` is a noncomputable target specification over all original finite sources, not the algorithm. Injectivity of graph-code decoding proves equality of the actual marked class, rather than equality of a weaker summary.
- `registry_whole_source_coverage` supplies one registry code for each original D whose responses agree for ALL elementary actions simultaneously and whose full class target agrees. `registry_source_sound` gives converse literal source realization. The original and registry games share action legality and the identical budget update.
- The original-source run theorem applies the exact G7 `valid_run_identifies` body to one D across the whole trajectory. No classical `winning_has_plan` extraction, rank compression, affine-response assumption or intervention/query analogy is used.
- The sum bounds use genuine endpoint-excluding index types. Their cardinalities inject into U; finite sum and marginal bounds yield 2B≤5n(n−1)2^u. At full coverage the subset fibers are empty, so their Boolean function spaces each have cardinality one, giving 5 choose(n,2).

## Exact provider and version provenance

The source copied into `G7ResourceGamePort.lean` is the complete repaired resource-game body from [commit 53ee5a2](https://github.com/Sodelin/Research-Commons/blob/53ee5a23159d98869da8c0c997f560acc1ac0139/research/2026-10-21-lean-online-builder/lean/hosted435/G7ExactLawResourceGame.lean), Git blob `7ff58bacc8b6fcbf1bfd9cbfffd0894eaea8c6db`. Original attribution to the accepted GPT-6 Astra Pro F1/F2 mathematical argument and dot's source is retained, with an additional explicit compatibility-port header.

The later [attributed hosted review](https://github.com/Sodelin/Research-Commons/blob/8a96bb015b6cb88df196d6897b5437344a09238b/research/2026-10-21-lean-rust-solver-builder/evidence/G7-GAME-RANK-HOSTED-REVIEW.json), blob `8c60ce01fc5aa1991cd337e6bb8cfb77ecf0ed40`, records Lean 4.35.0/mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. It inspected complete source and printed theorem types and records attributed peer hosted execution, not an independent native run by that reviewer. The resource-file SHA256 is `ae22d0f069fc62f21bed41e0a7b4864d01f9520852433839cba9120ec693b409`; the only compatibility repair replaces the losing-pair proof's unavailable `_root_.not_imp` simplification with `unfold Homogeneous`, `push_neg`, and the resulting witness. Selected audits, including `valid_run_identifies`, report standard axioms only in that hosted context. Rejected earlier revisions are not treated as success.

THIS package remains Lean 4.33.1/mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The copied body has not been elaborated here. The later hosted evidence does not verify this port, the causal adapter, this plan, or this package's transitive imports. The old draft notice is retained inside the copied source as historical text, not as a denial of that later review. Rank-compression source is not imported.

Additional pinned read-only API inspections for this packet: `Finset/Sort.lean`, blob `739519ada9a00f41e86b668a426321f840edd930`; `List/Lex.lean`, blob `499633688330dcb641b953cef5a376c13f9662d0`; `Nat/Choose/Basic.lean`, blob `1cd090d71c8175e5f2071d939d30394b4c56d9de`; ordered finite sums, blob `3745e5cb7ff4b16ad6532357837698f4bf54c4a8`. Lean 4.33.1 `Init/Data/Nat/Basic.lean`, blob `88cfc9ace257e1d79efaf89815fd7df94f63e03b`, confirms the definitional right-successor addition used in the indexed plan recursion. Read-only API inspection is not elaboration.

## Remaining original obligations

The graph-level A–C/E proof chain now has source bodies through effective enumeration, explicit interactive policy, full target transport and the required indexed/coarse/full-coverage counts. Every layer still requires actual permitted elaboration, transitive correctness/axiom audit and integration. A lexical absence of `sorry` or `axiom` is not that audit.

The probability-source layer D1–D6 remains: positive binary CPT polynomial semantics; a precise discrete faithfulness provider; selection-state relabeling as nonzero-polynomial witness; one joint shared-mechanism parameter cube for all named regimes; finite nonzero-product rational avoidance; and selected conditional-independence versus regime-law equality. `ExactResponse` is visibly a premise until these source obligations are formalized, not physical realizability established by definition.

The reviewed narrow elementary-query lower family L1–L8 remains to be formalized. This packet does not claim an arbitrary binary/full-law lower bound, a sample bound, a count of physical interventions, polynomial total runtime, hard-intervention validity, novelty, or completed machine verification. Classical HPL, Richardson–Spirtes, Ali–Richardson–Spirtes, Sadeghi and Zhou–Kocaoglu attribution remains as reconciled in the earlier manuscripts.

## Review status

Author source inspection only at creation. Earlier coordinating assistant static reviews, not human/external peer review, cover the specifically recorded v43/v44 boundaries only. They do not automatically accept this packet, imported proof bodies, the 4.33.1 port, or successful elaboration.

At 00:54 UTC on 23 October, a coordinating assistant static review, not human/external peer review, read this complete handoff and accepted its exposed scope boundary: supplied finite labels/order, exact graphical response premise, all-response Plan/Valid budget, one-source full class target, effective enumeration distinct from target specification, and attributed hosted provider evidence distinct from the unelaborated 4.33.1 port. D1–D6 and L1–L8 remain open. This is not review of every transitive proof body, compiler acceptance or machine verification.
