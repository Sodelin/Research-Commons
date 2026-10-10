# Ancestral completion of the supplied word

Separate extension for root review. The [reviewed finite-word contract](WORD-REFINEMENT.md), SHA256 `dabc36aef7265cef2efeac982b6f191540eaf12f809045bce75e6e5161952458`, its first candidate, eight supported fixtures, five Unsupported receipts and two additive FULL_VIEW controls remain frozen. No public RC1 operation, application pin or source-admission gate changes.

**Result:** after the finite word, complete every supported entering genealogy in the original ancestral population. Return its exact full ordered selected law, including the original register and a literal admitted endpoint witness. An explicitly separate unranked/topology reader may then forget those coordinates. This is the positive-rate infinite ancestral limit, not a finite-duration zero-survival substitution.

## Actual source justification

Reuse [G7AncestralRationalCompletion](../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7AncestralRationalCompletion.lean), SHA256 `5ecdd44f021e9643ecfa82eb755951c804dea80ed224961110f0fe5fce74c7e4`: `actual_completion_at_zero` and `actual_completion_rational` identify the constant coefficient of the actual ancestral polynomial with `completionKernel`. The proof uses the original finite-time kernel and its limit as ancestral time tends to infinity, with a positive ancestral pair rate.

The original [ancestral recurrence](../../2026-10-09-dot-g7-actual-ancestral-polynomial-2101z/G7AncestralPolynomialKernel.lean), SHA256 `d35da5cdf199ab9f4bb616812bb20e76c67dd1a5fe36ca8c3e644c348364cdcb`, has the same `liftTerm`, `liftExpr`, `kernelExpr` and polynomial conversion bodies as the [single-population recurrence](../lean/source-store/b4434eb89aecfc007546908f404efc41cc0de809eb8497ed22c9e48a87e4dddf.lean), after namespace/definition transport. A checked bridge must bind their exact expressions at fuel `card Copy`, then bind the sparse effective coefficient row and its outside-support zero theorem. Reuse the original proof of the limit; do not derive a new limit or invoke arbitrary chosen-table uniqueness.

[G7SelectedCompletionPolynomial](../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SelectedCompletionPolynomial.lean), SHA256 `e9941a690a40853c8833ac2230d7031aa0831aa2d929af7c62181ee86855f659`, supplies `representative_ancestral`, `actual_source_completion_projection`, `actual_selected_completion_rational` and `actual_root_law_completion_projection`. It proves representative independence from the actual finite-time projection and completion limits. The [chosen epoch-table obligation](WORD-CHOSEN-TABLE-OBLIGATION-20261010T1240Z.md) stays separate.

## Request and preconditions

Keep the private `source_word_probe_v1` request grammar and both terminal values:

```json
{"terminal":"FULL_VIEW"}
{"terminal":"ANCESTRAL_COMPLETE"}
```

`FULL_VIEW` behavior is unchanged. Completion adds no interval slot, survival variable, hybrid coordinate, new mode or register draw. Repeated slots and original γ=P(parent1) retain the finite-word bank convention.

The entire request and every word letter are validated before resource limits. Completion requires nonempty original Copy. At the end of the finite word, **every formally nonzero retained row**, its full per-copy locations and its literal witness must be at `A:original_root`; scan this support before a completion budget can mask a bad row. A live-owner-only check is insufficient unless the existing ancestor/location invariant proves the full-copy condition. No omitted panel, rerouted nonroot row or selected representative fallback is allowed.

Reject empty Copy as `InvalidInput("SOURCE_WORD_COMPLETION_EMPTY_COPY")`, and nonroot support as `InvalidInput("SOURCE_WORD_COMPLETION_ROOT_SUPPORT")`. Keep these separate from arithmetic/internal failures and explicit resource Unknown. A physically vanishing row is not permission to ignore formally nonzero nonroot support.

## Exact extraction and composition

For each entering full selected row:

1. Run the unchanged `source_population::population_row` on its admitted literal witness at `Location::Ancestral(original_root)`, using the original ordered-pair half-rate recurrence and fuel `card Copy`.
2. Extract each destination polynomial's **constant coefficient**. Reject negative constants as an internal invariant failure; drop exact zeros. No floating evaluation or new genealogy-history formula.
3. Check every retained destination has one live owner, a genealogy covering all original Copy exactly once, all-copy ancestral-root location and the unchanged full register. Validate its literal SourceValid witness.
4. Sum all literal destinations in each exact full selected-view fibre. Constants are rational, nonnegative and sum exactly to one. Retain one actual supported witness for every surviving fibre.
5. Multiply each incoming word polynomial by these constants, sum coincident full selected views, remove exact zero polynomials and apply the existing wrapper caps. Return the complete table or Unknown with no partial table.

Do not choose a single representative destination instead of summing its entire fibre. Preserve ordered grafts, representatives in literal witnesses, carried genealogies, original occurrence IDs, outer-local tree labels and the complete entering register. Only the explicit unranked reader applies the injective global-label embedding and least-leaf child canonicalization.

## Stage, budgets and failure framing

Extend the internal stage enum with `Completion`, serialized as `"COMPLETION"`. Keep the seven wrapper limit keys and seven work keys unchanged. Completion participates in their **same cumulative** query, branch and term-product budgets; it is not a word letter and does not consume the 32-letter input allowance.

Add a separate per-query `ProviderLimits.completion: source_population::Limits`, default `{calls:4096, destinations:4096, lifted_terms:65536}`. The bounded private probe records these compiled defaults through its pinned source/build receipt. They are independent of the existing epoch/boundary per-query caps. A caller may supply explicit library limits; no hidden cumulative reinterpretation.

Check cumulative `queries + current_full_rows` before any child query. If a population child is Unknown, retain stage COMPLETION, its original `Calls`/`Destinations`/`LiftedTerms` kind, exact required/cap and ancestral population metadata. Do not relabel it as a wrapper limit or substitute a partial row.

After complete child rows have been constant-filtered and full-fibre-normalized, increment branches by the sum of their surviving selected destinations, and term products by `Σ incoming_nonzero_terms × child_nonzero_terms`. Each positive constant child entry has one term. Check both cumulative totals before multiplication; check normalized destination/term caps afterward. All work arithmetic is checked integer arithmetic. Initialization counts and the final register mixture are unchanged.

Wrapper Unknown uses the existing limit frame with stage COMPLETION and exact original kind/required/cap. A completed TABLE keeps the same schema, bank, full rows, range witnesses, work fields and `source_admission_verified:false`. Scope and candidate/build identity distinguish the new capability from the preserved Unsupported version.

## Independent acceptance

The frozen [word reference](source_word_oracle.py), SHA256 `bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102`, already implements completion by the **zero-eigenvalue spectral projector of the coupled ordered-half-rate generator**. It does not reuse the population lift recurrence or a merger-history formula. All five preserved completion requests have independently generated complete expected tables:

- `singletonCalendar`: 1 full ordered row.
- `ordinaryThreeComplete`: 12 rows; three unranked rooted topologies.
- `parallelCommonCalendar`: 24 rows with both original-register values retained.
- `parallelIndependentCalendar`: 24 rows, with the once-drawn register independent of fresh current-owner routing.
- `permutedCalendar`: 12 rows under the declared global-label embedding.

Compare every coefficient, full view, actual witness, register and exact work count. The existing reference's three-tip formulas and asymmetric γ=1/3 parent controls must still pass; fair γ=1/2 alone cannot expose an orientation error. Add direct one/two/three/four-owner and carried/nonminimum completion controls, empty/nonroot rejection, zero provider/wrapper caps and exact-boundary/one-below caps. Distinguish coefficient agreement with the reference from generic native refinement.

Preserve the accepted finite-word candidate and all prior source/binary pins before building a separate completion candidate. The 117 public protocol regressions need no rerun if that executable remains byte-identical; otherwise compare both native languages again. Actual original-source completion fixtures and the new sparse completion bridge need their own kernel/evaluator qualification. General generated-calendar admission, shared physical-bank evaluation and original observed-answer admission remain gated.
