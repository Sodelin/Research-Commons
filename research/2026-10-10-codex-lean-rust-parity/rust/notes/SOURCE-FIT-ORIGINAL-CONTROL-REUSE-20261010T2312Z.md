# Original masks on the existing fitted-source bank

Contributor: Codex / rust_implementation, 2026-10-10 23:12 UTC. Status: sourced findings and a proposed private integration contract; no new native, reference, fitter or compiler execution. Current implementation, frontend, application and accepted source pins were read and rehashed without modification. [The adjacent capture](SOURCE-FIT-ORIGINAL-CONTROL-REUSE-20261010T2312Z.json) records full paths, SHA256 identities, inspected declarations and exact accepted-provider bindings.

The smallest interface that retains the original control semantics is a private **controlled selected-word assembly** over the existing immutable `source_fit_bank::Bank`. It can reuse `source_word::word_row` without a new route, clock or register engine: preserve the natural initializer, apply endpoint substitution only to conditional transition polynomials, and then multiply the two. The current `source_fit_readout::ProgramTerm::forcing` remains useful for the explicitly chosen rooted observer; it is not a register-preserving controlled full-Code transition.

## Accepted source contract

The accepted 1504 context contains the following exact bodies. Dated source comments saying draft or uncompiled are superseded for these bytes by the recorded kernel/audit acceptance; they do not supply native refinement.

| Provider | Inspected body and supplied implication | SHA256 |
| --- | --- | --- |
| `OriginalFixedIDControls` | `OriginalMask = Hybrid N → Option Bool`; `forcedParameter`; `controlledGamma`; `controlledMode`; `actual_forced_hybrid_kernel`; `actual_forced_owner_route` | `5b32ee2edff84d6ef7c75549b55e7368380fcff9dbb3b0cd4397584746bb224d` |
| `ControlledUnrankedSourceProjectivity` | `controlledCalendarLaw` draws `originalRegisterPMF N p` unchanged, then the controlled program; `controlledCompletedLaw` uses actual completion; empty mask is natural law | `6ba2f40bd84c286a6281335b26e9e96efd20e10e6ab6cca5919ddbb7b8f2a5e5` |
| `G7ControlledWordPolynomial` | `controlledWordPolynomial` multiplies unchanged `initialPolynomial` by `substituteControl` of the conditional word; `actual_controlled_word_polynomial` identifies the full selected coefficient | `0734c0e30fcad3a51ce4cceba5167b200f094e7fba544df4899c0b502fc83e28` |
| `G7ControlledCalendarPolynomial` | `actual_controlled_schema` binds this word to the original generated calendar; `actual_controlled_calendar_polynomial` retains the same physical rates and natural gamma | `d9efb1b177fbe61d2cdaccd64d44f420d8f9f04504f85ef8df2895f97b88c503` |
| `G7OriginalControlRelabelling` | `named_mask` transports the same original ID and Boolean; `controlled_calendar` and `controlled_completed` preserve source/register/parent maps | `6709ad22f6ec80b67783b5099e9d89607fc31b43421ca065e43492b53a5942fe` |
| `G7OriginalSurvivalCoverage` | `actual_source_survival_chart` uses one fixed strict calendar and one original-E survival bank for the natural and **all** original-mask completed full-Code laws | `59314f77f7c450321a8683bc938b6372e2c1450b6eb8b2d179a99ed696f362e9` |

The 1504 acceptance is `lean/HISTORY-SURVIVAL-UNION-1504-ACCEPTANCE.json`, SHA256 `554461bf84edc6eba14ecb2a7feba86c8632a53f0bfedc81b15b88222019c838`; its certificate is SHA256 `1f45babae7a183dc1638ebfd7de210fddcf2dd872e8498f3f80ede4d06e9fcc2`. This is an accepted theorem about supplied typed sources, positive real rates and original controls. It excludes timed retiming, native representation refinement and source reconstruction. No newer family theorem is assumed here.

Forcing is a deterministic **current-owner** pulse at the addressed original hybrid, regardless of its natural COMMON/IH mode. It sends every live ancestor at that node to `H.parent b`, including the empty-owner identity case. A carried subtree is one owner; it is never split into newly actuated tips. `controlledMode` is false at a forced site and unchanged elsewhere. `controlledGamma` is the endpoint there and unchanged elsewhere. The original natural `p` and its once-drawn whole vertex register remain untouched. True means original parent1; false means parent0. Parallel edge occurrences retain different E identities even when their endpoints coincide.

`ActualStoredRegister` (`1417d1a45a68372298aa4897fbd73bb5f7b037902c7bc4bd6058c7c4ffd7330a`) proves actual step/epoch/boundary/program register preservation. `SourceNaturalInitialization` (`18050e86…`) draws hybrid bits once with P(true)=original gamma and sets nonhybrid bits false. These existing bodies settle the source semantics; another register or control engine is unnecessary.

## Existing native capabilities and the exact boundary

* `source_fit_bank.rs` at `e31b80a3…` supplies the opaque checked Bank, original occurrences/maps, old height-derived strict ages, common physical slot relations and original gamma=`1-oldg`. `Bank::forced_parent(h, bit)` already maps the unchanged bit to the original incoming occurrence. Probability complementation never complements a forced bit.
* `source_boundary.rs` at `f089b81f…` implements exit/ordinary/root, stored-bit COMMON and per-current-owner IH. Both pulse kinds preserve live/ancestor/genealogy and every register bit. An IH row has weights `gamma^t*(1-gamma)^f`; endpoint evaluation leaves only the all-false or all-true assignment, with constant weight one, preserving the same literal register. The existing typed boundary/carried-owner/parallel-occurrence bodies cover the required primitives.
* `source_word.rs` at `7fbb4e63…` has `Initial::Natural`, `Initial::Conditional`, the original `Enter/Exit/Interval` word, fixed mode registry, shared slot-major E+ancestral/gamma axes and unchanged completion. Natural initialization and conditional word evaluation are already separate paths. `word_row` returns complete normalized **selected-view** coefficients with one validated literal range witness per key. It is not a full-Code dictionary: distinct representative/ancestor Code states may share a selected key and contribute their sum.
* `source_fit_readout.rs` at `7a3a75b6…` has typed original-bit masks and weighted labelled programs. It forgets representative IDs, child orientation and latent register only under `ROOTED_UNRANKED_COMPLETE`. Its present forcing replaces gamma throughout the already natural polynomial, including the initializer. This can reproduce the saved rooted forcing/program controls, but its own type documents that it is not controlled full-register source dynamics.
* The current frontend calls `Request::natural`; bank/readout/check/readout-replay are exposed, while mask programs are not a public request operation. The transport sidecar retains the original force/program experiment and correctly calls the current natural readout counterfactual when those observers differ.

The source-fit program test (`407adcd3…`) already checks the old forced-parent0/parent1 and labelled 1/4,3/4 rooted mixture on one unchanged bank. It does not check the retained register law. The pinned old compiler `eb829017…` takes forcing bits in original incoming order, uses old `g=P(parent0)` and returns rooted unranked trees. Its force overrides have weight one. Therefore old gamma is complemented into the native bank, while the original bit is not. It is an appropriate independent rooted-observer comparison, not an oracle for full Code or latent registers.

## Proposed private API and assembly

Proposed API, not implemented or a frozen public wire schema:

```text
controlled_selected_word(&Bank, mask: &[Option<bool>], limits)
  -> TABLE {original mask/maps, unchanged bank, slot variables,
            selected-view rows, original-register range witnesses, work}
   | UNKNOWN {stage, child/provider/aggregate limit, no rows}
   | INVALID_INPUT / UNSUPPORTED / INTERNAL
```

The first scope is one mask on a nonempty, at-most-four-copy natural **generated** complete calendar already carried by the Bank. The mask length equals the original hybrid registry length. `None` keeps the captured global natural mechanism; `Some(b)` names the exact registered occurrence bit. No caller word, warm start, new actuator, per-tip mask, rate refit, per-configuration x/g bank or mixed natural mechanism is admitted by this interface. Existing rational-only bank/RootOf-Unsupported behavior stays unchanged.

Assembly uses only existing public providers:

1. Clone the Bank's symbolic word, keep its full slot bank, set its word empty and terminal FULL_VIEW, and call unchanged `word_row` with Natural initialization. Its rows are the exact once-drawn register states and their natural initializer polynomials `I_reg(gamma)`.
2. For each preserved initializer witness, call unchanged `word_row` with `Initial::Conditional(witness)`, the original generated word/AncestralComplete terminal, and mode false exactly at forced sites. Original modes elsewhere are copied unchanged.
3. In this **conditional** table only, substitute the original gamma coordinate at a forced site with 0 or 1. Normalize exact zeros and equal monomials. The old natural register in every view/witness is retained; no temporary register rewrite is needed.
4. Multiply each resulting transition polynomial by the untouched `I_reg`. Aggregate complete selected fibres in the existing selected-key order, keep a validated canonical literal witness, and verify symbolic mass one. All original variables, locations and register coordinates remain present.

Thus the proposed coefficient is

```text
P_mask(view) = sum_reg I_reg(original_gamma)
                    * endpoint_substitute_mask(K_reg, controlledMode)(view).
```

This is the body of the accepted controlled-word polynomial, rather than endpoint substitution of the completed natural polynomial. A forced bit opposite the entering stored bit must route by the forced bit while returning the original bit. In a one-hybrid example the final register marginal remains `(1-gamma, gamma)` even when every lineage is forced parent0. That is the meaningful control which the current rooted-only specialization cannot claim.

The result remains a formal slot-bank selected-view table. Rational whole-edge evaluation of each register-retaining row is not promised: unused/ancestral axes and residual fractional exponents must retain the existing explicit Unsupported boundary. The existing 7a rooted observer can remain the first evaluated consumer; comparing its forgotten-register marginals with this new assembly is a separate binding obligation. No silent observer change is allowed.

## Operational limits for review

Reuse the current graph/copy/bank/word/slot bounds and the exact per-query provider limits. Precheck the initializer's existing `2^h` assignment and `3^h` term requirements. For this one-mask interface propose a separate default of 16 conditional-word invocations; check that requirement before launching a conditional word. A larger valid source that exhausts it returns UNKNOWN, not source invalidity.

Wrapper counts must be cumulative across all conditional calls. Pass remaining `queries/branches/term_products` caps to each unchanged child so its own pre-generation checks enforce the remaining allowance. Preserve the original child stage/kind/population/required/cap and disclose that these are operational provider refusals. Check initializer-times-transition term products before multiplication; cap aggregate normalized destinations and terms, checked count arithmetic, wrapper rational operand/result bits and bounded output. Defaults may reuse existing 4096 queries/destinations, 65536 branches/terms, 262144 products and 4096 rational bits, subject to Design's final resource contract. These are proposed limits, not an executed resource guarantee. Existing word-provider arithmetic and OS limits keep their existing qualifications; a direct moment/row checker would not certify work or exhaustion.

No public CLI, helper or app schema is proposed to change now. A later export would need an additive versioned mask/observer envelope and an independent reference extension: the current helper is explicitly natural-only. Keep all source-admission, source-equation-provenance, timed-readout, universal-native-refinement, certificate and full-solver flags false.

## Meaningful acceptance and remaining obligations

If this contract is approved for later implementation, use a small fixed set tied to current bodies:

* Empty mask equals the saved natural table exactly; original x/g/source maps are unchanged.
* Existing asymmetric COMMON bank (`oldg=1/3`, original gamma=2/3): each forced bit routes the corresponding E1/E2 occurrence, yet the whole natural register marginal remains 1/3,2/3. The unforced COMMON row uses its entering bit.
* IH with two current owners and a nonminimum representative carrying three original copies: endpoint substitution leaves one shared deterministic owner route and never splits the carried fibre; outside populations/register bits remain untouched.
* The existing parallel E2/E3 graph: equal vertex endpoints do not erase or swap occurrence IDs. Force0 and force1 remain different placements/exposures.
* A two-hybrid partial mask retains the other original COMMON register and original gamma, and keeps one shared bank across all compared masks. Compare rooted marginals after explicit register forgetting with the pinned old compiler. Weighted configurations retain labelled alpha*law separately from an explicitly requested forgotten-label mixture; no uncontrolled mixture inference.
* Invalid mask/registry mismatch is refused before low budgets; exact and one-below wrapper/child caps return qualified UNKNOWN with no partial table. Completion checks every formal entering supported view, not values made zero at the fitted gamma.

The mathematical full-Code same-bank control/retiming theorem is already accepted. The remaining native obligations are exact JSON→original registry/occurrence/control binding; canonical encoding and complete selected-fibre aggregation; the native conditional table/normalization correspondence to `G7ControlledWordPolynomial`; generated agenda/phase and all-raw-root completion binding; and, for evaluated rooted outputs, explicit readout/gamma/exponent transport. The existing typed effective word/boundary/completion providers supply the source-side coefficient identities, but do not certify a new native wrapper merely because its formula matches.

`FiniteSourceSnapshot.decodeSnapshot` sets history to `[]`, and the current native carriers have no merger-age field. Neither this proposal nor whole-edge exposure invariance supplies timed histories, timed observation/controls or G5 statistical premises. Fixed named N2/NP admission does not establish arbitrary supplied-graph parser admission, planarity/cofaciality, source census or fitted-source provenance. No accepted mathematics is reopened by these downstream boundaries.

Next action: root/Design review this one-mask selected-word assembly before allocating implementation or a sole-scheduler native slot. All inspected runtime/provider files remain frozen.
