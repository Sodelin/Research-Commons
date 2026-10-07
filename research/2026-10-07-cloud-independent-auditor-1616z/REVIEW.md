# Independent audit of the Cloud G6 source-prefix drafts

Current execution evidence is in [G6-VERIFIED-PROGRAM-REVIEW.md](G6-VERIFIED-PROGRAM-REVIEW.md): the exact successor four-module component passed. The initial dated source audit below remains historical, including its concrete history-carrier finding. [README.md](README.md) indexes subsequent reviews and their limits.

Contributor/publisher: Codex independent auditor, delegated by the active Cloud G6 owner after Nolan explicitly requested the G3/G4/Lean/practical-solver/literature-and-organization/independent-auditor subagent workflow. Session `20261007T161600Z-cloud-independent-auditor`. This actual delegation supersedes the older no-additional-workers restriction for these named internal lanes; it does not activate G7, restart Dot, or grant shared-provider/build ownership.

**Verdict at 2026-10-07 16:17 UTC: source-faithful partial mathematical adapter; UNVERIFIED as a new Lean component, and the whole G6 Lean master remains IN PROGRESS.** No acceptance of uncompiled sources is issued. This lane launched no compiler job and edited neither the root worktree nor shared provider/workflow/status files.

Reviewed root commit `63daba9b4fcdde8fb2eb8d52645c870f0f3b5a1f`; `FiniteProbability`, `Conditioning` and `SourcePrefix` are tracked there. `ProgramPrefix` was an uncommitted draft when inspected. The [byte manifest](reviewed-inputs.json) records SHA256, Git blob identities, sizes and tracked status of the exact inspected sources. The auditor worktree started from freshly fetched main `714362be35d0de08202026b72f6961a6c3b7aa0c`. Findings belong to those exact inspected bytes, rather than unspecified later edits.

## Consequential finding: the current Code does not carry bin histories

`FiniteSourceSnapshot.Snapshot` carries live owners, ancestry, full live unranked genealogy, original population IDs and the original register. `decodeSnapshot` explicitly sets `history := []`. Thus these proofs act on a genuine admitted original-source **unranked endpoint/population/register snapshot**, with existing unranked subtrees retained. They do not preserve prior merger-bin histories, exact merger times, or arbitrary finite-calendar observed records.

This is not a counterexample to the stated partial adapters: their comments explicitly leave timed-bin compilation open. It is a concrete missing carrier and observation bridge in the full G6 endpoint. To discharge that gate, construct a finite decorated source state with the original prior subtree/bin labels, prove source-operation compatibility, and identify the actual joint finite-calendar observation with its output map. No arbitrary `Code → O` map can recover history discarded by decoding. Do not identify the fixed-graph original-register Code with the cross-graph boundary-forest carrier that may marginalize private unmarked internals.

This finding was sent to and actually acknowledged by the root owner. Root retained the full bin-history objective as open and forwarded the scope qualification to the Lean owner.

## What the drafts actually establish if they compile

The finite probability algebra derives `TV ≤ 1 − Σc` from common pointwise domination and normalization. Its scaled specialization handles full mass and zero mass without dividing by `1 − μ`. The generic bound validly has weaker premises than a nonnegative-subprobability formulation; this does not lose the intended PMF specialization.

`Conditioning` derives domination from `PMF.filter`'s normalized law and the defined retained indicator mass. Binding the original and filtered count laws through the **same** kernel yields domination; the desired approximation is not added as a source-model field. PMF mapping gives a single joint readout bound without a state/coordinate-count multiplier.

`SourcePrefix` instantiates this result at the existing actual `countPMF` and unchanged `sourceIteration`. The count mean is the existing globally derived `globalClockRate r * t`, independent of the entering snapshot. The actual source law expands definitionally as `countPMF.bind sourceIteration`. One original graph, sample assignment and rate bank are used on both sides. All source destinations inherit actual source-validity preservation; no arbitrary stochastic-matrix-to-biological-source cast appears.

The normalized proxy is `t_k/S_K` on `k ≤ K`, with retained mass `exp(-a) S_K`. The code's direct conditioning proof includes `a = 0` and `K = 0` by the positive mass at count zero. The reference Python backend instead uses `t_k/(S_K+2t_(K+1))` plus the deficit assigned to zero. There is no residual-lumped implementation/proof in these drafts. The preserved Python controls cannot be promoted to a test of this newly defined normalized constructor. A shared error certificate may later bound both, but their count laws and exact errors remain different.

`ProgramPrefix` composes the per-interval domination through unchanged actual boundary operations and derives a product retained mass. The same full initial Code distribution appears on both sides. It does not redraw a COMMON register per numerical interval. Provider `boundaryKernel (.common H)` reads `(state s).register H.hybrid`, while `independentPulseKernel` takes independent coins indexed by `AtNode (state s) H.hybrid`, the current owners. Rates are one shared `r`; boundary inheritance parameters stay in the fixed operation list. The theorem is not yet an actual calendar-agenda initialization/admission theorem, and it does not supply one shared multirow profile compiler or the biologically specified initial register law.

The source parameters remain arbitrary real values through `PositivePairRates` and NNReal durations; there is no computability or rationality restriction on the hidden-source quantifier. Conversely all principal constructors are noncomputable. Their exact PMF existence is not an executable rational coefficient algorithm. Explicit effective inputs/witnesses, certified Taylor tails, ratio condition `K+2 ≥ 2a`, residual error `2t_(K+1)/(S_K+2t_(K+1))`, termination, computable-real enclosures, and same-rate-bank numerical extraction remain separate obligations.

## Compiler evidence independently checked

The prior [run 37649710743](https://github.com/Sodelin/Research-Commons/actions/runs/37649710743) at input `967919f7499743f7ccc19b0aa633bb77698ffa9e` concluded failure. This lane independently retrieved its [CLI log](run-37649710743-independent-readback.log) and [run metadata](run-37649710743-observation.json). The finite real-vector declarations printed only `propext`, `Classical.choice` and `Quot.sound`; elaboration then failed in `pmf_sum_real` at line 69 on unresolved `SummationFilter` inference. The ordinary Lean invocation returned exit 1. Its failed declaration and downstream PMF declarations printed recovery `sorryAx`, which is not verification evidence. The corrected source explicitly supplies `SummationFilter.unconditional A`, but that edit needs its own execution.

The independent `gh --log` retrieval has stage prefixes and slightly different log timestamp rendering from the owner's preserved raw log. After removing that presentation metadata the payloads agree except for a trailing blank line; this comparison is retained in [failure-log-comparison.json](failure-log-comparison.json). Exact raw bytes are not claimed equal.

At the independent [2026-10-07 16:17 UTC observation](run-37650180952-observation.json), [run 37650180952](https://github.com/Sodelin/Research-Commons/actions/runs/37650180952) was pending at input `63daba9b4fcdde8fb2eb8d52645c870f0f3b5a1f`, with no jobs/output yet. Therefore it certifies no new component. Its submitted target list contains `FiniteProbability`, `Conditioning` and `SourcePrefix`; it does not include the uncommitted `ProgramPrefix` draft.

The verifier reads the pinned baseline plus additive sources, records import/source hashes and commands, compiles custom dependencies serially with `--trust=0 -j1 -M4096`, and rejects reported `sorryAx`, `Lean.ofReduceBool` or `Lean.trustCompiler`. Runtime is Lean 4.33.1 / `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. Mathlib cached objects are dependency reuse, not a full Mathlib rebuild. A future component PASS must be bound to its exact input manifest and endpoint/transitive axiom output; a successful runtime smoke does not certify the adapters.

One proof-engineering risk was sent to root before any compiler diagnosis: `prefixCount_real` attempts exponential cancellation with `nlinarith` on products. If elaboration fails, use explicit nonzero multiplication cancellation and division algebra. This is a suggestion, not an observed error or mathematical refutation.

## Whole-endpoint audit

The owner's [frozen master register](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/checkpoints/20261007T160100Z-G6-CLOUD-ACK.md) retains the accepted arbitrary finite RAW NONPLANAR source contract, separate COMMON/INDEPENDENT mechanisms, arbitrary hidden reals, actual one-source/shared-parameter profiles, and declared computational observation experiments. The following remain open Lean/source-assembly gates, even if all four current drafts compile:

| Obligation | Current evidence / exact missing implication |
|---|---|
| Effective count and source tables | Exact conditioning draft; rational tail/certificate algorithm, termination and extraction not formalized |
| Contextual positive chains and genuine positive reconstruction | Accepted hand sources; neither count conditioning nor a generic program proves both-mode source reconstruction |
| Calendar cuts, same endpoints and labelled bin histories | Accepted hand contract; current Code discards event history, so the actual finite-bin carrier/observation bridge is missing |
| All-size RAW NONPLANAR admission/core/target preservation | Accepted hand extension; no graph/core/switching Lean bridge in these adapters |
| Joint feasible source cells / both Hausdorff directions | Accepted exact shared-rate-cell hand construction; no formal effective enumeration or certified witness-to-cloud/source bridge |
| Target closures, distances and robust-fiber candidates | Accepted mathematical algorithm; not supplied by an endpoint PMF inequality |
| Anytime coverage, eventual recovery and finite-read necessity | Accepted hand classification; actual statistical/finite-transcript assembly remains absent |
| Known finite channels / closed-TV corruption / sharp 2β | Declared finite-alphabet contract; effective observed-image and strict/equality boundary theorems remain absent |
| Source-admitted rare-switch stopping obstruction | Accepted admitted hand family; no connected source-to-stopping Lean theorem here |
| Full verification, review and exact main publication | First attempt failed, revised run pending; no whole G6 kernel receipt/acceptance |

`distance > 2β` is the every-allowed-corruption positive side; `distance ≤ 2β`, including equality, is the obstruction side under the declared independent finite-alphabet observed-law model. This must not become an average-corruption claim, an unspecified DNA observation model, or a full-calendar noise theorem. G3 exact zero-distance positive-source attainment and unrestricted G4 remain separate; G7 remains queued.

## Read scope and next action

Actually inspected the new Cloud assignment/protocol/ACK/status, repository instructions and completion standard, all four drafts, source `FiniteSourceSnapshot`, `UniformizedSourceStep`, `SourcePoissonKernel`, `SourcePoissonExponential`, `SourceBoundaryKernels`, `SourceProgramTransport`, count-source handoff, forest-carrier handoff including the richer-timed-carrier countercontrol, and the additive verifier/workflow. The earlier G6 independent review and RAW NONPLANAR extension were inspected for their source-sharing, effectivity, carrier and endpoint clauses; this audit does not assert a new line-by-line reproof of their full inherited hand mathematics or unseen expanded manuscripts.

Next action: read the exact revised compiler receipt once it exists, challenge every failed declaration and endpoint axiom output, then independently inspect the finite decorated bin-history carrier before any timed-observation claim. The auditor is available to review new lane packets during this active parent task; a checkpoint does not promise background execution.
