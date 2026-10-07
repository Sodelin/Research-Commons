# G6 Cloud: source-faithful finite certification, in progress

Contributor: CLOUD-G6-SOL-ULTRA-20261007. Read [the corpus overview](../../RESEARCH-STATUS.md) for the wider programme; [the assignment](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/G6-SOL-ULTRA-PROMPT.md) and [startup frozen contract](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/checkpoints/20261007T160100Z-G6-CLOUD-ACK.md) define this endpoint.

The question is whether finite noisy observations yield effective, honest source/target certificates for every source in the original admitted class. Accepted hand mathematics includes the RAW NONPLANAR extension. This packet is translating the actual source and the remaining effective/statistical conclusions into Lean; it does not yet close the full Lean master.

## What the new source chain establishes

| Source | Meaning | Actual execution as of 7 October 2026, 18:21 UTC |
|---|---|---|
| [FiniteProbability](sources/UnifiedLean/G6/FiniteProbability.lean) | Finite common-subprobability and scaled-domination total-variation/event bounds, retaining zero/full-mass cases | PASS at `89dffaa` in run 37651501035 |
| [Conditioning](sources/UnifiedLean/G6/Conditioning.lean) | Mass of an actual retained PMF event, normalized filter, same-kernel bind domination and joint finite readout contraction | PASS in that run |
| [SourcePrefix](sources/UnifiedLean/G6/SourcePrefix.lean) | Condition the actual Poisson count and bind the same actual sourceIteration; derive retained mass, source domination and factor-free joint readout bounds | PASS in that run |
| [ProgramPrefix](sources/UnifiedLean/G6/ProgramPrefix.lean) | Compose stage conditioning from the same initial snapshot law, retaining exact boundary/register operations | PASS at `3a45c828`; sum-of-deficits state/joint-TV budgets also PASS at `1eb4b9a7` |
| [TaylorCertificate](sources/UnifiedLean/G6/TaylorCertificate.lean) | Positive geometric Taylor tail and computable retained-mass error bound, connected to actual source/joint-readout inequalities | PASS at `1eb4b9a7`, run 37655542723 attempt 2 |
| [RationalCertificate](sources/UnifiedLean/G6/RationalCertificate.lean) | Exact rational coefficients tied to the actual prefix law; least accepted cutoff exists and terminates for a supplied rational mean/budget | 17 selected reports PASS at `042da4c`, partial run 37661997971 |
| [BinHistory](sources/UnifiedLean/G6/BinHistory.lean) | Coarsen actual graft ages; persistent pair relations and two genuine same-bin mergers | Seven selected reports PASS in that partial run |
| [HistoryPrefix](sources/UnifiedLean/G6/HistoryPrefix.lean) | Joint actual endpoint-vector domination and a retained correlated PMF past label | Failed at `042da4c`; repaired derivative at `4fed303` PASS, ten named reports in run37663829244 |
| [BinFold](sources/UnifiedLean/G6/BinFold.lean) | Coarsening through the actual record fold; constant-bin fold conditional on every active tag | PASS at `4fed303`, three named reports in that successful run |

The later [successful four-module receipt](verification/evidence/g6-run-37652484086-PASS/README.md) confirms all 61 custom dependency targets and the complete 51-declaration audit passed, using only propext, Classical.choice and Quot.sound. Pinned Mathlib cache was reused. [Independent terminal/source review](../2026-10-07-cloud-independent-auditor-1616z/G6-VERIFIED-PROGRAM-REVIEW.md) accepts this precise unranked component scope. Earlier failed attempts and raw logs remain in the evidence paths. Follow [current status](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/STATUS-G6.md) for later results.

[The expanded successful receipt](verification/evidence/g6-run-37655542723-attempt2-PASS/README.md) records exact input `1eb4b9a7f39f50aa6bc59f2791e82d380764fdf5`, 65 custom source elaborations, 46 external Mathlib import roots and 67 zero-exit commands including cache and audit. All 80 selected declarations passed the standard-only transitive audit: 64 G6, one G3 scalar and 15 G5 frozen analytic-support declarations. This is an audit of selected statements and their dependency axioms, not a complete inventory of every declaration in the corpus.

[Independent terminal/source authentication](../2026-10-07-cloud-independent-auditor-1616z/G6-TAYLOR-G3-G5-VERIFIED-REVIEW.md) accepts that precise scope, matching all seven source identities and reconstructing the final audit stdout byte-for-byte. It keeps the original stopped-G5 failure/recovery stage separate from the successful current audit.

[Exact rational count certificate](TAYLOR-CERTIFICATE.md), [executable](count_certificate.py) and [actual 24-case receipt](count-certificate-controls.json) supply the inner numerical search/validator. [Independent hand/code review](../2026-10-07-cloud-independent-auditor-1616z/COUNT-CERTIFICATE-REVIEW.md) accepts recurrence, ratio tail, rational termination and explicit resource-limit semantics. The Lean Taylor/source bounds and, in the later [partial 104-report receipt](verification/evidence/g6-run-37661997971-FAILED/README.md), rational least-cutoff termination and normalized coefficient correspondence are checked. [Independent helper review](../2026-10-07-cloud-independent-auditor-1616z/RATIONAL-BIN-VERIFIED-HISTORY-FAILED-REVIEW.md) accepts these successful targets and rejects failed History recovery. The Python executable-to-Lean correspondence, arbitrary-real enclosure integration and outer law tables remain open. Earlier run 37654465801 passed the three new program-budget declarations but failed the Taylor series elaboration; its failed/recovery outputs are preserved. The repaired run's first attempt failed at GitHub startup with no jobs; attempt 2 actually compiled and passed. The stopped G5 diagnostic was recovered and matched before the analytic repair.

The base bounds concern the actual unranked snapshot/endpoint readout;
HistoryPrefix extends them to an entire finite endpoint vector and a
retained correlated PMF past label. The current `Code` keeps live genealogy, populations and registers but decodes prior event history as empty. Arbitrary endpoint readout contraction does not establish the required finite-calendar lift with old subtrees/bin histories. The normalized conditional proxy also differs from the old reference residual-lumped backend.


The [complete timed-context receipt](../2026-10-07-cloud-g5-sol-ultra-1557z/verification/evidence/g5-takeover-run-37658528073-PASS/README.md)
and [independent inventory review](../2026-10-07-cloud-independent-auditor-1616z/FULL-TIMED-TAKEOVER-REVIEW.md)
authenticate 170 selected modules and 3,856 owned declarations. They include
the inherited G5 timed consumer but predate Rational/History/Bin/BinFold.
The newer 104 reports and [successful 117-report build](verification/evidence/g6-run-37663829244-PASS/README.md)
overlap those components. The latter includes 142 custom modules and nine
G6 modules/101 named reports, with HistoryPrefix and BinFold now passing.
[Independent117-report review](../2026-10-07-cloud-independent-auditor-1616z/HISTORY-FOLD-VERIFIED-REVIEW.md)
authenticates exact sources and every compiler/final-audit stdout. These named
audits are not an updated generated/type/body-reference inventory.
The next bounded build adds [actual clock-to-bin support](ACTUAL-BIN-CLOCK.md),
the [finite-tag decoder](../2026-10-07-cloud-g3-contextual-source-1716z/finite-tag-decoder-1806z/README.md),
and the required complete expanded ownership inventory; those targets
remain unchecked at this snapshot.

## Current full-master register

This is the current successor of the historical startup register; the [startup ACK](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/checkpoints/20261007T160100Z-G6-CLOUD-ACK.md) preserves its original open snapshot. Accepted hand sources and attribution are unchanged.

| Obligation | Strongest actual evidence | Exact remaining action |
|---|---|---|
| Exact source/observation/target contract | Frozen original contract and accepted nonplanar hand review | Maintain arbitrary real hidden parameters, one shared source bank and separate mechanisms |
| Finite common-subprobability/scaled domination | FiniteProbability PASS and full selected 51-declaration audit | Reuse in connected downstream master |
| Actual conditioned count/source proxy and joint readout | Conditioning + SourcePrefix + same-register ProgramPrefix, including sum-of-deficits state/joint-TV budgets, PASS | Connect to the full master; retain normalized/residual distinction |
| Positive Taylor tail, rational certificate/effective termination | Taylor/source bounds PASS; RationalCertificate 17 named reports now prove least-cutoff termination and coefficient correspondence at supplied rational means; Python controls and hand/code review preserved | Executable correspondence, arbitrary-real certified enclosure integration and outer all-source law approximation |
| Contextual genuine positive-chain approximation/reconstruction | Accepted G6 Appendix A plus reviewed [COMMON contextual/effective constructor](../2026-10-07-cloud-g3-contextual-source-1716z/README.md); Lean open | Formal COMMON/INDEPENDENT, all entering forests/all finite caps, source-faithful physical chains |
| Cut guards, fixed endpoints and actual timed-bin lift | BinHistory seven actual-source reports PASS; HistoryPrefix joint-vector/PMF-past and BinFold same-record quotient now PASS; inherited 170-module actual timed environment passed | Active-age/bin support, refined calendar composition, retained old tags and unordered internal-node decoder; full law binding |
| RAW NONPLANAR admission, core and target preservation | Accepted all-size hand extension | Connected source/bridge/component/switching proofs |
| Joint feasible cells and rational law extraction | Accepted hand characterization | Effective exact feasibility, genuine witnesses and one shared parameter bank |
| Both target-image Hausdorff directions/distance enclosures | Accepted hand characterization | Connected effective source/compiler/closure construction |
| Candidates, honest confidence, eventual robust-fibre recovery | Accepted hand statistical contract | Exact source compiler plus simultaneous coverage and recovery consumers |
| Finite-read impossibility and rare-switch nontermination | Accepted admitted-source hand arguments | Source admission and exact stopping proof chain |
| Known finite channel/closed-TV/sharp 2β corruption boundary | Accepted finite-alphabet hand contract | Effective observed images, strict/equality cases and connected robustness conclusions |
| Publication/semantic challenge/build/full axiom audit | Immutable failed and component-pass receipts preserved | Successful connected endpoint, reproducible pins, complete audits and independent full-source review |

No positive source floor, rationality restriction on hidden parameters, per-row fitted witness or exact-real equality oracle is introduced. G3 exact attainment, G4 stopping and practical DNA precision remain separate. The single internal Lean owner controls serial frozen builds; see [the verification instructions](verification/verify.sh) and [runner](verification/run.py). New G7 work remains queued.

## Continued source work after the documentation checkpoint

[Joint actual-source history approximation](JOINT-HISTORY-PREFIX.md) extends
the product error budget to the inherited entire endpoint-vector law and a
retained correlated old-past label. [Same-bin actual graft update](SAME-BIN-UPDATE.md)
coarsens the inherited age update and identifies a source-legal endpoint
collapse within one bin. The initial root drafts remain preserved byte-for-byte. BinHistory now has
actual seven-report PASS. After two elaboration repairs, HistoryPrefix and
BinFold now have ten and three actual selected PASS reports respectively
in run37663829244. Rational least-cutoff work has actual PASS. The [targeted source map](../2026-10-07-cloud-lit-organization-1621z/g6-calendar-history-1722z/README.md)
locates the actual G2 history/decoration providers and remaining quotient gates.

[Programme development and expected usefulness](PROGRAMME-DEVELOPMENT-AND-IMPACT.md)
answers Nolan's questions about modular Lean, goal changes, the OpenAI
mathematics release and impact timing. It distinguishes delivery targets
from breakthrough or empirical-impact forecasts.

[Timed source explained](TIMED-SOURCE-EXPLAINED.md) gives a plain-language
account of how G2's clocks, old subtree ages, joint histories and projective
readout feed the G5/G6 consumers, with the actual 170-module build boundary.
