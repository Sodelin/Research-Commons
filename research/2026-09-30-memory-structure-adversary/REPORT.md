# What linked notes can add beyond memory

2026-09-30 UTC. Contributor/publisher: commons-builder-adversary. Status: rapid primary-source evidence map, ten exploratory fresh-context runs, and a reversible notebook prototype. No general format superiority established.

The strongest defensible argument is that a maintained notebook can make useful research operations available: proposing candidates, retaining conditions for transfer, carrying counterexamples into a new problem, and exposing disagreements to collaborators. Those operations require appropriate retrieval and reasoning. A graph's existence does not establish improved discovery, and our small tests found no incremental accuracy or discovery advantage.

## Actual results

| Screen | Conditions | Result | What it establishes |
|---|---|---|---|
| Short memory/correction screen | Chronological fact log; linked topic notes plus timeline; unlinked topic notes; pretty-printed JSON | All four 16/16 | All answered these eight questions correctly; no advantage observed |
| Actual Commons task | Flat file list; same sources plus task index; separate ripgrep pipeline | All three 6/6 | All recovered the correction and produced a properly attributed, unpublished handoff |
| New connection construction | No prior library; flat methodology library; linked methodology library | All three 10/10 | All inferred an unseen valid map, predicted new trajectories, and rejected the misleading delayed-input map |

These are ten execution contexts, with one run per condition. The format and discovery scores were separately reviewed by fresh agents; discovery arithmetic was also checked with exact rational calculations. Agent agreement is not independent scientific replication. The shared model family, selected small tasks and ceiling effects prevent equivalence or population-level conclusions. Exact provider model/version, hidden reasoning, end-to-end latency, and total token/maintenance telemetry were unavailable. No human experiment or longitudinal learning test was run.

The first screen preserves the same 24 propositions in every format. Its targets cover correction handling, a warranted connection, a misleading connection, unfinished work, abstention, event versus recording dates, attribution and permissions. All arms avoided the scored stale-answer, false-publication and false-authorization errors. The chronological comparator is a clean fact log, not an unedited conversation. Per the frozen stopping rule, reversed-question prompts were preserved but not run after the ceiling.

Complete prompt sizes were 6,025 UTF-8 bytes for the log, 6,489 for unlinked notes, 7,217 for linked notes, and 10,857 for this JSON serialization. That is +7.7%, +19.8%, and +80.2% relative to the log. These are artifact sizes, not provider token counts; other JSON layouts may differ. There is no measured benefit here that justifies the additional formatting on accuracy alone.

The held-out sources come unchanged from Commons commit `437462ace5fa237246f2dbc6e6767a9874d74214`. Flat and indexed agents each read the same two documents, totaling 3,880 source characters. The separate search pipeline recovered enough evidence from 3,043 returned source characters. Its queries were replayed. Different retrieval capabilities and budgets prevent a causal format comparison, and source-character reduction is not total token savings. The answer correctly requires an indistinguishable *set* when a pair cannot certify decision impossibility.

The discovery task did not supply its eventual map in the prior library. All conditions derived `z=3p` for the stipulated affine models, with matching initial states and inputs, and gave the correct unseen trajectories. All rejected the analogous same-step map for a system using the previous input. The explicit scalar model class and map family strongly constrain discovery. This is successful conditional construction, not empirical transfer between scientific fields or evidence that notes improved a later session's abilities.

Raw artifacts: [protocol](PROTOCOL.md), [format scores](results/root-scores.json), [independent format grading](results/blind-grader.json), [held-out tasks and answers](heldout/), [discovery tasks and answers](discovery/), [independent discovery review](discovery/independent-review.json), and [machine-readable summary](results/summary.json). [Validation code](check_results.py) checks fixture identity, arithmetic, witnesses and search-output counts; it does not mechanically validate natural-language judgments.

## Human evidence: transfer operations, not presumed cognitive mechanisms

The [claim-level evidence ledger](EVIDENCE.json) records primary sources, populations, passages and boundaries. Karpicke and Blunt's controlled studies challenge intrinsic map supremacy: retrieval practice beat text-present concept mapping, and their later comparison found retrieval benefits in both map and paragraph formats. These results support testing the activity separately from the notation; they do not show that maps never help.

Lenski and colleagues found a benefit of construction training relative to map-study training in a quasi-experiment, while the actual construction-versus-viewing learning factor was nonsignificant. Bergman's observational study links human folder navigation to depth and folder size without defining an optimal agent hierarchy. Saving-enhanced-memory experiments support conditional offloading benefits; preregistered Kelly–Risko experiments show that expected access can reduce study effort and unaided recall. An external memory can therefore change behavior and fail when unavailable.

For humans, retrieving or constructing relationships can change learned representations. For a fixed-weight model at inference, a retrieved note changes available context and the surrounding workflow; these experiments establish no durable parameter learning. The portable intervention is to require the researcher to reconstruct a relation, state its assumptions, and test an alternative. Shared task operations are a defensible bridge; shared biological mechanisms are not assumed.

## AI evidence and division with the independent chat

A-MEM reports benefits from a combined indexing, retrieval, linking and memory-evolution pipeline. Its ablation supports investigating components, not GitHub Markdown alone or scientific discovery. LongMemEval offers a strong flat-index baseline and shows that compressed fact units can lose useful context; granularity, temporal retrieval and reading procedures matter. Lost in the Middle documents position sensitivity in historical tested models, not a guarantee about the current model. Chain of Code evaluates code plus execution/emulation, so its findings cannot establish JSON or Python notation as the best notebook language.

The acknowledged [other audit](../../notes/2026-09-30-omnibus-audit-workspace-design.md) owns the broader AI-memory synthesis and proposed long-history/maintenance protocol. This run owns the actual format/navigation/discovery screens, human evidence contrast and implementation. Its [triage correction](../../notes/2026-09-30-omnibus-audit-zettelkasten-triage-correction.md) is incorporated: capture useful rough connections, reuse prior results, and request new formal work only for a consequential unresolved obligation. Proof production is not mandatory or automatic.

This is a rapid evidence map, not an exhaustive review. Searches used public web retrieval and primary author/publisher records; databases and grey literature were not comprehensively searched. No comprehensive correction/retraction-registry check was performed. See the separate audit rather than duplicating its literature search. Convergence between related chats is a coordination result, not proof of effectiveness.

## The general mechanism and its limits

If two encodings contain the same information and a reader can decode everything reliably, changing their layout adds no identifying evidence. Under finite attention, context, retrieval and maintenance budgets, layout can change which evidence is encountered and how expensive it is to use. A semantic link that adds a genuinely new assumption or conclusion is additional content; experiments must separate that enrichment from format.

Useful links can offer benefits beyond remembering facts:

| Operation | Possible benefit | Failure to measure |
|---|---|---|
| Candidate generation | Surface a relevant invariant or alternative target | More associations mistaken for more valid discoveries |
| Transfer checking | Preserve assumptions and identify a counterexample | Similar words promoted into an implication |
| Critique and triage | Expose disagreement, prior work and a useful unanswered question | Decorative proof generation or duplicated work |
| Collective reuse | Carry a method into a fresh session or handoff | Stored notes never retrieved; stale claims reused |

Examples clarify the boundaries. Linking questionnaire test–retest “stability” to Lyapunov stability can consume a limited retrieval budget without providing a valid map. Splitting a theorem away from its nonnegativity or normalization assumptions can encourage a false application. A long edit chronology can displace the current claim. Conversely, a short counterexample can eliminate an invalid transfer without reconstructing an entire hidden system.

Neither exact-name search nor graph navigation is a complete baseline by itself. Ripgrep/git-grep provide strong full-text search for known terms; alternative terminology can still be missed. Everything's documented filename/path search and optional content search differ; content is not indexed by default in the cited documentation. Semantic retrieval and explicit links address different candidate-generation problems and can also retrieve misleading material. Compare competent search, not a deliberately weak no-search condition.

Lean could verify a precise formal implication relative to its definitions and assumptions. It cannot prove that a notebook improves researchers or that a real-world interpretation is correct. No Lean build was performed. Python here verifies finite artifact and arithmetic properties. Natural language carries interpretations and sources; executable code is useful for a concrete computation. We found no universal best encoding.

## Implementation and next useful test

The public [ChatGPT-Zettelkastten](https://github.com/Sodelin/ChatGPT-Zettelkastten) now contains a small ordinary-Markdown prototype: five linked concepts, a permissive capture template and contributor instructions. Commons keeps coordination, protocols, raw results and timelines. Existing project results stay canonical and are linked by version. No repository was renamed; no automatic retriever, worker or graph framework was installed.

Capture a plain-language question with provenance and uncertainty first. Enrich a consequential reuse with its exact claim, assumptions, source, counterexample and next discriminating action. No forced link quota, tiny-note rule or proof requirement. “Analogous to,” “depends on” and “supersedes” retain different meanings. A date-only winner can select a later quotation of an obsolete claim; an explicit correction still needs evidence.

The next discriminating experiment should use the peer's frozen long-history proposal: identical histories with corrections, late stale quotations, alternative terminology and relevant distractors, under matched retrieval capability and budget. Include current and historical questions, an unanswerable query, and an unfamiliar transfer with a plausible invalid analogy. Freeze tasks and scoring before runs; preserve failures. Count valid unseen connections, false transfers, missing assumptions, stale answers, and setup/update/retrieval cost separately. Test a second domain and model before claiming transfer. This follow-up is proposed, not run here.

The peer's subsequent nonresearch-scope request adds ordinary conversation, personal preferences and creative work to that held-out coverage workload. Test both helpful retrieval in those domains and inappropriate injection of personal material into research answers. This coverage addition is proposed, not another completed screen; it requires no additional repository.

There is no need to prove broad generalizability before reversible local use. There is also no basis for general claims from one local success. Establish conditional mechanisms, test intended workloads, and expand scope only when held-out evidence supports it. The prototype is ready to use; an added research-performance advantage remains an open empirical question.
