# Root gate: actual seed/calendar proof repair

CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 03:20 UTC.

## Evidence and scope

The [actual successor receipt](verification/evidence/g6-run-37720559518-FAILED/README.md), author commit `993d2a4dd6e3bb34f57f5b1d9396db91e4e7161c`, preserves failure of run 37720559518 at frozen `28921f4ff46126897828244e8cad86b13ff603b9`. Its [scope note](verification/evidence/g6-run-37720559518-FAILED/ACCEPTANCE-SCOPE.md) records 171 successful custom modules, 403 selected reports and 4,055 owned declarations / 2,643 theorems. Independent canonical authentication is a separate gate.

PrivateSeedFactorization and PrivateRegisterCalendar failed as whole modules. PrivateSeedHistoryFactorization, PrivateRegisterCalendarPrefix and NaturalCalendarPastAdmission were blocked. Their recovery reports do not enter acceptance. All failed originals and actual logs remain preserved.

## Exact repair authentication

Root fetched both original files from the failed immutable input and both candidates from [preparation](verification/preparation/private-seed-calendar-repair-0315z/README.md), commit `6fe2728c3e93f715de765116509d27733e746071`. SHA256 and exact single-edit reconstruction pass:

| Module | Original SHA256 | Candidate SHA256 | Only change |
| --- | --- | --- | --- |
| PrivateSeedFactorization | `f3d7e97db701bb60d4d7e4f8ce1218bed1226ea198f13f1ad12861e1d312e14b` | `f97b65ffcb4820bdbe9173e75085ab2ee28fec2ecf816fa1dc83ce0f275c7f33` | Add `dif_pos hv` to the positive-membership branch's existing simp list. |
| PrivateRegisterCalendar | `a639cd69881e89e0e330ba20b944eb0a489941991a7af553cbb27036ad230ffa` | `abd013f3acab1e313957c28703c727ef4b5679bf753ea86adc95d95e22b27cc3` | Delete the final `simp only [List.append_assoc]` after `rw [ih d]`. |

The actual Seed log leaves exactly the dependent membership conditional in outsideRegister, while the left branch has simplified to false. The new `dif_pos` uses the existing `hv : v ∈ P`; it adds no premise. The Calendar log reports “No goals to be solved” on the deleted tactic, after the existing rewrite. Both edits are proof-only. Every other byte, statement, definition, provider, register flag, source carrier and scientific assumption remains fixed.

## Static selection and actual baseline

The [static plan](verification/freeze-plans/private-seed-calendar-repair-static.json) has SHA256 `9df427242a086e28a9e7f26fa87f5e426eb01f90e39076f40841535af8668117`.

Root compared it against both the preceding reviewed static plan and the recovered actual failed-input manifest. Exactly two requested source hashes change. The other 174 source hashes, every import list, topological order, target, selected name, namespace count and external root remain fixed. Root also matched every one of the 171 actually successful modules against the recovered actual manifest and complete ownership module list: all 171 hashes remain exact.

Selection remains **176 custom modules / 463 requested reports (331 G6, 117 G3, 15 G5)**. These are requested counts. New successful scope requires actual exit receipts, named reports and the complete generated/type/body/transitive-axiom inventory. Later G3 scalar, natural suffix completion, rational residual and structural adapters are outside this selection.

## Budget and execution gate

The previous actual job took 752 seconds, with a 719-second serial step. Five requested modules remain unverified. The unchanged 860-second estimate leaves 108 seconds beyond the observed job and fits the enforced 900-second job cap. This is a planning estimate, not a runtime guarantee. The 180-second command cap and `--trust=0 -j1 -M4096` stay fixed. No new transitive Mathlib context is introduced.

**Root accepts the exact proof-source changes and unchanged selection/budget at source level.** This note does not authorize an automatic retry or claim compilation. Before one sole successor, require the primary auditor's canonical actual-terminal and exact-repair acceptance, fresh empty-queue checks, immutable provider/input/workflow guards and a new dispatch receipt. The sole Lean owner executes and recovers it. No competing compiler or enlarged selection.

Natural-past physical binding remains unaccepted until its actual consumer passes. Cross-graph/contextual physical replacement, effective law/backend correspondence, menu/pruning and the full G6 endpoint remain separate obligations.
