# Proof source map and Lean storage

This is one entry point to existing stores and tools. It does not imply every manuscript is a proof, every Lean source compiles, or every archived claim is current. Public sources only.

| Existing surface | What to use it for |
| --- | --- |
| [Discovery CLI](README.md) and [theorem intake](THEOREM-INTAKE.md) | Existing canonical status, linked proof bodies, prior Git archive paths, changes, typed jobs and joined checker receipts. The full-text cache and theorem intake are distinct. |
| [Selective theorem/evidence index](../../handoffs/2026-10-09-goal-oriented-finish-lines/SELECTIVE-THEOREM-EVIDENCE-INDEX.md), [accepted results](../ACCEPTED-RESULTS-AND-REMAINING-WORK.md), and [G3/G4 master audit](../../research/2026-10-25-master-obligation-audit/README.md) | Curated scopes, prior suppliers and actual remaining statements. These are entry points, not automatic certificate jobs. |
| [Frozen preservation register](../../research/2026-10-05-dot-research-preservation-register-0125z/REGISTER.json) and [recovered G3 catalogue](../../research/2026-10-23-g3-proof-recovery/README.md) | Nine preserved packets; separately 58 recovered math notes and 17 then-unelaborated Lean files. The recovery catalogue has 16 named scoped result groups spanning those notes, not 58 independent theorem contracts. |
| [Number-theory argument catalog](../../research/2026-11-23-goldbach-residue-obstruction/argument-catalog/README.md), [RH proof-reading](../../research/2026-11-23-rh-proof-reading/README.md), and [formalization queue](../../research/2026-11-25-lean-and-conjecture-audit/FORMALIZATION-QUEUE.md) | Hand-first arguments, finite replays and unresolved analytic inputs. Pin whole statements before routing; reuse existing Lean instead of porting it again. |
| [Exact Lean bindings](../EXISTING-LEAN-CLAIM-BINDINGS.json), [package claim map](../../packages/research/integration/claims.json), and [historical binding inventory](../../research/2026-10-31-unbound70-source-binding-inventory/INVENTORY.json) | Look up names, types, dependencies and missing interfaces. Candidate reuse and confirmed binding are not the same. The 70-row inventory is historical. |
| [Portable Lean/Rust registry CLI](../../packages/research/README.md) and its [source lock](../../packages/research/source-lock.json) | Existing storage and build/check interface: `check`, `prepare`, targeted `check-exports` and `check-callers`; typed Rust emitters already exist for some families. Do not run a full retained build just to index or check one standalone module. |
| [Frontier source catalogue](../../research/2026-10-07-dot-frontier-source-index-and-obligation-map-0309z/README.md), [archive path index](../ARCHIVE-SOURCES.md), and [reading supplement](../../research/2026-10-30-catalogue-supplement/README.md) | Literature metadata, older paths and source-reference joins. Follow evidence, but don't bulk-submit these as our proofs. |

## Batch flow

1. Batch-index files and evidence before attempting translation. The default theorem intake now projects 537 records over twelve pinned source inputs (243 earlier + 294 from six existing registries). Of these, 84 are source-only, 194 binding/reuse audit rows, 258 statement review rows and one a recorded checked handoff. These are overlapping records, not counts of original or newly verified theorems.
2. Reuse an exact compiled declaration if it fits. For an unported hand proof, write a typed record under `research/proofbridge-incoming`; export supported inputs, check in Lean and join the receipts through the [theorem intake command](THEOREM-INTAKE.md). This does not silently turn prose into certifiable inputs.
3. GitHub is the source of truth for Lean code and immutable receipts; Drive can retain backup archives, not a second editable source tree. Keep new standalone sources eligible for isolated validation under `research/proofbridge-lean/`. Listed files are not verified just because they appear; promote separately after exact interface and dependency checks. The [bounded cloud batch](../../research/2026-11-25-proofbridge-linear/BATCH.md) generates and checks supported certificates on invocation; automatic pickup from registry changes is not yet wired.

```sh
python docs/discovery/tools/lean-registry.py --summary
python docs/discovery/tools/lean-registry.py --at HEAD --since HEAD~1 --delta-only
python docs/discovery/tools/theorem-intake.py --summary
```

The inventory CLI reads the named-module manifest, the content-addressed retained-source manifest, and the tracked standalone directory without compiling or copying all sources. A Windows scratch test checked the two actual input manifest Git blobs against their Commons pins, listed **233 named module records and 1,614 retained source records**, then reported an added and later changed standalone file while 1,847 records remained unchanged. Retained source records are not additional distinct proven modules; aliases and historical scopes can overlap. No full package CI replay or live hosted cache refresh.

Source deltas are not build-cache keys: an unchanged consumer can fail after a transitive import changes. Use a toolchain and transitive dependency identity, or compile affected consumers again. [Pinned cloud negative control](../../research/2026-11-25-proofbridge-linear/dependency-probe.receipt.json).

## Alexander 001 whole claim replay

The [six-lane proof packet](../../research/2026-11-25-proofbridge-linear/capped-host/SIX-LANE-ROUND-1.md) gives the checked single-host theorem in the pinned population model, both edge-labelled and fixed-source-gender. It rules out injective undirected adjacency-only embeddings. The source-only recovery replay is independent of the live install. This is a scoped proof result, not a new answer to the countable-family or other broader variants. The concrete Mathlib Real wrapper remains a separate replay check.

## Grid-minor follow-on

The [second round](../../research/2026-11-25-proofbridge-linear/capped-host/SIX-LANE-ROUND-2.md) supplies two independently checked proofs of the same finite square-grid-minor obstruction for the balanced natural-order host. The [machine receipt](../../research/2026-11-25-proofbridge-linear/capped-host/grid-minor-receipt.json) names both exact endpoints. This is a graph-level transfer, not a claim about the countable-host-family problem or a new Mathlib Real replay.

## Alexander follow-on: two-sheet avoiders and observation certificates

[Round three](../../research/2026-11-25-proofbridge-linear/capped-host/round3/ROUND-3.md) gives two graph constructions with hand-proof status and individually Lean-checked parts, plus a kernel-checked conditional observation-fibre interface. The exact binary edge-labelled cap-two result is about countable same-cap portfolios; the finite quartet transfer is not solver integration. [Exact receipt](../../research/2026-11-25-proofbridge-linear/capped-host/round3/round3-receipt.json).

## Alexander–NANUQ certificate council

[Omnibus design](../../research/2026-11-25-proofbridge-linear/capped-host/omnibus/OMNIBUS.md) indexes scoped merged-root, component and diagonal proofs; a kernel-checked finite quartet counterexample; and a bounded reference checker. Distinguish hand proof, checked components, exact Python replay and original-network admission. [Machine receipt](../../research/2026-11-25-proofbridge-linear/capped-host/omnibus/omnibus-receipt.json).
