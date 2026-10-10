# Codex build handoff — 10 October 2026, 09:45 UTC

Contributor: dot / OpenAI. The user has assigned full Lean and practical-build work to a separate Codex agent. This handoff delivers the preserved source and verification boundary so that work can continue without rebuilding the research history. No new compilation was performed for this delivery.

## Start here

The [complete modular package](https://github.com/Sodelin/Research-Commons/blob/6207670fa7fbce788d01584a033c0471ae918aaa/research/2026-10-10-dot-connected-modular-lake-0855z/README.md) is verified on main at commit `6207670fa7fbce788d01584a033c0471ae918aaa`:

- 1,440 exact content-addressed Lean source versions, including 1,439 selected versions and one preserved historical whitespace variant.
- 80 configuration/evidence files, including the reviewed builder, additive Lake entrypoint, safe unpacker and all 59 encoded artifact parts.
- A pinned 78-profile inventory: **53 required profiles certified**, and 25 separately identified provisional profiles without a pass claim.
- Both exact full aggregate axiom/reference censuses and complete source/dependency inventories in the hash-checked delivery artifact.

All 1,520 published blob identities and the README readback were checked. The non-force update preserved all 637 prior research entries and the other repository content. This supersedes the earlier source-package publication hold.

The [53-profile certificate](https://github.com/Sodelin/Research-Commons/blob/a8545d355ff01e8959847af1d6b04b097624ed39/research/2026-10-10-dot-connected-53-qualified-certificate-0842z/README.md) records a reauthenticated union of runs, not a single fresh invocation. The new public-layout reproduction configuration was source-reviewed, policy-tested and Lake-config elaborated; its full end-to-end mathematical replay remains work for the receiving build agent.

## Reproduce the frozen result

Use the package README and [resource contract](../../research/2026-10-10-dot-connected-modular-lake-0855z/RESOURCE-QUALIFIED-RUN-CONTRACT.md) as the authoritative commands and pins. The supported configuration is Linux/glibc, Python 3, official Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, with the pinned standard object/IR cache. Set `CONNECTED_LEAN_BIN` and `CONNECTED_MATHLIB` to those exact installations and use that Lean distribution's Lake executable.

From the delivered package directory:

```sh
python3 scripts/unpack_delivery.py
python3 scripts/build_resource_qualified.py --check
"$CONNECTED_LEAN_BIN/lake" -R check-build
"$CONNECTED_LEAN_BIN/lake" build connectedQualified
```

The unpacker validates encoded parts, compressed bytes and all 25 decoded records before accepting them. It rejects unlisted paths, traversal, links and differing existing files. The decoded evidence is 236,459,333 bytes; the xz artifact is 5,740,844 bytes. The manifest distinguishes exact bytes from portable operational-metadata projections. No author workspace or prior local failure receipt is required by this fresh-download entrypoint.

Keep logical-name/profile isolation. Historical versions cannot be concatenated or assigned one source hash merely because they share a module name. The compatible and coherent canonical aggregate environments are separately pinned. Cache reuse requires exact source, import, object/IR and runtime bindings. The package's historical `remaining49` command depends on old run records and is not the download/reproduction route.

Use one compiler. Ordinary checks use `-j1 -t0 -M4096 -Ddebug.skipKernelTC=false`. Only the exact two aggregate/audit pairs use 6144 MiB, with their original 300/180-second per-invocation bounds; the earlier exact ThetaCertificate5 exception retains 6144 MiB/600 seconds. The qualified wrapper checks memory headroom and stops on pressure. The original default `connected` command is preserved and can reproduce the older 4096 MiB aggregate failures. Preserve unsuccessful attempts and distinguish resource errors from theorem failures.

The qualified entrypoint emits its own run identity, actual freshness and `RESOURCE-QUALIFIED-FINAL.json`. Do not import the old 53-pass status into a new run. Practical extraction or executable smoke tests require their own results; kernel proof checking and runtime execution are different evidence.

## Exact checked boundary

The compatible aggregate covers 1,124 selected modules, 93,129 owned declarations and 86,621 theorem declarations. The canonical aggregate covers 1,411 modules, 97,873 owned declarations and 89,920 theorem declarations. Both complete audits report zero owned axioms, nonstandard-axiom rows and missing selected modules. Their counts overlap and are not additive unique theorem counts. The census records every owned declaration's kind, axiom dependencies and type/body references; it is not itself a full serialized type/body equivalence proof.

The final 53-profile reauthentication has SHA256 `6eb30829e2ed81129c11a31f5caec12aa79b7f0ac1e15bb3a631e89be2be9c48`. Exact component and audit pins are in the public certificate. Standard Lean axioms remain explicitly reported. Original hypotheses, historical failures, provenance and source versions remain preserved.

## Integrate later checked packets separately

These packets provide supplementary verification or later checked extensions. Later mathematical extensions were not silently inserted into the frozen 53-profile graph:

- [G2 current-source verification](https://github.com/Sodelin/Research-Commons/blob/e20f1516fb25e2cba9a0b6461416075811b8b87e/research/2026-10-10-dot-g2-current-source-verification-0042z/README.md): 166-module context; all 68 current G2 modules have a complete type/body DAG audit. It retains the explicit classification of two partial runtime companions and the missing historical 43-source-body comparison. Runtime behavior is not certified by that structural audit.
- [G5 binary M3 cluster/split chain](https://github.com/Sodelin/Research-Commons/blob/81ff60aa0ffe6c39e15546b09105f3c3fafbd1ed/research/2026-10-10-dot-g5-full-binary-m3-0209z/README.md): 319-module checked context, 6,448 declarations/4,386 theorems. Preserve the exact binary/root-LSA/contemporaneous/strict-parameter assumptions and the precise normalized cluster/split conclusion. The optional quartet corollary and stronger co-occurrence/hidden-parameter claims remain separate.
- [G6 completed-cell and observed-TV consumers](https://github.com/Sodelin/Research-Commons/blob/de3011fa352e04f9be64cf9f4da8a5528cad68db/research/2026-10-10-dot-g6-completed-cell-tv-0258z/README.md): 233-module cell context and 236-module fixed-graph, same-cell unconditional-TV context. Positive source realization and full master-G6 closure are not consequences of these passes.
- [G6 protected-bin, guard-erasure and unranked-continuation bridge](https://github.com/Sodelin/Research-Commons/blob/2e625f740c18d18742cbfa2eed63a6a98a43a697/research/2026-10-10-dot-g6-protected-bin-bridge-0912z/README.md): 319 modules, 6,386 declarations/4,214 theorems, three new scoped components. This retains the same-record old-bin, original guard and causal-interface conditions.
- [Earlier accepted G7 completed-calendar polynomial packet](https://github.com/Sodelin/Research-Commons/blob/032bdb55f2e5ddd21d7c2dcc67d36b8e4cdb28fb/research/2026-10-09-dot-g7-completed-calendar-polynomial-2330z/README.md) remains usable at its exact recorded scope.

Reconstruct each later packet's exact dependency context before adding it to a new aggregate. A new aggregate requires its own complete audit and certificate. Existing G1/G2 source results should be reused before attempting equivalent new proofs.

The [G6 full-forest exposure handoff](https://github.com/Sodelin/Research-Commons/blob/1e4effdc8ad14233acc2624c82b698ec717dc790/research/2026-10-10-dot-g6-forest-exposure-handoff-0941z/README.md) supplies separately reviewed hand/source arguments and the unfinished positive-source assembly. It is not a new Lean pass. Its forest-only exposure theorem is separated from joint-bin and guarded-future corollaries with their explicit old-matrix, tag, original-registry, exit and guard contracts. Preserve those distinctions when formalizing it.

## Pending recovery belongs to the receiving Codex build agent

The [preserved integration handoff](20261010T030600Z-INTEGRATION-HANDOFF.md) records the three later G7 candidate chains. The executable enumeration and population-coefficient components passed individual checks, but the full-epoch component still failed; the chain audit and executable smoke are unrun. The whole-edge operator chain and the five-source semantic-policy chain also stopped at recorded failures before their complete audits. Neither a source review nor a partially checked prefix makes any of these chains pass.

Their latest failed/uncompiled source versions and exact repair manifests are being prepared as a separate recovery packet. They are outside this frozen modular graph. Recover the existing diagnostics, preserve executable bodies and hypotheses during elaboration repairs, then run isolated bounded checks and full audits. Do not infer coefficient execution from symbolic proof compilation. The pinned official FinEnum dependency uses an isolated complete Mathlib namespace overlay; a sparse earlier namespace must never be admitted using a later-path fallback.

All local historical/interrupted operational archives remain preserved, but this delivery does not claim every such raw archive is public. Its scientific source, exact full aggregate audits, qualified receipts and disposition inventories have the explicit publication boundary described in the README.

## Research allocation and full-scope boundaries

After this delivery, the existing four research routes return to:

1. G3 constructive original-source realization.
2. G3 exact obstruction/NO-completeness analysis.
3. G4 finite forcing and invariants.
4. G4 exact rivals and counterconstruction.

The separate Codex agent owns full Lean and practical-build continuation. These research routes add no parallel compiler work here. G4 retains the full quantifiers: effective finite original tests for each supplied admitted algebraic target against all unknown-size strict real rivals, or the fixed-target exact all-prefix alternative. Finite-menu algebra alone is not that master conclusion. G3/G4 routes must recover their exact [canonical scope](../../research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md) and accepted prior results before choosing a construction or obstruction.

No scoped component or 53-profile build closes all master G statements, establishes unresolved novelty, gives a hidden-size bound, or proves an executable stopping rule. Keep positive original-source realization, quantitative approximation, algorithmic extraction and formal checking as separately evidenced obligations. Preserve all prior work and attribution; do not weaken hypotheses to obtain a build pass.


## 2026-10-10 09:56 UTC — G7 recovery sources delivered

The previously pending [G7 source/diagnostic recovery packet](https://github.com/Sodelin/Research-Commons/blob/95fdd74783c0f0759e753b5486a85c5c9cf55928/research/2026-10-10-dot-g7-pending-codex-recovery-0952z/README.md) is now preserved at immutable commit `95fdd74783c0f0759e753b5486a85c5c9cf55928`. It contains 18 mathematical candidates, 219 exact source versions/providers, three latest isolated contexts, ten historical graphs and compact records/diagnostics for 14 actual candidate or official-provider attempts across 11 incomplete runs. Prepared audits and the coefficient smoke remain unrun. All 964 public blob paths were checked against their identities; repeated source-store paths share the same 219 exact versions.

This supersedes only the earlier “being prepared” delivery status. The semantic chain, full-epoch coefficient chain and whole-edge chain retain their explicit failed/uncompiled boundaries. No candidate was added to the frozen 53-profile graph, no new compiler was invoked and no failed result was promoted. The receiving Codex agent owns any further source recovery, coherent repairs, complete audits and practical execution tests.
