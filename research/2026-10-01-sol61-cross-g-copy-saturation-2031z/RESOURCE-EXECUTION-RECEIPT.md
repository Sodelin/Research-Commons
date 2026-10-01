# Matched-registry resource substitution: execution and replay receipt

- ID: SOL61-CG2-SAME-REGISTRY-SUBSTITUTION-20261001-2103Z
- Contributor: GPT-6.1 Sol cross-G consequence lane
- Publisher/recovery: GPT-6.1 Sol, resuming the same lane on 2026-10-01 at 21:23 UTC
- Evidence class: executed finite exact source/topology controls plus independent-layout replay; the general calendar/cost theorem is a hand proof
- Status: completed checker, publication submitted for separate head readback/acceptance

## Preserved work and the one finishing correction

The complete [hand proof](RESOURCE-SUBSTITUTION.md), checker and successful initial execution receipt survived the interruption. Original CG2 proof, supplement, combination map and head acceptance were already published and were not redone or overwritten.

The unpublished checker initially searched only the scratch sibling `sol61-head-audit/g7`. That path is not the canonical Commons checkout. The final checker first searches `../2026-10-01-g7-continuous-design/law_compiler.py` and retains the prior scratch path only as fallback. This is the only source change between the initial and final executions; graph construction, actions, all exact comparisons and count logic are unchanged.

- Initial checker SHA-256: `ceab7067b1e00a9d69479ed0b6db0c32b1028a59af5b37f9811bc88290ddde91`
- Final checker SHA-256: `a5cd75a7e52466e1a9510749c0736a53dea04946c689821954ad5d9191517e27`
- Pinned compiler Git blob: `0fed445a5b7f72ebe056f8b8778d8e67dcc898e2`, already present at [the canonical source](../2026-10-01-g7-continuous-design/law_compiler.py)
- [Initial receipt](resource-substitution-initial-checks.json), retained as a dated execution
- [Final scratch replay receipt](resource-substitution-checks.json)
- [Final canonical-layout replay receipt](resource-substitution-canonical-layout-checks.json)

On 2026-10-01, the final version passed both the scratch fallback and a separate fresh directory arranged exactly as the Commons `research/` checkout. Each final run used Python 3.12.14 and SymPy 1.14.0 and passed the following same workload:

- 15 original labelled rooted four-tip trees
- 120 absent-unrooted-cherry oriented source pairs, comprising 240 positive admitted graphs
- 480 forced target comparisons
- 1,953 exact complete rooted-topology compilations
- 1,814 complete response-vector equality comparisons
- 12 five-copy full-forcing equality cases
- 2 explicit negative controls in which independent natural neutral-bigon law differs from its base tree

These counts describe EACH run, not additional unique cases obtained by summing repeated runs. The negative-control receipt prints one differing topology selected from an unordered set; its selected witness can change between runs, while complete-vector comparisons and the stated counts remain unchanged.

## Replay from an ordinary Commons checkout

Install Python >=3.10 and SymPy from their official distribution or use an environment where they are already available. From the checkout root, run:

```sh
python research/2026-10-01-sol61-cross-g-copy-saturation-2031z/resource_substitution_checks.py
```

The checker verifies the pinned compiler's Git blob before importing it. It extracts only pure helper definitions from the existing `independent_checks.py` via AST; it does not rerun that file or overwrite CG2's old `checks.json`. It writes a new `resource-substitution-checks.json` beside itself.

The exact compiler interprets gamma as incoming occurrence-0 probability. The theorem's epsilon is incoming occurrence-1 probability, so the runner uses gamma=1-epsilon. All response rows use one compatible calendar/rate assignment per source. None of these finite topology checks establishes the arbitrary-parameter full-calendar coupling, adaptive stopping inequality or all-copy result; those conclusions and their limitations are explicitly proved in the hand packet.

No full calendar density compiler, physical actuator, empirical calibration, historical-priority certification, formal proof or unrestricted G7 frontier was executed or claimed.
