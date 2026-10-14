# Detached owned-provider batch: source-only draft

No launcher, builder, driver control, compiler or import query has been executed for this packet. The driver is prepared for root/Lean review and their exclusive compiler ownership. It must not interrupt active external compilation or start an owned pilot while the external closure remains incomplete.

`one_owned_batch.py` reuses the exact tested detached transport `4c396546…`, the existing `one_batch.py` launch/status/stop/finish protocol, and the reviewed namespace builder `2d5c8504…`. It adds no process transport, decoder or mathematical source. `SOURCE-PINS.json` pins the nine-file namespace successor snapshot, its exact imported helpers, selected provider/external plans, source-selection records and predecessor protocol. It now also pins the published `one_batch_small.py` (`89b335b1…`), whose process name is included in the occupancy check. The complete initial `ae19be41…` driver, pins, review and manifest remain unchanged in `initial-draft/`.

The separate namespace suite has since passed 16 bounded non-Lean controls at [publication f80665bff](https://github.com/Sodelin/Research-Commons/commit/f80665bff34c30ccca052d4aa232874279e49b07); `NAMESPACE-CONTROLS-SUCCESSOR.json` pins that actual verification and guard receipt. This authenticates reuse of the unchanged namespace source snapshot. It does not execute or validate this owned driver, authenticate production objects or compile the provider. Root's review found no blocking driver flaw; its only implementation followup was the additional scheduler name. `CONTROL-PLAN.md` describes the narrow future driver/capture controls; none has run.

Fixed paths:

| Purpose | Path |
| --- | --- |
| Selected source | `/workspace/scratch/astra-support-sources-0936` |
| External state | `/workspace/scratch/astra-support-external-0840` |
| New owned state, agreed with Lean | `/workspace/scratch/astra-support-owned-namespace-0025` |
| Mathlib | `/workspace/scratch/astra-mathlib-0645` |
| Toolchain | `/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin` |

The first pilot requires the new owned state to be absent. No previous owned state is reused, rewritten or cleaned. Later batches require this driver's immediately preceding verified `FINISH.json` and the explicit matching receipt index. A failed or interrupted batch requires review and an explicit repair; this driver does not retry or select another batch.

There is one guard per explicit launch, with at most 16 fresh compiler invocations, 6 GiB virtual address space, the unchanged 4 GiB cgroup stop, 900 seconds wall time, 600 CPU seconds, 1 GiB per file, 8 GiB free-disk floor and 1 GiB available-RAM floor. Only `--prepare-provider` is requested. The new adapter and actual final Lake/audit stage remain separate.

Before launch, the driver checks exact source/configuration pins, an idle compiler lane, the frozen external plan and all 3591 contiguous successful receipt metadata records with matching log filenames. This is a **preliminary refusal gate, not object authentication**. No full-object hash job runs outside the guard. The pinned `build_support_namespace.py` is the authoritative gate: under that guard it verifies the complete selected source/log/object state and namespace routes before any owned compiler invocation. A receipt count or a successful launch cannot establish this authentication.

The transport preserves intent and preinventory before launch. Its PID identity and pidfd stop behavior remain unchanged. Launch means outcome UNKNOWN. OS guard exit remains unknown after detachment; the terminal receipt reports the builder's exit code. A guard exception, requested stop, missing receipt or changed identity cannot be promoted to success.

After the exact guard is no longer running, finish first preserves `OWNED-STATE-DELTA.json`: changed indexed receipt/log bytes, copied original selected Lean sources, missing paths, exact PLAN and NAMESPACE records, without binary object bytes. This occurs before parsing the terminal/capture results. Ordinary builder failure retains completed invocation evidence and eventless unverified bytes through the existing capture helper. Guard errors and requested stops retain the full delta without invoking that helper's success branch. Capture failure is itself written to `FINISH.json` as unverified.

On successful guarded execution, finish separates fresh compiler invocations, newly cloned authenticated reuse receipts and previously resumed receipts. The builder's cumulative `authenticated_reuse` summary is not described as the number of newly cloned components. New sources must match the saved selected bytes. Provider readiness is reported only after the guarded builder succeeded; no final Lake target, new-adapter audit, full1613 aggregate or physical representative is thereby claimed. Capture does not independently rehash all compiler objects.

Future owner commands, **not run**:

```sh
python3 -B one_owned_batch.py launch --batch-id 1 --start-index 0 --fresh-budget 1
python3 -B one_owned_batch.py status --batch-id 1 --start-index 0 --fresh-budget 1
python3 -B one_owned_batch.py finish --batch-id 1 --start-index 0 --fresh-budget 1
```

The same explicit arguments identify `stop`, which delegates the existing guarded pidfd protocol. An owner reviews each closed result before choosing the next index/budget; no automatic next batch exists. Production execution and any new composition controls require the current compiler owner's release. Static source parsing is the only validation recorded here.
