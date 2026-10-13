# Independent batch042 recovery review

Reviewed by the Rust integration lane on 2026-10-13 after the original cloud
environment reconnected. This review launched no compiler and changed no
implementation, selected source, build configuration, or resource limit.

The recovered stdout contains exactly 32 successful module events for indices
2499–2530 and a `BATCH_COMPLETE` summary with 32 fresh compilations and 2499
authenticated reused modules. Independent readback checked all 32 selected
source bodies and import metadata, recorded commands, runner/helper identities,
64 compiler logs, and 160 compiled artifact hashes. These 32 receipts were absent
from the original prebatch inventory. This authenticates module evidence; it
does not recover the missing outer guard receipt.

Original `external-batch-042/RECEIPT.json` and `MODULE-RECEIPTS.json` remain
absent. `ORCHESTRATOR-040.json` remains pending at042. Its digest agrees with
the retained monitor row at13:14:13.308319UTC. The monitor has no completion
row. The completed042 stdout and the monitor's whole-file digest were first
explicitly authenticated during recovery, including readback at18:54:31UTC;
they are not pre-disconnection attestations. The interruption cause, original
outer exit status, elapsed time, and resource maxima remain unknown. Per-module
sampled peaks do not supply the missing outer measurements.

The initial recovery-script review requested explicit historical snapshot pins
and direct checks of preceding capture implementation/preinventory fields
omitted by the generic existing-capture validator. The final script includes
both repairs. Static inspection found no Lean invocation or overwrite of the
original evidence. It checks the exact2531-module prefix, source/toolchain and
dependency identities, logs and objects, import shadowing, unchanged prebatch
evidence, exact32 new events, and absence of subsequent planned objects. Its
new output directory preserves copies and records the original guard as
`UNKNOWN`; AST parsing also passed.

The actual new guarded readback passed with exit0, no stop, 7.006779699s elapsed,
and32,460,800bytes child peakRSS. Its limits were300s wall,120s CPU,1GiB virtual,
4GiB physical stop,1GiB file limit,8GiB disk floor, and1GiB available-RAM floor.
These describe the authentication run only. Independent verification checked
the guard's output hashes, stdout-to-result binding, result-to-ledger and
configuration bindings, and all137 captured files against `FILES.json`.

| Evidence | SHA256 |
|---|---|
| `recover_batch_042.py` | `9c67bbe90b2e64686ac361593345b6053b1d390b32efa161a548da1246ba4343` |
| Original042 stdout | `5af434c2700edda6b162668caabe3e9476eecf51259704e43923fedb4ef59b9a` |
| Original pending orchestrator | `bd52c3a5295479bfa44a34be79608d4ea3f28021923657b84b2eec3498fdf2d8` |
| Retained monitor | `04f6cac56754d31101a0f3ca53ebff7a79d5d08d20d585859b39939984f98da3` |
| `evidence/recovery042-auth-v1/RECEIPT.json` | `6648974a1440dffd84d61937f3c62fe79a5b29f2c8a20a8820dfb6a85c2cf4c9` |
| `readback/RESULT.json` | `bd839025e06b6eac1cd0925091e09df32bd27a78e9893d81e2599c2fa68af1be` |
| `readback/FILES.json` | `99004f283b563655a07dd44f535ea92e73ac913f99fbeaedde38125d85995b02` |

Recovery compiled zero modules. The authenticated external prefix ends at2530;
the next selected index2531 is `Mathlib.MeasureTheory.Measure.Typeclasses.SFinite`.
The complete external plan, provider/adapter compilation, interface/axiom audit,
and remote publication are not established by this recovery review. Further
compilation remains under coordinator control. No statement about arbitrary
input solvability or universal native-code correctness follows from these checks.
