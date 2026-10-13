# Independent readback: thread diagnostic, adoption and batch 055

Contributor: Astra Rust integration lane, 13 October 2026 UTC. This review
launched no Lean/Rust compiler and made no adoption, source or policy change.

The unchanged selected module 2860 compiled under the explicitly revised
6 GiB virtual limit. The frozen physical guard remained 4 GiB. This establishes
the recorded executions, not the exact cause of the earlier pthread failure.

| Record | Actual outcome | SHA256 |
|---|---|---|
| Original batch 054 guard | Exit 1; no guard stop; module 2860 compiler -6, `failed to create thread` | `045b049a341fa59928c59acd8e93d3bcb1edc8fdced176de8102bfce95eff5cc` |
| Diagnostic v1 guard | Compiler 0; diagnostic/guard 2 because required extra process observations were absent | `2deff44122fa3f91a0d353967f1cb2016e5e9787397d2094895d29e86b73cc8a` |
| Diagnostic v1 result | Five authenticated artifacts, empty compiler logs; zero extra monitor samples | `c991bf2e6ba2e814deb2d56a2373bffc2523426003c211c1c483e45d81edca7a` |
| Diagnostic v2 guard | Compiler, diagnostic and guard 0; no stop; 33.039 seconds | `851ba3fc78c41c9f3181857d89add49ea1725fa925c6d3152fafd71d34181dce` |
| Diagnostic v2 result | Five authenticated artifacts, empty compiler logs, 375 samples and 25 child limits/maps snapshots | `4f4a6d8932f405979d02f02b766d85063686875a17ec40e57a5f7ec195110e8f` |
| Explicit adoption guard | Exit 0, no compilation; 0.502 seconds | `179dc1e900f0c05f717ef4a4aa7deaac1fb79cc6130f55f6fc95e4943a591461` |
| Adoption record | Original failed receipt/logs archived; v2 receipt installed explicitly | `1422ff489814444e5ca22ad33e6c48606f1251afe411fc2941b7f26b27311ee0` |
| Batch 055 guard | Exit 0; one fresh module 2861, 2861 authenticated reuse; 38.040 seconds | `51a9147ea780dd883502817b70b12551aa2218afbaca5b13a0083e56eac0f7c2` |
| Batch 055 capture | Source/import selection, command, logs, receipt and five objects independently rehashed | `7435dd6a75fcd6206a878866e543a4fc1a4bba68bf5feac7227d1d043fc8a738` |

The reviewer checked actual diagnostic source/compiler/options/helper/plan
identities, outer and compiler logs, five artifacts per successful diagnostic,
and the 2860 prior receipt hashes. V2 child snapshots record address-space
soft/hard limits of 6,442,450,944 bytes, 120-second CPU limits, and an 8 MiB soft
stack limit. The outer receipt records the unchanged 4,294,967,296-byte physical
stop. Shared-helper peaks were VmPeak 6,039,928,832 bytes, RSS 1,574,010,880 bytes,
and cgroup 3,334,369,280 bytes. Recorded OS OOM counters remained zero.

V1 failed because `/proc/<pid>/task/<tid>/children` is absent in this environment.
A read-only probe found `/proc/self`, numeric PID and NSpid consistent; this is
not evidence of a PID namespace mismatch. The source repair changes discovery
to numeric `/proc` entries filtered by parent PID and exact executable, retaining
the immediate identity recheck before observations. Its bounded non-Lean test
passed, including owned-child filtering, actual process files and absence after
reaping. Monitor repair source:
`2648d7e48979c1c241fe2563b7ea40c98034a38d2a0cbe15b535718ac5c5baf9`;
test source `7ef6b5ff1f8ab717f2c0fa62e969c5d3a3d447ca44248d07474dd46519cd75aa`;
test guard `f7895b28b385b0c7bd56412041d455678b5b9ca4023de197ea5daec861c6cfa3`.

The adoption source
`da3e74856f8fc9f73d1627d804d9b660fa62d2d60d3401c05964e631a889a3a6`
requires the exact successful diagnostic and prefix ledger. The archived failed
receipt remains `05d682973501c3af2a74bd4d6b8b3015741d7ca32d58cbcb258b273992dd456d`;
the adopted receipt is `aa778c902a1158232b4e308872d7326bf864816959d4096aff5a988b94b8cb76`.
Original batch 054 guard/capture and the mixed v1 guard were rehashed unchanged
after adoption. The historical process detector predates the new launcher;
the coordinator's separate extended no-active preflight is required for that
launcher's precompiler interval.

The new external launcher
`11e3fd84ca11692760ecd428801e176b666e4b19f7fb2bcbd04169de7970713c`
differs from the frozen 5 GiB launcher only in its explanatory docstring and
the explicit 6144 MiB virtual-limit argument. Physical/time/disk/source/helper
controls remain unchanged. Batch 055 tested one fresh selected module under
that external profile; it does not prove the rest of the closure will fit.
The next unresolved prefix index is 2862. Provider/final Lake execution and
interface/type audits are still separate pending obligations. Original batch
042's outer guard remains **UNKNOWN**; its later recovery authentication is
separate. This review does not establish remote publication of new records.
