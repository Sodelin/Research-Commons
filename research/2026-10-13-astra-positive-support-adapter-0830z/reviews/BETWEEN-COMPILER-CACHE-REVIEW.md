# Between-compiler cache review

Reviewer: Astra Rust integration lane, 2026-10-13. Read-only source/diff review
and receipt authentication; no compiler or test was launched by this reviewer.

No semantic, active-output, or child-cleanup regression was found in the narrow
change to `serial_compile.py`. The added sweep runs after `child.wait()` and
after the compiler log handles close, only for exit0 and cgroup usage above2GiB.
It uses the same sorted authenticated input inventory. All five active output
paths remain excluded before child creation. Each input is opened read-only,
flushed and given `POSIX_FADV_DONTNEED`; no source/object bytes, global setting,
compiler argument, or outer limit changes. The existing during-child cleanup
path, including best-effort abort logging and unconditional child termination
on helper exceptions, is unchanged.

Begin/end events retain `resource_index`, so generic capture does not confuse
them with successful module-completion events. Post-exit advice occurs inside
the guarded invocation and its elapsed time remains in the helper duration.
If post-exit advice or logging raises, the compiler is already reaped; the batch
fails without publishing a successful module receipt. Resulting unreceipted
objects and compiler logs require preservation and explicit repair under the
existing policy. The new path does not silently promote that situation to a
verified success.

The archived previous helper/test sources, current helper/test pins, failed027
guard/capture, preserved empty2141 logs, repaired2141 receipt, unchanged
ChangeOrigin source, five object artifacts, diagnostic result/guard and log
hashes all matched the repair record. The clean-cache diagnostic's compiler
elapsed11.845s and guarded elapsed13.513s at the same5GiB virtual allowance and
4GiB monitored physical stop. Its success does not isolate the cause of the
earlier surge or say anything about the user's hardware incident.

The existing v3 test receipt and both output hashes were authenticated, not
rerun. It records five passing small-child tests, including advice only after
child exit and the earlier broken-logging cleanup regression; guarded
elapsed0.502s and peak RSS20,512,768bytes. Batch028 also has a verified guard/log
receipt: one fresh module,2142 authenticated reuses, `complete: false`. Its new
after-exit event records cgroup usage2,498,912,256→1,516,101,632bytes over1.478s.
This is a bounded observed continuation, not full closure or a universal memory
bound.

| File | SHA256 |
| --- | --- |
| `serial_compile.py` | `e6bde9e36ec348c15cdb52b7737d9120aa0b943d3e2bf955b7061b3b86eaddb0` |
| `test_serial_compile.py` | `8e7906e2d3383311a572688b143540489c4c0726b162fd511af5ca1bd600444a` |
| `evidence/BETWEEN-COMPILER-CACHE-REPAIR.json` | `eefab267144ad6a26fbfa9242b340a4cceed61660d20f670822747a158595352` |
| `evidence/resource-helper-tests-v3/RECEIPT.json` | `80b918f6af627abba7690da3875fc2324ee0d631d1d05460c3eef6e37932b7db` |
| `evidence/change-origin-clean-cache/RECEIPT.json` | `131a4de57eb4598f24b208a29cfdb50bf4ac9a28565188381509481538b045ac` |
| `evidence/external-batch-028/RECEIPT.json` | `b0473801e505336bf260e0a9acf7ab59ce456b8b5a8e8695f6f028f0e0ce3058` |
