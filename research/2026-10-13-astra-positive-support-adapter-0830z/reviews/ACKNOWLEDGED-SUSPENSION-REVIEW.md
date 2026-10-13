# Acknowledged suspension review

Reviewer: Astra Rust integration lane, 2026-10-13. This records the completed
read-only source/diff and receipt review. No compiler, test, or new investigation
was run to write this note.

No PID-ownership or cleanup regression was found. After a successful SIGSTOP
request, the helper does not reap the compiler before the `finally` SIGCONT.
It waits at most one second for observed `T`, `t`, or `Z`; timeout and status,
logging, or advice exceptions traverse resume and then the existing child
termination path. The frozen outer guard also unconditionally kills the
remaining process group, including stopped workers, when it stops an invocation.
Advice still uses the authenticated read-only inputs and excludes active outputs.
Source bytes, compiler options and memory limits are unchanged.

The observed state comes from `/proc/<pid>/status`, which reports the thread-group
leader. It does not prove every thread has acknowledged suspension. `Z` likewise
records the observed leader state, not an independent all-thread exit proof.
The outer resource guard remains authoritative. These observations and the
finite test cases do not establish a universal memory or scheduling guarantee.

The shared helper retains its3GiB advice threshold and uses a0.2s minimum
interval; the earlier successful diagnostic used2.5GiB and only recorded
suspension requests. The repair preserves that distinction and its historical
receipt. The adopted2145 receipt and objects matched the repair record.

The six-test v4 guard receipt and both logs were hash-authenticated, not rerun:
exit0, no stop, guarded elapsed1.002s, peak RSS20,566,016bytes. The tests include
an actual stopped leader observed during advice, successful resume, failed-advice
cleanup and broken-logging cleanup. Batch030 also had matching receipt/log
hashes: exit0, no stop, guarded elapsed19.017s, three observed `T` events, one
fresh module and2146 authenticated reuses. Its `complete: false` is retained;
this is not full external or provider completion.

| File | SHA256 |
| --- | --- |
| `serial_compile.py` | `d47f2d50afd4648374d7ca1630dce71f3aa09422fe740d356b2d0d9c8ce8ca28` |
| `test_serial_compile.py` | `33674153dc39a274bbacac16250bdf389a6d14ffe0c081529dc18ae9a1acc995` |
| `evidence/ACKNOWLEDGED-SUSPENSION-REPAIR.json` | `82761f8d3abdafd16adbbd2398a0e380b4cc1f4ad336b7baf4c20d0c3e74cc8c` |
| `evidence/resource-helper-tests-v4/RECEIPT.json` | `64e5b9431a7e881f9261dcbd74dfdd7e651109ae5717fa159af97aa464aa4bc5` |
| `evidence/external-batch-030/RECEIPT.json` | `a0a338f38f539ea017bfeabe8fd9c48e10551c1d27991e7af04fedd99c6c640b` |
