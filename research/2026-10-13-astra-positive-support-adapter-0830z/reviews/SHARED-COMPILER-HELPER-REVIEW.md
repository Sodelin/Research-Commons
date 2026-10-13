# Shared compiler helper: scoped source review

Reviewer: Astra Rust integration lane, 2026-10-13. No compiler, test child or
cache operation run by this reviewer. Existing source and receipts were read.

The reviewed runner diffs preserve the selected source/import authentication,
receipt reuse checks, synchronous Lean command and unchanged outer guard.
External inputs accumulate only after their receipt/artifact authentication or
successful fresh compilation. Owned inputs come from the verified external
objects and accepted owned object inventory, with newly authenticated copies
and freshly compiled objects added after success.

`serial_compile.py` freezes a sorted input list per invocation, excludes all
five active-output suffixes, opens advice inputs read-only, and sets
`MALLOC_ARENA_MAX=1` only for its child. Toolchain file symlinks must resolve
inside the toolchain library. Source or object bytes and global settings are
not written by the helper. The independent guard retains responsibility for
time, physical memory, address space and process-group termination.

Resource policy/begin/end events use `resource_index` and `resource_module`,
so the existing capture parser does not misclassify them as module completions.
The helper records its loaded source hash, input-inventory hash and count,
advice threshold/interval, and that sampling pauses during advice. Both runner
receipts retain the returned resource policy. The new external runner also
rejects unreceipted target artifacts before starting a compiler.

## One concrete cleanup edge

In the reviewed helper, `except BaseException` emits `RESOURCE_HELPER_ABORT`
before terminating/waiting for the child. If that logging operation raises
(for example, broken stdout), helper-local cleanup is skipped and the original
exception can be replaced by the logging failure. The required outer guard
still supplies process-group cleanup, but the helper's own cleanup guarantee
is incomplete. Make abort logging best-effort and put termination/reaping in
an unconditional cleanup path, preserving the original exception. A bounded
non-Lean test can combine a missing input with failed abort-event logging.

## Existing validation and repair evidence

The three existing helper tests passed under the guard. They cover active
output rejection before child launch, child environment/output and unchanged
input bytes, and child termination on a missing-input exception. They do not
cover the failed abort-log edge above.

Completed batch018 freshly compiled index1896, `Mathlib.Algebra.Star.Pi`, in
1.631 seconds using this helper, authenticated 1896 previous module receipts,
and retained `complete=false`. The guard exited0 with no stop. Its actual
stdout/stderr hashes agree with the recorded outputs. This demonstrates one
successful new-runner invocation; it does not establish closure completion.

The index1895 state repair retains the batch017 interrupted evidence. Its
recorded previous capture hash and replacement receipt hash match the actual
files. The successful measured diagnostic remains distinct from both the
earlier interruption and the new shared-helper run at index1896.

| Reviewed source or evidence | SHA256 |
| --- | --- |
| `serial_compile.py` | `2c94cb4be0d83babd765d70c54244a85edd825155336263605ebde85c195a086` |
| `build_external_serial.py` | `4c3ea4206bd80900a687d4a229d2b45ceb2e6027a69f7794615fa05ef0b35e6e` |
| `build_support.py` | `f9d1567dc09f7322928a048c433199b83d2cf60c7d1e31bd8e2fac92ca823026` |
| `evidence/ARENA-AND-INPUT-CACHE-REPAIR.json` | `9b015d950f5481dbae479c1f112efb3067d6f8507f7ee321c4768d71211f6d95` |
| Replacement state receipt `1895.json` | `aa9924ec75e7de9ca3e8b3547f839adcbb29e3d797e2f05af0ea27f7db458983` |
| Original batch017 `MODULE-RECEIPTS.json` | `fd3b02bfce384114d8c68bbedca996c3dbbe5fe96dff93643d16dbf29220bd18` |

Source changes resolving the cleanup edge require new hashes and their own
validation; earlier successful receipts must retain the helper hash actually
loaded for those executions.

## Cleanup repair follow-up

The revised helper makes abort-event logging best-effort before child
termination/reaping and the bare re-raise. Its exact source is
`c495482f4f6118de0d4eb5d26ff511b1b80ef1db071a223a52b7d55c740fd873`.
This addresses the concrete cleanup edge above without changing the guard,
compiler command, source selection or input-cache policy. No additional
blocking issue was found in the scoped follow-up.

The added regression allows the policy event and child launch, then makes
both advice-begin and abort-event logging fail. It checks the raised
`BrokenPipeError` and that the child was reaped. All four tests passed under
the existing non-Lean guard in 0.502 seconds; recorded stdout/stderr hashes
match their actual files. The reviewer read this evidence rather than
rerunning tests. Test source SHA256:
`f8cab634f36e3706f1b72b3ad14039e29640335ddf2bf8ba8c05b9d44c31a3f2`.
Receipt `evidence/resource-helper-tests-v2/RECEIPT.json` SHA256:
`cda69e16a811beee47828bdaca71a0b98d7906bb1db34fd6e2408b6c0911cb25`.
Batch018 correctly retains its earlier loaded helper hash; no new Lean
compilation is inferred from these four bounded helper tests.
