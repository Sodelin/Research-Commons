# Synchronous elaboration repair: scoped source and receipt review

Reviewer: Astra Rust integration lane, 2026-10-13.

**No blocking authentication or compatibility regression found in this narrow
repair.** The reviewer read the new external runner, compared the two modified
runners with their preserved predecessors, and checked the repair's existing
source/receipt hashes. No compiler or tests were run for this review.

`build_support.py` differs from its immediate preserved predecessor only by
adding `-DElab.async=false` to the Lean command. The orchestrator changes its
compiler-runner path to `build_external_serial.py`; its guard remains at the
4 GiB virtual ceiling and 4 GiB physical cgroup stop, with the previous disk,
RAM, wall and CPU limits. Serial batch scheduling and evidence capture remain
unchanged. This modifies elaboration scheduling, not the selected Lean source,
theorem statement, or axiom allowance.

The new external runner requires byte equality with `EXTERNAL-PLAN.json`,
authenticates the frozen helper and previous manifest, and checks pinned
compiler/dependency context. Reuse requires the exact planned source hash,
every planned receipt field, successful exit, a present `.olean`, matching
artifact hashes and matching compiler logs. Failed or changed receipts still
stop execution for an explicit repair. New receipts distinguish synchronous
fresh compilation from authenticated reuse and retain the command and runner
hash. Previously successful asynchronous objects remain reused under their
original receipts; the runner does not describe them as freshly recompiled.

The index1734 repair retains the original failed receipt and its output in
batch013, archives the former state receipt, and binds its replacement to the
successful diagnostic result and guard receipt. The copied source hash is
unchanged. The reviewed hashes agree:

- Source: `5622789fad49c260ae51bcb1f8791d631d7a69919bf96e9991e636dd44f6878b`.
- Archived failed receipt: `f263383d1d969244761350b3aee26cc0e156e5f1f039200f83c3f35331dfc775`.
- Replacement state receipt: `5adc9951731bff39fa40590d90b682a9fd09e025b568020ecc1104080c024a53`.
- Successful diagnostic result: `2f9c3391c1c63a21d31aa8c61862c7da1d182d75e2101ff534ba55dbc3a38dee`.
- Successful diagnostic guard receipt: `7c3fb964d69c62dcd9ed37565db7f985f19018693fe5df1b8c40b2e5772b77ee`.

That diagnostic records exit0 in 6.124 seconds, sampled VmPeak 3,688,873,984
bytes, sampled RSS 973,647,872 bytes, six threads and unchanged zero cgroup
OOM counters. These are observations from this cloud invocation, not a cause
attribution for the user's desktop incident or a guarantee for other modules.

The completed narrow batch014 provides an additional actual compatibility
receipt: the new runner authenticated 1735 existing module receipts and freshly
compiled index1735, `Mathlib.Topology.EMetricSpace.Lipschitz`, with the new flag
in 4.385 seconds. Its guard exited0 without a resource stop. Actual stdout and
stderr hashes match the guard's recorded hashes; the module capture records
the new runner and command. The summary correctly retains `complete=false`.
This establishes one successful follow-on invocation, not completion of all
3591 planned external modules or the accepted-provider/adapter build.

| Reviewed file | SHA256 |
| --- | --- |
| `build_external_serial.py` | `21b554bebd880942fda678646a74f4da3399a9352244d5e2df04bcd7c3ecdc34` |
| `build_support.py` | `3a7e2ee88dfb124d2184fe2504882fbcc7a47b31ecc35f594da9bb241340d9e5` |
| `run_external_batches.py` | `2a04e1ccbb929989cf4604db03c893178ab39b6e89b8c3ad2c4c63aaf32c7ecb` |
| `evidence/SYNCHRONOUS-ELABORATION-REPAIR.json` | `ed978689b374f55bca28ec4935e25ca65cb1074901a3c5a979cbcd6aef26e445` |
| `evidence/external-batch-014/RECEIPT.json` | `38605039944c35f1fbb0676bdc0cef2d2e09aed397caf1edc11697acb1e0edb3` |
| `evidence/external-batch-014/MODULE-RECEIPTS.json` | `cee4df42ae8bcbb901d72e9546c6c80a8781c48e156888426cacb8cf0a6760c3` |

Continue retaining the literal failed batch013 capture when reporting history;
its index1734 failure must not be replaced with the later successful state
receipt. Final complete-closure verification, theorem axiom audits and remote
publication remain separate obligations.
