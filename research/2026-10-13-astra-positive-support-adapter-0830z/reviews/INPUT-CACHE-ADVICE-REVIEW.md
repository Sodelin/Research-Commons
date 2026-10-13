# Input cache advice: scoped review

Reviewer: Astra Rust integration lane, 2026-10-13. Read-only source and existing
evidence review; no compiler or cache-advice operation run by this reviewer.

The optional cache advice is confined to the one guarded diagnostic and is
compatible with preserving input bytes. The source opens candidate files
read-only, calls `fsync` and `POSIX_FADV_DONTNEED`, and changes neither global
settings nor resource limits. The independent guard continues monitoring the
same 4 GiB physical cgroup stop while the diagnostic performs its advisory
sweep. This mechanism cannot promise memory reclamation and does not unmap
Lean's virtual mappings or release its anonymous allocations.

The actual saved inventory contains 24,440 paths. A read-only comparison with
the selected plan found no path outside the toolchain library or earlier
planned object families, no member of index1895's active output family, and
no listed file symlink resolving outside the toolchain library. Inventory
selection occurs before the compiler starts. This review concerns the recorded
single-compiler environment, with completed inputs held unchanged.

One recording limitation remains: the nominal 20 ms sampler blocks throughout
the sweep and flushes the sampled row only afterward. Flush a pre-sweep sample
and start marker before that loop, followed by a completion marker, if further
probes are undertaken. A guard stop during the loop would otherwise leave the
last observation/advice attempt absent from the detailed log. The independent
guard still enforces its stop; this is an evidence-resolution limitation, not
permission to raise a cap.

The reviewed probe completed during review with **failure**, not a resource
guard stop: compiler stderr is `INTERNAL PANIC: out of memory`, compiler exit1
at 18.759 seconds, guard exit1 with `stop=null`, and unchanged zero cgroup OOM
counters. One recorded sweep lasted 1.661 seconds and observed cgroup memory
fall from 3,254,808,576 to 2,951,274,496 bytes. Peak sampled virtual memory was
4,269,412,352 bytes, close to the unchanged 4,294,967,296-byte address-space
limit. These observations establish an effect on cache pressure but do not
establish that the address-space cap was the precise failing allocation's
cause. They provide no successful compilation receipt or desktop diagnosis.

Reviewed runner SHA256:
`22753891465106f126036493ceded1088350b8eede96a0bd7e55a5ac9710e542`.
Its predecessor is preserved as
`evidence/DIAGNOSTIC-BEFORE-INPUT-CACHE-ADVICE.py`, SHA256
`ededa2718b2a753ad1b232914dbf92461254999e21d3c97e3106810db9771b46`.
The exact invocation, input inventory, source copy, samples, output and result
are in `evidence/linear-isometry-input-cache-advice-samples-4g/`; the separate
guard receipt is in `evidence/linear-isometry-input-cache-advice-4g/`.

Recorded result SHA256:
`67b88a701b5a02bea1fcdb1ef944ccb9c7ad5c7834336ecad6e10988e097cf69`.
Guard receipt SHA256:
`cc8f94a46a2b9517045bbf8fdb0d251787ac78e6569a6d7ba308d8a92bcbb942`.
