# Bounded queue pickup and resume

Run this against an existing authorized Git checkout and a trusted local Lean 4.33.1 already installed. Keep the state directory on persistent storage separate from the checkout, owned by the same worker. The driver checks only supported typed inputs and compiles generated source. It does not import untrusted standalone Lean, run Z3, push commits, or create a hosted job.

```sh
python3 queue_pickup.py /path/to/checkout /path/to/worker-state <exact-head> /path/to/lean --base <initial-ancestor> --jobs 1
# On later invocations omit --base.
python3 queue_pickup.py /path/to/checkout /path/to/worker-state <exact-head> /path/to/lean --jobs 20
python3 test_queue_pickup.py /path/to/lean
```

First initialization records only the caller's starting ancestor, not proof evidence. When a head is staged, Git input and manifest pins remain fixed until that head is handled. Each invocation handles at most 20 entries and accepts completion only after terminal receipts and generated artifacts are on disk. A timeout or unclassified checker failure blocks advancement at that row. A reproducible invalid weighted combination is recorded as rejected, not as a proof or disproof. The driver refuses changed pending receipts and changed helper identity; the identity is not a portable Lean dependency cache or full toolchain attestation. Same-head replay makes no new proof claim. Retired or unchanged proofs are not rechecked merely because the head changed.

The [cloud test](queue-pickup.receipt.json) checked a partial run and explicit resume, tamper refusal without cursor advancement, fresh verification of an added rounded proof, rejection of an amended false claim, and a docs-only no-op. The [five-lane receipt](pickup-five-lane.receipt.json) also contains independent checks of the exact handoff, Lean import, SMT generation and Discovery regression. This is a Linux worker pilot. No hosted wake, general prose port, or complete repository batch is installed or implied. A caller still needs a trusted current Git checkout, pinned compiler, and a durable state volume across wakes.
