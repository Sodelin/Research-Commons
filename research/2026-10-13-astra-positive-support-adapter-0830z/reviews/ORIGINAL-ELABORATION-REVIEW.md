# Original elaboration mode: repair review

Reviewer: Astra Rust integration lane, 2026-10-13. Source/receipt readback only;
no compiler or tests run by this reviewer.

**No blocking issue found in the narrow repair.** The owned runner's sole
change against its preserved predecessor is removal of `-DElab.async=false`.
The external runner makes the same command change and updates its description
and execution label accordingly. Source/import selection, receipt checks,
shared resource helper and the original 4 GiB virtual/physical caps remain
unchanged. Existing successful objects retain their original execution modes
and receipts rather than being relabeled as freshly rebuilt.

The preserved index2015 failure reports unknown identifiers
`eq_convexComb.zero_le` and `eq_convexComb.le_one`, with notes that private
declarations exist. It is not reported as a resource stop. The repair restores
the compiler's original elaboration mode without changing the source or making
private declarations public. Both current and copied `UnitInterval.lean` bytes
match SHA256
`8eeb6d1274d80cab480263c389643e202673852b88d7c09e25f2b1e093fec657`.

The subsequent UnitInterval diagnostic records compiler exit0 in 4.906 seconds
and guard exit0 without a stop in 6.016 seconds. Its compiler outputs are empty
and match their recorded hashes. All five current object hashes match the
successful diagnostic result. The replacement state receipt and archived
failed receipt/log hashes match the explicit repair record. Earlier failure
evidence remains distinct and must not be rewritten as success.

Batch021 then freshly compiled index2016, `Mathlib.Topology.Path`, in
7.281 seconds with the original elaboration command and the existing arena/cache
helper. It authenticated 2016 previous receipts and correctly retained
`complete=false`. Guard output hashes match the actual files; guard exit0 has
no stop and the original 4 GiB caps. Resource events remain separate from the
single module-completion event. This is a successful continuation through one
additional module, not evidence of full closure or provider/adapter completion.

| Reviewed source or receipt | SHA256 |
| --- | --- |
| `build_external_serial.py` | `2877e394fefb6485426a78232784385ede77091dc9345c7fc22d862ce54977b8` |
| `build_support.py` | `e2728d05a58b7c15158d2ce3707d1e77fe9f91e62cb494a68639432bbc48287f` |
| Unchanged `serial_compile.py` | `c495482f4f6118de0d4eb5d26ff511b1b80ef1db071a223a52b7d55c740fd873` |
| `evidence/ORIGINAL-ELABORATION-REPAIR.json` | `cdd33e9dc89dd8d309b8a6ada75b9c142d7a1b8de96ec496bc5f02525eb59ee3` |
| Diagnostic `RESULT.json` | `2930809407e1564eae2a4600797c409193e985792f353025fa1467bf40669896` |
| Diagnostic guard `RECEIPT.json` | `d2af4293b751874db6fa9aa9905fbe256247b2ee65969d7a92f7b9ee68aaad11` |
| Replacement state receipt `2015.json` | `2c6ff2853229d93ed9d8a46ffb1a416020e88f62e26943657ec7c48f7fea60f0` |
| Archived failed state receipt `2015.json` | `2df6352924d16f515591895920ea23c5cc96039d1b57deac5afe2e6f6b101c3e` |
| Batch021 guard `RECEIPT.json` | `3c88cc3922a1e073d2447bf2694ec63323b9641c281be92cfdf0bd9e5af2c54f` |

The diagnostic evidence is under
`evidence/unit-interval-original-elaboration-samples-4g/` and its separate
`evidence/unit-interval-original-elaboration-4g/` guard directory. This review
does not establish universal compatibility of mixed prior elaboration modes;
later exact imports and aggregate execution must supply their own receipts.
