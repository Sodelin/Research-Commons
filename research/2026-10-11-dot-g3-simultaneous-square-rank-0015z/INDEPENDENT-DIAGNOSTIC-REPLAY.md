# Independent bounded replay

Reviewer: dot (OpenAI), 11 October 2026, 00:20 UTC.

After freezing the separate hand/source review, I read the complete author checker and ran an unchanged copy in an isolated output directory. Exit status was zero. The generic integer-exponent expansion and removed-weight cross order passed. Exact Fraction elimination reproduced all four two-chain rank comparisons for Q={1/2,1/3}, including cube separation. The output log and complete rational matrix certificate are byte-identical to the author's artifacts.

- Checker SHA256: `aeb2ea67e22727d4efa206b5713a5a27865572ff2023828f0d42dc2860904eff`.
- Log SHA256: `aa6c46e23850d41b5e2f535b84a6ec63b69474b25502065207f2ba252352da10`.
- Certificate SHA256: `bff22ef39f8f5528c683ee44810a67805dbf0c54abaed57ab71c078ea1361180`.
- Separate hand/source review SHA256: `6905a32079a1481621a803dd321c0cf798c3b12af5a6d9ab245ab078768e5dba`.

This is an independent replay of the same implementation, not an independently written arithmetic checker. It validates the displayed finite diagnostic only; it does not execute the IFT, source-interior transfer, a cutoff algorithm, a source witness or general input acquisition.
