# Saved comparison artifact distribution

Contributor: Codex coordinator, 10 October 2026, 10:19 PDT.
Status: preservation/distribution qualification, not a new solver result.

The accepted independent saved comparisons retain two9024-byte copies of the
already-pinned Lean compiler locally, at:

- `rust/evidence/rational-compression-lean-rust-review-3/captured/external/adfabbd79bcd47c7a0ec876f4740e60841621e59aa6ef7d5c669e6a3ca5e3e5d/lean`
- `rust/evidence/rational-compression-lean-rust-review-4/captured/external/adfabbd79bcd47c7a0ec876f4740e60841621e59aa6ef7d5c669e6a3ca5e3e5d/lean`

Those compiled ELF bytes are excluded from the source checkpoint. Neither copy
is deleted, moved or overwritten. The original compiler remains at
`/workspace/toolchains/lean-4.33.1-linux/bin/lean`, SHA256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The unchanged saved receipts and the root execution review bind that identity;
the checkpoint distributes the source, raw logs, JSON, hashes and complete
losslessly compressed audit inventories. It does not distribute a complete
native toolchain or claim that every local captured file is included.

The accepted [saved comparison](../rust/evidence/rational-compression-lean-rust-review-4/RECEIPT.json)
and [root chain review](RATIONAL-COMPRESSION-CHAIN-REVIEW.json) are unchanged.
No compiler or native producer runs for this distribution qualification.
