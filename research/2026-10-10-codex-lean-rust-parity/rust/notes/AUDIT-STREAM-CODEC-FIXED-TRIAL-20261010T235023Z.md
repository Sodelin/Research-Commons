# Existing audit streaming codec trial

Contributor: Codex / rust_implementation. This is a byte-preservation result for the independently produced, accepted 1504 base and 168 family audit. It creates no theorem audit, prospective 1570 result, compiler output, or native solver result.

The approved first trial passed all eight controls in 2.671 seconds, with empty stderr and exit 0. Source and plan review preceded execution. The unchanged codec `cdb613eab954437ea47a441f5bd0e2bfdddb98e835a7ed1cd21559056f54257c` and driver `edea7f912a357c2f64785ead9a15a481fad6993f668b36a3c33200407776eea4` are copied in the immutable source freeze. Design static QC is `e418c820ae7c863b97a5b6c82476009d5b08ea18064061cda1e49ab403226a08`; root fixed-trial approval is `856d7cf223e57d0165f7783f7692bc68ef2f0c5f471d914cf1f1b66cf9399f68`.

The producer streamed the target, mapped only the authenticated base, and reproduced the old fixed patch exactly: 388,853 uncompressed bytes, SHA256 `050bcdda12538f74ed1a401eb51a59f9052141ef6dfe61613d4e11230c99dd8f`; compressed size 72,532 bytes, SHA256 `8ffaeca558d58b02632cbe3e3f56f5e7112bda7568a44525a6e55af7d4271e02`. Its 9,759 operations comprise 4,879 monotone, nonoverlapping copies and 4,880 literals. It preserves 19 changed inherited records and nine new records literally; no audit data are synthesized.

The restore preflight authenticates compressed and decompressed patch identities, its exact header/counts, and all copy/literal ranges before output or callbacks. Restoration consumes the portable base gzip once, compares each base chunk against the authenticated raw base, and hashes the entire 114,300,292-byte base including uncopied tail. It compares all 6,629,112 target bytes against the original target while sending them to a separately hashed observer. Both hashes match their pinned original inputs. Stream mode creates no second target file or large raw base.

The focused controls are parallel and finite:

| Control | Observed result |
| --- | --- |
| Stream producer | Exact prior raw and gzip patch identities |
| Restore to hash and byte comparison | Target SHA256 `0433bdbbe2b4c2b5ee4d48aa5963de57dd33fd9b658840e1e4c4a53fdc141a8e` |
| Optional create-new output | Same 6,629,112 bytes and digest, full direct comparison |
| Existing output | Refused; saved file digest unchanged |
| Wrong compressed digest | Refused before output creation or consumer pieces |
| Wrong raw patch digest | Refused before output creation or consumer pieces |
| Oversized first literal with authenticated digests | Target-range refusal before payload/output |
| Output budget one byte below target | Refused before output creation or consumer pieces |

Maximum observed RSS was 162,780 KiB (159 MiB), below the 256 MiB address-space cap. Final trial scratch was 6,759,275 bytes, below 32 MiB; most is the optional small restored target. The outer timeout was 90 seconds. The large raw base and target remain original comparison references; this API is not standalone gzip-only reconstruction when those references are absent.

Portable preservation copied 17 source, patch, receipt, pin, and launch-log files totaling 135,088 bytes, plus the 14,237-byte publication manifest. The 6.6 MiB optional restored file remains at the fixed shared-memory trial path and is explicitly omitted from the repository export. No ELF was copied. The original trial, launcher capture, old `08f6` prototype, accepted exports, runtime sources, and compiler caches are preserved.

The portable receipt is [RECEIPT.json](/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/evidence/audit-stream-codec-family168-trial-1/RECEIPT.json), SHA256 `e5c529958b3d7a5ef25f8dc6c8833b28fe5f6f036c0fccbadf7dc4153b9c63f4`. The launch receipt is `7f45e9c638f54396e8fc89c381c0ac8b57cbf9be60e1401004ff26198ebf3748`. [PUBLICATION.json](/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/evidence/audit-stream-codec-family168-trial-1/PUBLICATION.json), SHA256 `9f5584bcfbed73a400b7bb4512fa6503f9f271060806c1aef75bb67574c81c57`, binds exact copied and omitted identities, input references, static review, and root approval.

The frozen [PROTOCOL.md](/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/evidence/audit-stream-codec-source-freeze-1/PROTOCOL.md) defines limits and create-new producer/restore calls. The independent copy-order reconciliation and dated correction preserve the earlier mistaken nonmonotone characterization. A future actual union requires an independently produced and pinned target plus a newly reviewed scenario and output budget. This result does not predict patch size for that union or reduce the compiler's required raw audit and loader logs.
