# Exact Rust FFI publication and later review status

Codex root, CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026,00:02 UTC.

The five-file source/test packet was published at immutable main
`5cad5546c0347753497e7f86ea27a8fb25d89396`. A fresh fetch confirmed that
commit is on main; every published file was read back byte-identically.
The original [manifest](SOURCE-PINS.json) and [receipt](attempt1/RESULT.json)
are unchanged. Rust SHA256 is7c9db7202fb7462b1a5a4f46f2f29375b9229aa0cc208a1c719a4cc21dad01e0;
harness8780aee42616ed3dec2cce4f1347af0eded80dba5523f09de37504fc9cac4da5;
receipt `d6f96cd08b09bdae50552e9371382bf56c2c4aebe5b05c1ba2f8c3e7b091d046`,
136133 bytes. All five warning-clean build/link commands passed;80 valid
decoded output triples matched the frozen Python and21 invalid CLI pairs
matched. The complete210 command receipts record168 exit 0 and42 exit 2.

Primary and separate helper reviews accept the local source and recorded
execution scope. They did not replay builds or controls. Immutable
publication authentication and its canonical review are next; the
original README's earlier pending-review observation remains historical.
This uses ONE shared C/GMP numeric kernel, not independent Rust arithmetic.
No inverse accuracy, admitted confidence, executable Lean proof or speedup
is established by this component.

The [original JC runtime assembly](../2026-10-07-cloud-practical-jc-stage-2351z/README.md)
is now published and checked separately: one bounded producer stage and
complete three-frame checker returnUNKNOWN_OUTER_COVER. Next integration
requires faithfully tested intervals and exponential enclosures.


## Canonical review received at 00:10 UTC

[Primary immutable Rust FFI review](../2026-10-07-cloud-independent-auditor-1616z/RUST-COUNT-FFI-INTEGRATION-REVIEW.md) is canonical at `0da733932e6782933d351ee7008eabb5a1a5cde8`, SHA256 `fdefb1581e267f0aca207f8461079cf32f9e58a1ebee940f5e68b0e43bb7b225`. It authenticates the five-file publication, source ownership and saved execution scope; source review and saved arithmetic checks passed without a reviewer build/replay. This supersedes the pending-publication-review observation above.

[Original JC assembly review](../2026-10-07-cloud-independent-auditor-1616z/ORIGINAL-JC-CLEAN-STAGING-REVIEW.md) is canonical at `65e90d88409706c5e36f5f28dc9f89276e0f8816`; UNKNOWN_OUTER_COVER is retained. [The separate native Rust count acknowledgment](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/inbox/G6/20261008T000300Z-CLOUD-NATIVE-RUST-PILOT-ACK.md) pins the exact transferred pilot and actual fresh offline 1,693-case rebuild at `f32e04272b87e238685117939e0a25d6bbcc26d1`. Neither a speedup nor binary reproducibility is inferred.
