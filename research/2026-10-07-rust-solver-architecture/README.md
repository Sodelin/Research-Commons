# Rust solver architecture: original proposal and dated adoption note

Contributor: OpenAI dot. Dated update: 2026-10-07 23:49 UTC.

[ARCHITECTURE-PROPOSAL.md](ARCHITECTURE-PROPOSAL.md) is the original design proposal, preserved unchanged at SHA-256 `5a3acffb4e4483bc5b4b49881f78b14863705032c4f7f8e9938955c17ecb0c5a`. Its initial unimplemented, unadopted and unpublished status describes the earlier proposal snapshot.

Nolan subsequently authorized starting staged integration at 23:13 UTC, then transferred Rust application, integration and publication work to the Codex work team at 23:36 UTC. The count-only pilot has bounded executed checks and independent review; the exact payload is supplied through [the ownership and blob-manifest handoff](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/inbox/G6/20261007T234400Z-DOT-RUST-CODEX-OWNERSHIP-TRANSFER.md). Final count-pilot publication and receiver acceptance remain Codex-owned.

The interval stage was started and then paused for that transfer. [Its preserved unfinished handoff](../2026-10-07-rust-interval-handoff/README.md) records nine passing unit tests, one failing unit test, an optimized build pass, and no differential acceptance. The failure diagnosis is not a fix. No later-stage implementation or verification is inferred.

The original proposal's other engines, interfaces and GUI remain proposed choices that need a named capability, mathematical contract, compatibility policy and validation evidence. Staged integration does not imply an automatic full rewrite, installation of every backend, a production-default change or a completed solver. No dependency or deployment selection is made by preserving this design note.

Preserve frozen references, exact arithmetic and rounding schedules, refusal/budget semantics, provenance and explicit claim limits; test independent implementations before performance claims. Cloud retains its existing formal/source integration and sole Lean compilation ownership. This transfer changes no shared provider, Lean source or workflow. Dot is no longer implementing the Rust application.
