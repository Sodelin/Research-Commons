# Qualified connected Lean release: all 53 required profiles passed

The frozen 53-profile release has passed its final cross-run reauthentication. This is a union of 38 earlier passes, 13 resumed passes, and two exact resource-qualified aggregate reruns. It is not a claim of one fresh invocation or a fresh run from a public download.

- Compatible aggregate: **1,124 modules; 93,129 owned declarations; 86,621 theorem declarations**.
- Canonical aggregate: **1,411 modules; 97,873 owned declarations; 89,920 theorem declarations**.
- Both full audits report no owned axioms, nonstandard-axiom rows, or missing selected modules. Standard Lean axioms are explicitly allowed.
- Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; serial compilation, trust zero, kernel checking enabled.

Every selected source, exact import/object/IR bundle, measured native-runtime binding, complete owned-declaration census and literal namespace-root resolution was reauthenticated. [The complete 53-target pins](TARGET-RESULT-PINS.json) distinguish fresh components in each target's run from exact-context reuse. Counts overlap between profiles and must not be added as unique theorem totals.

## Resource qualification

The original 4 GiB aggregate attempts failed with Lean interpreter memory exceptions. Their evidence remains preserved. The unchanged 1,124-module aggregate and full audit passed at 6 GiB with 300-second bounds; the unchanged 1,411-module aggregate and full audit passed at 6 GiB with 180-second bounds. All component contexts were reauthenticated. The existing exact-source ThetaCertificate5 exception remains 6 GiB/600 seconds. [Resource identities and preserved failure hashes](RESOURCE-QUALIFICATIONS.json) bind these exceptions.

Some inactive loader traces had been losslessly compressed after byte-for-byte round-trip verification. Final verification restored every required raw trace at its exact path, ran the unchanged raw-byte checks, and retained every archive. [The restoration record](LOSSLESS-EVIDENCE-RESTORATION.json) includes the corrected 129-path scope.

## Scope and delivery

Profiles preserve historical source versions and namespace isolation. The canonical aggregate is one coherent selected context; this certificate does not put all historical versions in one environment. Twenty-five provisional targets are outside this required release. The later checked G5 full binary M3 and G6 cell/TV extensions remain separately certified and have not been silently inserted into this frozen graph.

A build pass establishes these selected formal statements and their recorded assumptions. It does not close every G1–G7 master theorem, establish novelty, prove generated runtime behavior, or replace the separate full type/body DAG audit for G2. General G3/G4 and the later G7 candidate endpoints remain open. See the [per-goal status](https://github.com/Sodelin/Research-Commons/blob/5e7e053afc3b85b967b123af0b2bc76acccda1dc/research/2026-10-10-dot-per-goal-lean-status-0000z/README.md) and [dated integration handoff](https://github.com/Sodelin/Research-Commons/blob/3a791f946cd6605e58078c958b7e364a8b447930/handoffs/2026-10-09-goal-oriented-finish-lines/20261010T030600Z-INTEGRATION-HANDOFF.md).

This compact packet delivers the result certificate and exact target/audit hashes. The complete modular source/evidence package and an additive resource-qualified Lake reproduction entrypoint are being prepared. The old default command remains preserved; this packet does not claim it has been corrected or replayed from a public layout.

Research attribution and earlier proofs are preserved in their source packets. This dated certificate records compilation and audit evidence, with no new mathematical or novelty claim.
