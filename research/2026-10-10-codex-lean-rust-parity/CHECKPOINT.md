# Continuation checkpoint

Codex coordinator, 2026-10-10 10:28 UTC. This records saved work and observed
processes; it does not promise workers or a cloud session remain alive forever.

## Workspace and ownership

Repository: `/workspace/Research-Commons`. Local branch:
`codex/lean-rust-parity-20261010`, baseline
`32f1538ebcd1a80b999bb14e08df905d13184ec7`.

Four Sol/max workers: `lean_integration`, `lean_reuse_recovery`,
`rust_implementation`, `solver_design`. The original `lean_reuse` connection failed
repeatedly; its saved drafts were resumed by the recovery worker. Root owns the
application launcher, central checkpoint, independent quality checks and git
references. Workers own `lean/`, `reuse/`, `rust/`, `design/` respectively and
coordinate shared contracts. Lean integration owns compiler scheduling.

No changes have been pushed and no PR has been created. Held publication
artifacts have not been rerouted. Do not equate a saved checkpoint with a hosted
automation or silently replace historical hashes.

## Accepted and advancing work

See [README](README.md) for accepted parity, oracle, launcher and static-inventory
receipts. Preserve all failed/incomplete attempts. The constructive rational
witness module has freshly compiled: all 14 printed endpoint axioms use only
the standard Lean axioms. The contradiction-certificate first attempt failed
on imports/decidability; subsequent fixes passed the complete fresh eight-module
arithmetic/wire/cap audit (345 declarations, 175 theorem declarations). Typed
original-cell/ordered-compiler/fixture files remain drafts until their receipts pass.

AFFINE/COUNT native parity passed 281/281. Before additive CHART changes, binaries
were preserved in scratch. The frozen Rust executable is
`/workspace/scratch/lean-rust-parity-native/runtime/affine-v1-frozen/parity-solver`;
its identities are recorded in existing receipts and the source snapshot
`rust/evidence/history/affine-v1/SNAPSHOT.json`. The executable Lean core binary
identity in prior accepted evidence is
`795fd20be92a466ac8d7069824744d3d9837fe8c7893ff3d56958bef998ec68e`.

The additive CHART operation passed 78 native/regression cases, 15 certificate
forgery controls and 42 direct physical-bank cases. Its separate chart adapter
passed 18 independent challenges; the explicit `natural-cell` application command
passed six launcher cases plus output preservation. Current native identities:
Lean `e7dd375a6bdf08337894a0070e9ed5f19ef5004192251c796d61b8f5750534c8`,
Rust `9e2bafa8d82e108820ba46c866e7826dd872d3075df8f9709bc6fd1020e1f5d4`.
Exact receipts and source snapshots remain under `lean/evidence`, `design/evidence`
and `quality/evidence`. Pre-LAW CHART binaries/sources have also been preserved.

The root's [direct physical-bank oracle](quality/chart_bank_review.py) passed
42/42 cases on both CHART binaries. It checks ages, inverse rates,
inheritance, chronology and duration/rate exposures directly, without compiling
affine rows. Design owns independent original-row contradiction checking and
transport controls. Reuse is preparing a concrete typed two-tip compiler fixture;
the relevant theorem is list `.toFinset = compileCell`, since the inherited
compiler returns a finite set without a transport row-order promise.

## Full Lean replay

Pinned Lean 4.33.1:
`/workspace/toolchains/lean-4.33.1-linux/bin`, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Pinned Mathlib: `/workspace/dependencies/mathlib4`, commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

The official HTTPS Azure cache failed with CONNECT 403. The team is building
dependencies from source, preserving proxy configuration and HTTPS. Minimal
arithmetic and wire dependencies completed. The full union requires the larger
external closure, estimated at 8,312 Mathlib files because inherited sources
import broad `Mathlib.Tactic` providers.

The external Lake source build remains live with four Lean workers. Its logs are
`/workspace/dependencies/build-evidence/current-union/stdout.txt` and
`stderr.txt`. Counts in Lake logs are dynamic jobs; they do not count accepted
project modules. **The project-module union started at 10:21 UTC**, run
`lean/.build/runs/20261010T102154.481687Z`. It is checking ready owned modules
serially while external prerequisites continue. At 10:28 UTC it had 79 fresh
passes and was checking the exact documented ThetaCertificate5 exception.
Inspect the process and logs before restarting it; do not duplicate a running compiler.

The default sequential replay command for the new public-context union is:

```bash
CONNECTED_LEAN_BIN=/workspace/toolchains/lean-4.33.1-linux/bin \
CONNECTED_MATHLIB=/workspace/dependencies/mathlib4 \
python3 research/2026-10-10-codex-lean-rust-parity/lean/scripts/build_connected.py current/connected
```

The builder saves exact source/import/native-runtime identities, source-specific
compilation receipts, aggregate imports and a complete owned audit. Root review
found that audit acceptance had only checked exit code; integration fixed it
to require `PASS_FRESH_KERNEL_CHECK` and compiler identity stability. Do not use
an audit with failed integrity checks to assign target PASS. Most ordinary
components have 4 GiB/180-second caps; the exact previously documented
ThetaCertificate5 source has its retained 6 GiB/600-second exception. Preserve
resource failures as failures, not mathematical counterexamples.

This is a new 52-context public composition with 1,342 available source versions
and a 1,340-module current union. It does not reconstruct the held 1,411-module
package or reassign the historical 53-profile certificate.

## Next concrete actions

1. Continue additive LAW: port the inherited G7 full-joint genealogy compiler to
   Rust and an effective native Lean mirror, with exact polynomials/current-lineage
   routing and conservative budgets. Design owns the contract; root's five
   independent symbolic baseline cases already pass.
2. Finish original-bank/ordered-compiler/typed-fixture draft verification with
   separate exact owned audits; preserve the accepted arithmetic/wire/cap chain.
3. Finish external prerequisites, then compile/audit the current 1,340-module
   union. Resolve actual failures without editing historical proof evidence.
4. Preserve accepted CHART application behavior while LAW advances; source
   admission and prior default behavior remain unchanged.
5. Current application byte verifier passes (23 pins, 534 inherited unchanged
   files, one explicit intervening navigation update). Refresh pins when owned
   runtime sources stabilize after changes and record local git checkpoints. Its generator
   preserves the prior manifest and explicitly records the intervening
   `START-HERE.md` baseline update.
6. Continue the full source/observation compiler and remaining original
   mathematics where actual compatible providers permit it. G3/G4 unknown-size
   recognition/forcing, G6 representative/cloud and G7 policy gaps remain open;
   no finite chart or runtime test is substituted for them.
