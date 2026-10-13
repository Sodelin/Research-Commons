# Exact public core recovery and fresh decoder/history replay

**Tested result, 2026-10-13 07:04 UTC.** The previously unavailable local Rust
core was found in the existing public branch
[`codex/lean-rust-parity-cloud-20261010` at `4e556c4ae6225d18fabf30bc7d3347a468749ebc`](https://github.com/Sodelin/Research-Commons/tree/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust).
This corrects the earlier executor-local recovery gap. It does not change the
separate missing Lean physical representative provider or establish general G3.

All 25 in-repository Rust-related pins in the latest decoder execution
configuration match that immutable branch byte for byte. In particular:

| File | SHA-256 |
| --- | --- |
| `src/lib.rs` | `905866b45229667cc06385461c7eb0e96784cb2309e0ba17b45d4c8409a37d4d` |
| `src/source_population.rs` | `6afebffe8bb727a1c92bd113d479f01f0b2877bbf527c79866247805bc21da7c` |
| `src/source_epoch.rs` | `c46a498ac2b5a0f3bc3ea246cc4f6d012ff58871292b8af84cfebe3d45b40354` |
| `src/source_fit_bank.rs` | `e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a` |
| `src/source_fit_readout.rs` | `7a3a75b60af55f1138e82aa66c5a2e94b5dc9c8a597eadb0ff25230f03dae7c5` |
| `Cargo.toml` | `8eb9e35ed020e0efd4feb7c50d52d91dfd68bc0c8928a029e9afd292c321aa8d` |

The other inspected public branch, `6c743ca48da3aa894e11e1c560c199165a549348`,
shares several core files but lacks the same library module selection. It was
not substituted merely because its branch name looked relevant.

`restore_parity.py` reconstructs a new scratch tree from immutable Git objects
and the already published decoder/history source packet. It checks the entire
decoder packet hash, each embedded artifact, and every applicable historical
parent pin before writing. Its 51-file, 488,056-byte inventory is
[`evidence/parity-restore-window-repair/RESTORED-SOURCES.json`](evidence/parity-restore-window-repair/RESTORED-SOURCES.json),
SHA-256 `c5c84b5fa1755ae05830059353c184a77c52bd236b4053fe2668e6e30f066da6`.
The inventory gives every selected source hash, Git blob, immutable commit or
packet origin, and transformation. No existing checkout files are overwritten.

The latest decoder implementation and its three-head test harness remain
literal copies, respectively SHA-256
`37a00f8767af2a0002970e7a59d046861c4c8601f65c46fe0e86650694c6e318` and
`38e1bdc0fcf4a082a6af4e215a9d3ffac9cd6ad6fbbfd5d2c98b4e7226af591a`.
The original serial full-history harness, SHA-256
`82fd059e3b813e6d1c9b65de03c8f15037d5d6d9ab15be8b51687160e2f98cb7`,
is preserved alongside the executed relocated copy. Exactly one absolute
`#[path=...]` is changed to its adjacent recovered `source_selected_prefix.rs`;
all test logic and expected values remain unchanged. The manifest records both
hashes. This relocation is not represented as literal unmodified harness reuse.

## Actual fresh execution

The exact Rust 1.90 toolchain provisioned by the existing native replay method
compiled the recovered core and its exact arithmetic dependencies in a fresh
target directory using `cargo build --lib --locked --offline -j 1`. The build
took 5.51 seconds with peak child RSS 270,446,592 bytes. An inherited unused
import warning was preserved rather than editing the frozen source.

| Receipt directory | Actual outcome | Reuse distinction |
| --- | --- | --- |
| `evidence/recovered-parity-core-build` | Core library and arithmetic dependencies compiled, exit 0 | Fresh compilation from recovered source; no historical object files used. |
| `evidence/recovered-parity-controls-extern-repair` | Decoder 3/3, serial full-history 1/1, all compile/test steps exit 0 | Fresh test binaries against that newly rebuilt core; original decoder and explicitly relocated serial source. |
| `evidence/recovered-parity-population` | Existing population controls 6/6, exit 0 | Fresh test binary; reuses core/dependency objects built earlier in this same run. |
| `evidence/rust-unit` | New sparse-certificate checker 5/5 unit groups, exit 0 | Fresh checker and exact-count parser/library dependencies in its separate target. |
| `evidence/rust-binary` | New sparse-certificate executable, exit 0 | Fresh executable reusing dependencies just compiled for its unit tests. |
| `evidence/rust-differential` | 556 process checks, 180 accepted and 376 refused, all expected outcomes | 178 rational certificate forms plus exact mutations and wire controls; finite differential evidence. |

The new certificate executable hash is
`1a508f23613bb527e5605c806fb8215ed6a16adeed4c4147658236790064d805`.
The recovered decoder/history runner authenticates all 51 restored files before
and after execution and records compiler, library, executable, command, exit,
and output identities. The enclosing resource guard records separate memory,
disk and time limits, pressure samples and process-group termination policy.
All test runners use one native test thread. These successful runs did not
trigger a resource-pressure stop.

Preserved failures and exact repairs:

1. `evidence/parity-restore` failed before writing the recovered tree; its first
   diagnostic suppressed Git stderr. `evidence/parity-restore-read-diagnostic`
   retained the actual reason: Git attempted to map a pack beyond the 512 MiB
   address-space limit. The repair sets **per-command** `core.packedGitLimit=64m`
   and `core.packedGitWindowSize=16m`; the same process limit then passed in
   `evidence/parity-restore-window-repair`. No OS or persisted Git setting changed.
2. `evidence/recovered-parity-controls` compiled and passed the decoder, then
   failed serial harness compilation because the runner omitted explicit
   `num_bigint`, `num_integer`, and `num_traits` extern arguments. The repair adds
   those exact freshly compiled libraries; it changes no recovered Rust logic.
   The new run has a distinct output and binary directory and preserves the
   original failure.

## Reproduction

From this packet directory, use the following structure with fresh absolute
scratch paths. `guard.py` must enclose each build/test, and every evidence
directory must be absent. Set `CARGO_HOME` to the existing checksum-verified
vendor configuration and prepend its verified toolchain `bin` directory to
`PATH`; do not replace the system toolchain. Dependencies are selected by the
unchanged recovered `Cargo.lock` and fetched only if required by that pin set.

```text
python3 -B guard.py --out evidence/restore-new --cwd . --memory-mib 512 --wall 60 --cpu 45 --file-mib 16 -- python3 -B restore_parity.py --output SCRATCH --manifest evidence/restore-new/RESTORED-SOURCES.json

python3 -B guard.py --out evidence/core-new --cwd SCRATCH/research/2026-10-10-codex-lean-rust-parity/rust --memory-mib 2048 --wall 180 --cpu 120 --file-mib 256 -- env CARGO_HOME=VENDOR_HOME CARGO_TARGET_DIR=TARGET CARGO_PROFILE_DEV_DEBUG=0 cargo build --lib --locked --offline -j 1

python3 -B guard.py --out evidence/controls-new --cwd . --memory-mib 2048 --wall 180 --cpu 120 --file-mib 256 -- python3 -B run_recovered_controls.py --restored SCRATCH --target TARGET --rustc TOOLCHAIN/bin/rustc --out evidence/controls-new/steps --binaries NEW_BINARY_DIRECTORY
```

This is a reproducible recovery of the accepted bounded native component and
latest finite controls. Its original claims remain unchanged: canonical source
snapshots preserve local/global IDs, ordered genealogy, parallel edge occurrences
and all register positions; selected-value membership is a bounded witness
check, not unique source/code/history recovery. Full serial histories retain
earlier/later merger distinctions even when final states coincide. Neither
these tests nor their native code establish universal native-to-Lean refinement,
arbitrary hidden-source admission, certificate acquisition, or general G3.
