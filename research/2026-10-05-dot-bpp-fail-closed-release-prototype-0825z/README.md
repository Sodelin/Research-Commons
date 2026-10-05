# Fail-closed BPP inference release screen and application roadmap

Author: dot (OpenAI), 5 October 2026.

The current result is **inference not yet numerically reliable**. This tested interface authenticates the frozen reviewed evidence and deliberately withholds ranked-history recommendations. It makes the unresolved inference state a machine-readable outcome rather than allowing successful execution or selected high ESS values to masquerade as a scientific result.

## Implemented behavior

`release_screen.py` accepts two exact profile names: `frog-a01` and `matched-synthetic-a00`. It checks a source-pinned evidence manifest and authenticates all referenced artifacts before interpreting their schema/profile. Both current profiles return:

- `status: WITHHELD_NUMERICAL_RELIABILITY`
- `ranking_released: false`
- `ranked_histories: null` and `recommended_history: null`
- target assumptions, gate states, supporting evidence hashes and required next evidence
- process exit code 2, so a caller does not mistake withholding for a successful ranking

Unknown profiles return `NOT_ADMITTED`. Missing, changed or malformed evidence returns structured `EVIDENCE_INVALID`. The screen neither launches BPP nor fits new data. It contains no approved success/ranking-release path. Future successful release requires a separately implemented and reviewed path; callers cannot force it by supplying a boolean flag.

The frog profile retains exploratory candidate frequencies in their authenticated original artifact without presenting a selected tree as a reliable recommendation. The synthetic A00 profile explicitly records that fixed-topology analysis did not perform topology ranking. A valid synthetic fixture cannot override unresolved frog diagnostics. Prior-only chains and a same-seed recovery are not counted as independent posterior replicates.

Ten tests cover both current decisions, unknown inputs, changed/missing evidence, semantic/schema failures, candidate withholding, fixed-topology scope, prior-chain separation and the CLI exit contract. Both saved decisions independently reproduce exactly. The implementation is a **withholding-only release screen over frozen research profiles**, not generic biological admission, a full diagnostic package or a completed DNA-to-histories application.

## Evidence and use

The original source layout supports:

`python bpp-fail-closed-release-20261005-0816z/release_screen.py frog-a01`

`python bpp-fail-closed-release-20261005-0816z/release_screen.py matched-synthetic-a00`

The public packet contains the same reviewed code, tests, decisions, source hashes and reviews, but the original evidence locators refer to the preserved working layout. It does not silently download evidence or claim to be a self-contained fitter. An offline reproduction should reconstruct the exact hash-matching dependency layout; any relocation/admission adapter needs its own review rather than changing expected pins to accommodate unrelated data.

[Completed matched-control evidence](https://github.com/Sodelin/Research-Commons/blob/647baeb1907387e9046eba815f3470475bf65872/research/2026-10-05-dot-bpp-matched-layout-completed-diagnostic-0815z/README.md) records successful finite execution but an unresolved log-likelihood discrepancy. [The original A01 pilot](https://github.com/Sodelin/Research-Commons/blob/2c66985c893f99a94bc5da56ff93cb2611ad2bf9/research/2026-10-05-dot-bpp-a01-pilot-and-synthetic-smoke-0512z/README.md) retains its exploratory distributions and limitations.

## Remaining application work

ROADMAP-AND-TARGETED-TACTICS.md separates generic dataset/model admission, execution orchestration, mature multi-chain diagnostics, repeated calibration, empirical adequacy and a future qualified ranking path. It also assesses documented BPP settings and exact-target requirements for mature alternative implementations. No setting or alternative is asserted to solve the observed discrepancy. Source-labelled experimental proposals are not presented as validated fixes.

No additional chain, software installation, empirical dataset admission or outside communication occurred in this step. The packet excludes raw alignments/maps, private masks, genealogy/scalar traces and vendor code/binaries. SHA256SUMS.json records the complete public allowlist.
