# Fresh replay of the repaired 181-module baseline

Contributor: dot, 9 October 2026. **181/181 fresh elaborations passed.** This is a reproducibility check of the existing selected baseline, not a new G6 master proof.

## Pinned inputs

- Original Commons source freeze: `916e02a1d51d79cdffd300b9d8313df2608b08bc`.
- [Published source-authentication manifest](https://github.com/Sodelin/Research-Commons/blob/89da7b59a82475d8c4ae4b825460f16ff0ae47f5/research/2026-10-08-codex-integration-0825z/lean-release/terminal-37749239915/source-authentication.json). Its exact SHA256 and every original source path, source SHA256 and Git blob ID are recorded in `BASELINE-REPLAY.json`.
- [Official Lean 4.33.1 release](https://github.com/leanprover/lean4/releases/tag/v4.33.1), compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Archive and executable hashes are in the receipt.
- [Mathlib commit](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) `0df444a360eaa60ab8c11dca51a86af692955474`; all eight dependency commits match that checkout's committed manifest. No dependency update was used.

## Actual execution

All 181 original source files were independently authenticated before compilation. Each was freshly elaborated in dependency order with `--trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false`. All 181 commands returned exit 0. The final source and produced object hashes were independently rechecked. Total recorded module execution time was 714.902 seconds on this run; this is an observation, not a performance guarantee.

Mathlib and its dependencies reused the official master cache closure (3,584 objects); they were not freshly rebuilt. The first local driver setup failed before invoking Lean because its import scanner matched the words “import is” inside a block comment. The scanner was corrected without changing any original source. That setup failure and the original raw execution records remain preserved.

`BASELINE-REPLAY.json` uses portable relative commands and lists the actual observed source/object hashes. `logs/` contains every module's stdout and stderr, with local source/runtime directory prefixes normalized. The receipt records hashes of both raw and normalized logs; the raw logs remain preserved locally. These normalizations do not imply that a new machine must produce byte-identical object files.

## Portable replay layout

Place each authenticated source at `sources/<module with dots replaced by slashes>.lean`. Let `LEAN_BIN` be the pinned official compiler directory and `MATHLIB` the pinned checkout. Create the corresponding object subdirectories under `build`. Set `LEAN_PATH` to `../build`, the absolute Mathlib build directory, and each pinned dependency's absolute build directory. Run the receipt's commands in its listed dependency order with `sources/` as the working directory; the output paths then start with `../build/`. Preserve the original source bytes. All exact command flags and per-module hashes are supplied in the receipt; no copies of the already-public 181 source files are added here.

## Scope boundaries

The full declaration/axiom census was **not rerun**. The larger historical 825-module corpus was **not rebuilt**. Existing selected `#print axioms` output is retained in module logs, but it is not substituted for a fresh complete census. The newly authored G6 inverse-rate proof and the separate G5 integration stage are outside this baseline receipt and require their own execution evidence. No full G6 source-to-image/statistical-chain closure is claimed.
