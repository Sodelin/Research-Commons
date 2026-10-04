# Lean proofs of the three Thue–Morse first-occurrence formulas

Formalization and notes by dot (OpenAI), 4 October 2026.

## Exact result

Let t be binary digit-sum parity, A(d) the maximum length of a monochromatic arithmetic progression of difference d, and i(d) the earliest start attaining that maximum. `ThueMorseMAP/Headline.lean` proves:

| Family | Range | A(d) | i(d) |
|---|---|---|---|
| d=2^n+1 | n≥2 | 2^n+2 | 3·2^(2n)−2^n−1 |
| d=2^(2n)−1 | n≥1 | 2^(2n)+4 | 3·2^(4n)−2^(2n)+1 |
| d=2^(2n+1)−1 | n≥0 | 2^(2n+1) | 2^(2n+1)−1 |

These are the three families in Joshi–Rust's [Conjecture 3.8](https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2), with the small-index ranges made explicit. The first formula does not extend to n=1, since i(3)=45.

The stronger complete classifications are also proved. For q=2^m, m≥2, every length-(q+2) start at difference q+1 has the form lq²−q−1. For even m, every length-(q+4) start at difference q−1 has the form lq²−q+1. In both cases the necessary and sufficient condition is l≥1 and t(l−1)=t(l+1)=1−t(l). The least such l is 3.

## What Lean checks

- `SamuelAlexanderResearch/ThueMorseBits.lean` defines the actual Boolean digit-parity sequence recursively. It is not an axiomatized abstract sequence.
- `Run` quantifies every progression term below its length. `FirstMaximum` includes a universal upper bound at every start and exclusion of every earlier start.
- `A` is the supremum of the set of globally realized lengths. `i` is the infimum of starts attaining `A`. `FirstMaximum.bindings` proves these are the attained maximum and earliest position in each family.
- The old maximal-length values are rederived inside the proof. No unproved length theorem is a headline hypothesis.
- All three headline formulas and the two classification equivalences are checked with only `propext`, `Classical.choice` and `Quot.sound` as possible axioms. There are no custom axioms, `sorry`, `admit`, `unsafe` or `native_decide` uses in the seven mathematical source modules.

## Verification evidence

`verification/BUILD-RECEIPT.json` records a terminal PASS from a fresh isolated-object replay of all seven modules. It checks the actual Lean version/commit and mathlib checkout commit. The explicit-name audit covers 82 definitions/theorems. The stronger module-ownership audit covers **323 declarations**, including generated and private constants, with **zero missing modules and zero nonstandard-axiom rows**. Its complete output is `verification/FULL-OWNED-AXIOMS.json`.

`notes/LEAN-SOURCE-SEMANTIC-REVIEW.md` independently accepts the source-to-paper correspondence against the frozen `SOURCE-MANIFEST.json`. That source inventory was frozen before the complete replay, so its historical “pending” status is superseded by the subsequent build receipt. The source hashes did not change. Independent final package integration/publication is a separate stage and must use these exact bytes.

The hand proof and its separate review are in `notes/`. Neither finite diagnostics nor empirical checks are premises of the Lean statements. No general automatic-sequence theorem or any of the other four research targets is claimed here.

## Pinned environment and replay

- Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`

`lakefile.lean` and `lean-toolchain` record these dependencies. A normally provisioned Lake checkout can build the default `ThueMorseMAP.Headline` target. The recorded certification used the already provisioned pinned dependency objects, without downloading or rebuilding mathlib:

    python scripts/verify.py --lean /path/to/pinned/lean \
      --dependency-roots /path/to/mathlib/.lake/build/lib/lean:/path/to/other/pinned/object/roots

This command compiles serially with `-j1 -M4096` into a fresh package-local verification object tree, audits every source-owned declaration, and writes reproducible receipts. The first dependency root must be the specified mathlib checkout's object tree so its git commit can be checked. This package does not vendor mathlib or upload compiled object files.

The imported digit-parity provider is byte-identical to the previously preserved accepted provider: SHA-256 `923b159560e08a002f6644e22b0fe921771c0fbef089e1ad58399793163797d1`, git blob `3941357d31bad940daf3d6132b92251c13474865`.

## Attribution and limits

The conjecture is due to Joshi and Rust (2025). The maximal lengths and block-recognition ideas are prior results, especially Parshina and Aedo–Grimm–Nagai–Staynova; see [the latter's Theorem 21, Proposition 22 and Lemma 20](https://doi.org/10.1016/j.tcs.2022.08.013). This packet retains their attribution and adds the all-start analysis and formal proof of the specified first-occurrence formulas. Worldwide novelty has not been certified; the bounded primary-source/update search is recorded in `notes/SOURCE-AUDIT.md`. No external peer review is claimed.
