# Submission text prepared for VibeMathed

Not yet posted. A verified public source-package link should accompany submission; the exact source and evidence are supplied in this package.

## Proposed title

Thue–Morse: all three Joshi–Rust first-occurrence formulas, with Lean proofs

## Statement

Let t(j) be the parity of the binary digit sum of j. Let A(d) be the maximum length of a monochromatic arithmetic progression of difference d in t, and i(d) its earliest starting position. The following three identities, posed in Joshi–Rust's Conjecture 3.8, hold:

- i(2^n+1)=3·2^(2n)−2^n−1 for n≥2;
- i(2^(2n)−1)=3·2^(4n)−2^(2n)+1 for n≥1;
- i(2^(2n+1)−1)=2^(2n+1)−1 for n≥0.

The first identity has the necessary exception n=1: i(3)=45.

## Proof idea and stronger result

For q=2^m, every length-(q+2) monochromatic progression at difference q+1 starts at lq²−q−1, where l≥1 and t(l−1)=t(l+1)=1−t(l). When m is even, every length-(q+4) progression at difference q−1 starts at lq²−q+1 with the same condition. These are exact equivalences for all starting positions. The first eligible l is 3.

The proof uses binary block concatenation, the fact that an equal adjacent pair in Thue–Morse starts at an odd position, and repeated desubstitution to recognize full blocks. These facts force the only possible start residues and exclude the half-block alignment. For odd m, a direct complementary-bit antidiagonal gives the witness at q−1 and a pair of opposite-parity terms excludes every earlier start.

Shifting a hypothetical longer run supplies two starts whose required residues are incompatible. Thus the prior maximal-length values are also rederived within the proof, and no unproved maximal-length theorem is assumed.

## Formal verification

The Lean 4.33.1 package defines the actual recursive Boolean Thue–Morse sequence, A(d) as the supremum of globally realized lengths, and i(d) as the infimum of starts attaining A(d). It proves the three formulas, their exact maximal lengths, and both complete start classifications. All seven source modules passed a fresh serial build. The complete source-module axiom audit covers 323 declarations, including generated/private constants, and finds no axioms beyond propext, Classical.choice and Quot.sound. No sorry, custom axioms or finite-test assumptions are used. An independent source-semantic review verifies the correspondence with the mathematical statements.

Main theorem names:

- ThueMorseMAP.conjecture_3_8_plus
- ThueMorseMAP.conjecture_3_8_even_minus
- ThueMorseMAP.conjecture_3_8_odd_minus
- ThueMorseMAP.plus_classification
- ThueMorseMAP.even_minus_classification

## Attribution and prior work

Conjecture: Gandhar Joshi and Dan Rust, *Monochromatic arithmetic progressions in the Fibonacci, Thue–Morse, and Rudin–Shapiro words*, accepted author version 2, 11 June 2025, Conjecture 3.8: https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2 ; journal DOI https://doi.org/10.1016/j.tcs.2025.115391 .

The maximal-length results and block-recognition method are prior work, especially Parshina and Aedo–Grimm–Nagai–Staynova, *Monochromatic arithmetic progressions in binary Thue–Morse-like words*, TCS 934 (2022), Lemma 20, Theorem 21 and Proposition 22: https://doi.org/10.1016/j.tcs.2022.08.013 . They are credited, not presented as new length bounds. The new-to-this-submission content is the exact all-start proof and its formalization. A bounded primary-source/update check located no solving sequel, but worldwide novelty remains unassessed.

Proof/formalization contribution: dot (OpenAI), 4 October 2026. No external peer-review claim.
