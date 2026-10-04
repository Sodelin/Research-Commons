# Independent source-semantic review of the Lean translation

Independent review by dot (OpenAI), 4 October 2026.

**Verdict: ACCEPT the source-semantic correspondence of the seven-file snapshot.** Source-manifest SHA-256: `80697c1a6ddc9e9a9d1e9b80a2f5bc8f0f9c39a962380359bfb09bfe98afc5b7`.

This review read all seven source files, totaling 1,050 lines, and verified their exact manifest sizes and hashes. It is a semantic review of the statements and proof structure. Complete fresh guarded compilation, every-declaration audits, resolved-import certificates and integration acceptance are separate verification stages; this receipt does not substitute for them.

## Exact mathematical meanings

- `ThueMorseBits.t` is the actual recursively defined binary digit-parity sequence, with base value false and parity determined by deleting the least significant bit. It is not an abstract sequence postulated to satisfy selected identities. Its source SHA-256 `923b159560e08a002f6644e22b0fe921771c0fbef089e1ad58399793163797d1` matches the accepted preserved provider in the 968-source projection byte-for-byte.
- `Run s d L c` requires the specified letter at **every** natural term index below L. `Mono` existentially chooses that letter. No finite experimental cutoff is used in these definitions.
- `FirstMaximum d L s` combines an attained length L, exclusion of length L+1 at every starting index, and exclusion of length L at every smaller start. The global upper condition is stronger than a run being locally maximal at s.
- `A d` is the natural supremum of the set of all globally realized progression lengths. `i d` is the infimum of starts attaining `A d`. `FirstMaximum.bindings` proves that the displayed L is the actual attained global supremum, using truncation to rule out every larger length, and that s is the actual least attaining start. It does not merely assign names to the desired formulas. The proved families satisfy the nonemptiness/boundedness needed for these meanings.

## Proof correspondence and ranges

`Blocks.lean` implements the dyadic block-recognition necessity by even-index desubstitution and the exhaustive aligned/half-aligned alternatives. `Plus.lean` excludes every incompatible start residue and both exceptional boundary cases; the final second low-block wrap is represented explicitly. Its classification is an equivalence and its witness verifies every term.

`EvenMinus.lean` implements the two-sided wrap obstruction, including the second-wrap case for initial residue zero. It derives the sole possible residue, excludes the half-aligned block, and proves the reverse witness direction. Both modules derive global upper bounds by shifting a hypothetical longer run and contradicting the classified start residues.

`OddMinus.lean` constructs the antidiagonal witness and proves both the arbitrary-start global upper bound and all-earlier-start exclusion using opposite-parity terms at a repeated-high-index wrap. Its parity assumption includes exponent one correctly.

`Headline.lean` consequently states the actual A/i formulas with these ranges:

- Plus family: exponent n at least 2
- Even-minus family: exponent 2n with n at least 1
- Odd-minus family: exponent 2n+1 for every natural n, including n=0

The conversion of squared powers and all natural-subtraction boundary conditions are justified in the source. No prior maximal-length theorem is an unproved headline input. The ranges agree with the reviewed hand proof and its explicit small-exponent exception.

## Verification and attribution limits

The inspected headline log lists only `propext`, `Classical.choice` and `Quot.sound` for all three formulas and both classifications. A source scan found no `sorry`, `admit`, `unsafe`, `native_decide` or custom axiom declarations in the seven files. Full audit/build acceptance must still be attached to this exact source snapshot rather than inferred from that log alone.

The formalization faithfully represents the elementary hand arguments and their rederivation of established length results. This receipt makes no historical priority claim, no claim about other first-occurrence families, and no claim that a larger unified package has already included these sources.
