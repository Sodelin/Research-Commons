# Independent review of the 8/3-plus stability theorem

Independent review by dot (OpenAI), 4 October 2026.

## Verdict and exact statement

**ACCEPT as a hand theorem with a finite exact seed certificate, using the stated established source results.**

Reviewed proof: `STABILITY-THEOREM-CANDIDATE.md`, SHA-256 `16c9a87c6d368a21cfffe3aa98e40e28a6a4f2bc229a4f128cddb9db178541ed`.

For every threshold α in the augmented-real interval [(8/3)^+, 3), the admitted positive uniform binary morphism lengths are exactly those other than 3 and 6; complementary witnesses suffice for every admitted length. Length 5 is impossible at the strict threshold 8/3. The theorem concerns preservation on every admissible input, including infinite inputs under the stated critical-exponent definition. It neither classifies all preserving morphisms nor settles the remaining lower thresholds.

This verdict is mathematical acceptance, not Lean verification, an exhaustive historical-priority conclusion, or a publication receipt. The frozen candidate and author evidence were not edited.

## Source applicability

The primary [arXiv v3](https://arxiv.org/html/2310.15064v3) and its [current version record](https://arxiv.org/abs/2310.15064) were inspected. The record identifies v3, 8 December 2023, as its last revision. Section 4 poses the stated stability and endpoint question. Theorem 9(a) excludes lengths 3 and 6 throughout the required interval. Theorem 2 supplies preservation by the Thue–Morse morphism. Lemma 16 supplies cubefreeness for the exact endpoint families used here.

The proof of Theorem 15, rather than only its headline existence statement, supplies those endpoint families for every odd length at least five, including both cases at residue three modulo eight. Its hypotheses agree with the candidate's reversal treatment.

Theorem 4 applies to the length-12 seed: its condition (a) concerns the exponent of each whole image, its two markedness conditions concern first and last letters, its long cross-overlap condition is vacuous here, and its finite input bound is four throughout this threshold interval.

This review does not claim to have compared the publisher's full-text body with arXiv, or independently certify the absence of later solutions.

## 1. Boundary-marker strengthening

The four markers and their offsets are correct. A marker of equal-pair shape starts four places before a boundary; an alternating marker starts three places before it. For each of the four suffix/prefix combinations there is exactly one crossing marker. No internal marker is possible in either overlap-free image. Because image length is at least five, a five-letter marker cannot cross two boundaries. Equal markers therefore have starting positions congruent modulo the image length.

A whole image cannot be a square: its doubled image would then contain a cube, contrary to the inherited cubefreeness result applied to the admissible two-letter constant input.

The marker-free length estimate covers all boundary cases:

- A factor wholly within one block has length at most twice any proposed period.
- At one crossed boundary, absence of its marker leaves at most three letters on the left or at most one on the right. The rest is in one overlap-free block, giving length at most 2p+3.
- At two crossed boundaries, there is exactly one complete middle block. Absence of the first marker limits the left partial block to three letters; absence of the second limits the right partial block to one. The middle block has length at most 2p, and equality would make it a square. Thus the total is again at most 2p+3. If p exceeds the middle-block length, the strict inequality is immediate, so no invalid assumption that p must be one of that shorter word's proper periods is needed.
- At three or more boundaries, an internal boundary has enough surrounding letters to contain its marker.

Consequently a periodic factor of length at least 2p+4 contains a marker. For p≥5, exponent greater than 8/3 implies that length bound. The available interval of starts of five-letter windows has at least 2p integer positions, so every such window can be shifted left or right by p while remaining in the factor. Repeating the marker forces p=ck.

## 2. Partial endpoint lifting and small periods

When p=ck and the factor spans more than two periods, its number M of touched blocks is greater than 2c. The two partial endpoint blocks cannot be c blocks apart. Therefore every pair of touched blocks separated by c has at least one complete member. A column visible in the other member can be compared at distance p. Complementary image columns are injective, so all corresponding parent letters agree.

This establishes period c for the entire touched parent factor, not merely its fully visible interior. Since M≥|U|/k, the parent's exponent is at least |U|/p. No maximal-factor extension hypothesis is required for this conclusion.

For periods one through three, exponent exceeding 8/3 already forces a cube. For period four, a cubefree factor of exponent above 8/3 must have length eleven. Exhausting its four-letter cyclic root leaves only rotations of 0011. Equivalently, three-equal cyclic runs force a cube, and the remaining alternating roots force a period-two cube. The four survivors omit both 010 and 101.

At the first boundary crossed by such a length-eleven factor, at most two letters can precede the boundary, since every image ends in one of those excluded triples. A second boundary would place an entire middle block and its suffix triple inside the factor. Thus at least nine consecutive letters lie in one image with period four, contradicting overlap-freeness. This handles the period-four exception uniformly.

Together these arguments give the displayed critical-exponent bound for every cubefree finite input. At a strict threshold α>8/3, both terms in max(8/3,ce(w)) are strictly below α. At a plus threshold they are at most its underlying real value. For infinite input, applying the bound to each finite touched parent gives the same global bound by ce(w); hence the argument respects strict supremum-based freeness, rather than merely excluding individual factors at the threshold.

## 3. All lengths and the fixed seed

Every positive integer factors into an odd part times a power of two. The reviewed endpoint construction covers odd parts at least five. The identity and powers of the Thue–Morse morphism cover odd part one. Compositions preserve the same all-input threshold property and complementarity. The only remaining family is 3 times a power of two; the length-12 seed covers all its members from twelve upward, leaving precisely the two inherited impossible lengths.

The seed images have least whole-word period seven, so their whole-word exponent is 12/7. Their critical exponent is separately 7/3; these quantities have not been conflated. Their first and last letters differ. All cross-image prefix/suffix overlaps of lengths six through twelve are absent in both directions.

The common nonempty admissible input list of lengths at most four has exactly 22 words. Each has critical exponent at most two; every other such binary word has a cube. Their seed-image critical exponents are exactly the three listed values 7/3, 18/7 and 8/3. Thus the fixed finite data satisfy the universal sufficient criterion at every threshold in the required interval. This is a genuine finite certificate for a universally quantified criterion, not an inference from a sampled fixed point.

## 4. Strict endpoint obstruction

The length-five argument treats the broader binary marked class. After normalization, markedness and the admissibility of every two-letter input rule out equal adjacent letters at either end. The same two-letter inputs rule out alternating prefixes or suffixes of length four, using the other available ending or starting pair. Internal triples are excluded by one-letter inputs.

These restrictions leave exactly two possible images starting in each bit, hence the displayed four pairs. The two noncomplementary pairs contain the stated cubes; the two complementary pairs contain the stated length-eight, period-three factors on admissible three-letter inputs. All offsets and factors were independently checked. This is a complete hand exclusion. The separate 128-map enumeration corroborates it without serving as its completeness argument.

## 5. Executed checks and bindings

The author checker was copied and run without changing its original files. It passed, and the resulting JSON was byte-identical to the frozen receipt.

- Author checker: `verify_seed_and_endpoint.py`, SHA-256 `8a7671712e27f32f6d02cb0879554649a2dafd8185c8af5bfb713855286cd799`.
- Author receipt: `SEED-AND-ENDPOINT-CERTIFICATE.json`, SHA-256 `21a9fecd81289f6ad2bf0db284ccd46d0f5dba07303610493b4ec06d9a71e946`.

The separate `check_independent.py` uses maximal runs of equalities between positions separated by each candidate period. This computes critical exponents without the author's enumeration of every substring and its least period. It independently reproduced all 22 seed-image values and checked their attainment witnesses, all 128 normalized marked length-five exclusions, the four surviving period-four roots, all four marker cases, and the four endpoint witnesses. It also checked the transcription of the inherited odd-length endpoint construction for the 126 odd lengths from five through 255. That last finite list is supplementary; the full odd-length quantifier comes from the inspected source proof.

Independent checker SHA-256: `eac157f17641f1e04f81c123c65bb4e2f13a5339cbac0e4e8923dab4e6283274`.

The independent control receipt and this review are bound by `REVIEW-ACK.json`. No broader current-literature or novelty conclusion follows from these computations.
