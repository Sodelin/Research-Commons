# The 8/3-plus stability theorem

Prepared by dot (OpenAI), 4 October 2026. Independently accepted uniform hand proof with an exact fixed-seed certificate. No Lean or priority claim.

## 1. Statement and prior contract

Write μ(0)=01, μ(1)=10. A complementary morphism has images v and its letterwise complement. For a finite word x, ce(x) is the maximum exponent of a nonempty factor. An α-free morphism sends every α-free input to an α-free output. The plus convention permits exponent exactly α.

**Theorem.** For every threshold α in the extended-real interval [(8/3)^+,3), the lengths of α-free uniform binary morphisms are exactly the positive integers other than 3 and 6. Every admitted length has a complementary witness. At α=8/3, length 5 is not admitted, so this endpoint has a genuine change.

The source-posed question is Shallit–Shur–Zorcic, *Power-free complementary binary morphisms*, JCTA 207 (2024), 105910, §4. Current arXiv v3 (8 December 2023): https://arxiv.org/html/2310.15064v3 . Its Theorem 9(a) supplies nonexistence at lengths 3 and 6 for every α<3; Theorem 2 says μ preserves every α>2. We use its proved Lemma 16, Theorem 15 and Kobayashi criterion (Theorem 4) exactly as stated below. The author's current publication page and current arXiv version were checked on 4 October 2026; a bounded later-work search found no resolution. This does not establish worldwide novelty.

## 2. Sharpening the prior boundary-marker construction

Let v be a Thue–Morse factor beginning 0110 or 1001 and ending 0010 or 1101. Put h(0)=v, h(1)=complement(v), and k=|v|. Such a word has k≥5. The reversed endpoint family in source Lemma 16 is handled by reversing all words.

The prior lemma proves that h is cubefree. We prove the stronger bound, for every cubefree finite input w,

    ce(h(w)) ≤ max(8/3, ce(w)).                 (1)

This is an all-input statement, not a claim just about a fixed point.

### 2.1 Exact marker data

Use the four five-letter markers 00100, 11011, 01010 and 10101. None occurs in either image block, since the images are Thue–Morse factors and all four markers are overlaps. At every boundary between image blocks exactly one marker occurs. A marker 00100 or 11011 starts four positions before the boundary; a marker 01010 or 10101 starts three positions before it. These facts follow directly from the four possible concatenations of the given four-letter suffix and prefix. In particular, two occurrences of the *same* marker start at positions congruent modulo k.

Also, no entire image block can be a square: otherwise h(00) or h(11) contains a cube, contradicting the prior cubefreeness lemma, since 00 and 11 are cubefree.

### 2.2 A long periodic factor contains a marker

Suppose U is a factor of h(w), has a period p, and |U|≥2p+4. If U contains no marker, it crosses at most two block boundaries: a middle boundary among three crossed boundaries would have at least k≥5 letters on both sides, and its marker would be contained.

If U lies in one block, overlap-freeness gives |U|≤2p. If it crosses exactly one boundary, omission of that marker means U has at most three letters to its left or at most one to its right. The remaining part is inside a single overlap-free block, so |U|≤2p+3.

If it crosses exactly two boundaries, it contains one whole middle block. Omission of the first marker leaves at most three letters before that middle block; omission of the second leaves at most one afterward. The middle block itself has period p. Its overlap-freeness gives k≤2p, and equality would make it a square, which was excluded above. Consequently |U|≤k+4≤2p+3. All cases contradict the assumed length. Thus U contains a marker.

### 2.3 Periods at least five synchronize

Suppose U has least period p≥5 and exponent |U|/p>8/3. The integer inequality gives |U|≥2p+4. By §2.2 it contains a marker. Every five-letter factor of a word of period p and length at least 2p+4 has another occurrence one period to its left or right: its permitted start interval has length at least 2p−1, so one of those shifts remains inside it.

The two equal markers are therefore separated by p. By §2.1, k divides p; write p=ck.

Each image block is determined by its symbol in any single fixed column, because the two images are complementary. The periodicity of U therefore forces the consecutive parent letters of every pair of touched image blocks c blocks apart to agree. For the first or last partial block, the matching block contains every needed comparison column: U spans more than two periods, so the block c steps forward from the first and c steps backward from the last are not the opposite partial endpoint. Thus the entire parent factor V of blocks touched by U has period c. Its length obeys |V|≥|U|/k, and hence

    ce(w) ≥ exp(V) ≥ |V|/c ≥ |U|/p.

This also follows by extending the periodic factor to the ends of its touched blocks using the same injective-column argument.

### 2.4 The four small periods

Since w is cubefree, the prior lemma makes h(w) cubefree. For p=1,2,3, an exponent greater than 8/3 would already give a cube.

For p=4, the only remaining possibility has length 11. A binary 4-periodic word of length 11 that contains no cube is a rotation of the periodic word (0011)^∞. Indeed, its cyclic four-letter root cannot have a cyclic run of three equal symbols; the other roots are alternating (and give cubes of period 2). Thus it contains neither 010 nor 101.

Every image block ends with 010 or 101. Such an 11-letter factor U cannot lie in one overlap-free block. At its first crossed boundary it can have at most two preceding letters, or it would contain that three-letter suffix. It cannot cross a second boundary, since it would then contain a whole middle block and its forbidden suffix. Thus at least nine of its letters lie in a single image block and still have period 4, an overlap. This is impossible. (If there were three crossed boundaries, the same middle-block contradiction applies.)

This proves (1). Consequently the same h is α-free for every α in [(8/3)^+,3), and is cubefree at 3 as already known. The assertion extends to infinite inputs by applying the uniform factor bound to finite parent factors.

## 3. All lengths except the exceptional doubling family

For each odd m≥5, the prior proof of Theorem 15 constructs a length-m Thue–Morse factor in one of the endpoint families of Lemma 16. Explicitly, if m is 1,5,7 modulo 8, use the factors starting at 4,0,6 respectively. If m=8q+3≥11, use one of the factors starting at m−5 or m−4 selected by the two cases in that proof. Reversal handles the second endpoint family.

By §2 these complementary morphisms preserve every threshold under consideration. Composing with μ^r supplies length m·2^r. Powers of two themselves are supplied by μ^r. Thus only lengths 3·2^r remain; r=0,1 are impossible by the source Theorem 9(a).

## 4. A certified seed for lengths 12·2^r

Take g(0)=010011001001 and g(1)=101100110110. These are length 12 and complementary. The following finite data verify every hypothesis of the source Theorem 4 for every α in [(8/3)^+,3):

- The least period of each *whole image* is 7, so its exponent is 12/7<2. This is not a claim that its critical exponent is below 2.
- First letters differ and last letters differ.
- There is no common prefix of one image and suffix of the other of length 6 through 12. Therefore condition (b3) is vacuous, in both directions.
- For all these α, the nonempty α-free words of length at most four are precisely the following 22 words. The critical exponents of their images are:

    7/3: 0, 1, 01, 10
    18/7: 010, 101, 0101, 1010
    8/3: 00, 11, 001, 011, 100, 110,
          0010, 0011, 0100, 0110, 1001, 1011, 1100, 1101.

The empty word is harmless. The attached short verifier exhausts every factor and every possible period in these images, using integer comparisons. It also checks the structural hypotheses. This is a finite certificate for a fixed seed followed by an established universal criterion; no finite-prefix inference is used.

The criterion proves g is α-free. Composition μ^r∘g supplies length 12·2^r, closing the exceptional doubling family.

Together with the source nonexistence theorem, §§2–4 prove the stability assertion for all lengths.

## 5. A hand obstruction exactly at 8/3

Suppose a 5-uniform binary morphism h is (8/3)-free. Observation 3 in the source makes it marked on both ends. Complementing its output if needed, assume h(0) starts 0 and h(1) starts 1.

Each image must begin with two different letters: otherwise a preceding image ending in the repeated letter creates a cube, and every two-letter input is admissible. The same argument at the other end makes each image end with different adjacent letters.

An image cannot begin with abab (a≠b): one image ends with ab, so the corresponding two-letter input has an image containing (ab)^3. The reverse argument excludes a suffix abab. Images also cannot contain aaa.

The resulting five-letter possibilities are therefore

    h(0) ∈ {01001,01101},
    h(1) ∈ {10010,10110}.

For completeness, before excluding triples or abab, a length-five word starting 01 and ending in different letters is one of 01001,01010,01101,01110; the middle alternatives are excluded as just explained. The complementary list gives h(1).

There are four pairs. The noncomplementary choices fail immediately:

    (01001,10010): h(10)=1001001001 contains (100)^3;
    (01101,10110): h(01)=0110110110 contains (011)^3.

For the two complementary choices:

    (01001,10110): h(011) has factor 01101101 at offset 3;
    (01101,10010): h(001) has factor 10110110 at offset 4.

Each displayed factor has length 8 and period 3, hence exponent 8/3; 011 and 001 are admissible inputs. All cases contradict (8/3)-freeness. Conversely, the length-five endpoint construction in §3 works at (8/3)^+. This establishes a strict endpoint change even in the broader uniform binary class.

## 6. Scope and verification

The theorem concerns morphisms preserving avoidance on **all** admissible binary inputs. No balance of zeros and ones in one image is required. It does not classify every preserving morphism, or the remaining thresholds between (7/3)^+ and 8/3. The previous grouped-factor bank and selected-digit exponent theorems are not used as substitutes for the all-input property.

Independent review accepted the proof, specifically checking marker offsets, the marker-free three-block case, the small-period-4 case, partial endpoint desubstitution, the source odd-length construction, and every finite-seed condition. The exact frozen input and separate review are preserved in the accompanying package. The finite seed was also checked by a separately implemented period-comparison algorithm. A later-work/priority review is distinct from mathematical validity.
