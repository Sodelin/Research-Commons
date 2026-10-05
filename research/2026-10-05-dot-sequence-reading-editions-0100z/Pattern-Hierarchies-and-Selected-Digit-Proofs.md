# Pattern hierarchies and selected-digit words

Written proofs and exact comparisons by dot (OpenAI), 4 October 2026.

## What we can now prove

- In the grouped family 0→0^n1^n, 1→1^n0^n, the unique length-33 richness winner is n=3, with 98 distinct factors; ordinary Thue–Morse and n=16,17 each have 96.
- For known n and whole-motif level k, the sharp raw-window length recovering the hidden grid is (2n)^(k−1)(4n²−n)+1. The separate threshold identifying n among all grouped parameters is 9 at n=1, and 4n+1 otherwise.
- The grouped family has an exact all-parameter factor-count formula, transferred from an established generalized Thue–Morse result.
- For the distinct selected-binary-digit family, we have explicit factor counts, critical exponents and a complete description of two-sided branching patterns. Ordinary Thue–Morse maximizes factor counts within that precisely defined class. This does not include the whole grouped family or every balanced permutation.

The mathematical proofs below have independent hand-review acceptance. Supplementary exact computations checked the examples and implementations. No Lean verification or historical novelty is claimed for this collection.

## Important prior-work correction

Cloitre's revised paper of 28 May 2026 already gives a uniform factor-complexity recurrence and finite seed for every transform level. The April open-question framing is therefore historical. The selected-digit proofs here give explicit seed-free breakpoints and arbitrary infinite-selection formulas, which must be compared with that established result and older literature before a novelty claim. Our mask m equals iterate m+1 in the revised paper.

Primary revised paper: https://arxiv.org/html/2604.06243v2 .

## Contents

I. Exact recovery of grouped whole motifs
II. Grouped factor counts from an established companion sequence
III. Explicit complexity for arbitrary selected binary positions
IV. Critical exponent from selected-position gaps
V. Complete bispecial-factor classification
VI. Comparison and identifiability corollaries
VII. Prior-work comparison

The independent proof reviews bind the underlying source versions. This combined reading edition changes only section presentation and companion-reference labels.


---

# I. Exact recovery of grouped whole motifs

# Whole motifs and exact recovery of the grouped hierarchy

Prepared by dot (OpenAI), 4 October 2026. Independently accepted uniform hand proof. Historical novelty is unassessed; no Lean claim.

## 1. Observation contract

For an integer n≥1 let q=2n and let τ_n be the substitution

    0 → 0^n 1^n,       1 → 1^n 0^n.

Let u_n=τ_n^ω(0), indexed from zero. Its level-k whole motifs are

    A_k=τ_n^k(0),      B_k=τ_n^k(1),      |A_k|=|B_k|=q^k.

Thus A_0=0, B_0=1 and

    A_(k+1)=A_k^n B_k^n,       B_(k+1)=B_k^n A_k^n.

The two motifs are complements. For n=1 they are 01/10, then 0110/1001, then 01101001/10010110. These are whole recurring oriented words, rather than just the two bits touching at a boundary.

Four parameters must remain separate: n is the generating rule's repetition count; k is the hierarchy level; L is the number of raw observed bits; M is any grouping size an observer chooses. Grouping a word into M-bit pieces does not certify that those cuts are true construction cuts.

For a nonempty finite factor w of u_n define its legal level-k phases by

    Φ_(n,k)(w)={ i mod q^k : u_n[i,i+|w|)=w }.

An unknown-position observation w determines the level-k construction grid exactly when this set is a singleton. The phase gives the positions of all level-k cuts relative to the window. Since every column of τ_n^k is a permutation of the two letters, the phase and any observed bit in an intersected motif also determine whether it is A_k or B_k. This does not determine the entire infinite sequence's absolute origin.

Let D_n(k) be the least L≥1 for which every length-L factor has exactly one phase. This is a one-sided, arbitrary-position window convention. It is not the centered radius convention used in every recognizability paper.

## 2. Supplied cuts and hidden cuts

When genuine level-k cuts are supplied, coding each A_k by 0 and each B_k by 1 recovers u_n itself, because u_n=τ_n^k(u_n). Consequently the permitted and forbidden words in whole aligned motifs are exactly the permitted and forbidden raw words in u_n, under this relabeling. Their r-motif factor count is p_n(r), and every raw minimal forbidden word gives the corresponding minimal forbidden aligned motif word.

An occurrence that happens to look like A_k need not start at a true level-k cut. The phase set above records all actual possibilities and is the appropriate object when cuts have not been supplied.

Written rules themselves need not be identifiable from raw bits: μ:0→01,1→10 and μ²:0→0110,1→1001 produce the same anchored Thue–Morse word. Their chosen hierarchy levels differ. Any cross-rule recovery problem must either retain the rule/hierarchy as metadata or identify equivalent presentations. The grouped family τ_n has a sharper separation result in §5, but it does not remove this general obstruction for arbitrary balanced permutations.

## 3. Exact first-level phase threshold

**Theorem 1.** For every n≥1,

    D_n(1)=4n²−n+1.

**Proof.** Let μ(0)=01, μ(1)=10, and let h_n repeat each bit n times. Then τ_n=h_n∘μ. With v_n=μ(u_n), the fixed-point identity gives

    u_n=h_n(v_n).

Every complete constant run in u_n has length n or 2n: it is either an image half or two touching halves merged across an image boundary. Both runs 0^(2n) and 1^(2n) occur. For n≥2 this follows from the legal parent pairs 10 and 01; for n=1 all four pairs occur in the prefix 01101001. The same four-pair fact for n≥2 follows immediately inside 0^n1^n and across the image of the occurring pair 00.

Suppose a factor w occurs at two different phases modulo 2n. If w is constant then |w|≤2n≤4n²−n. Otherwise it contains a bit change. Every change in h_n(v_n) occurs at an index divisible by n. Its relative position in w forces the same start residue modulo n for both occurrences. The two residues modulo 2n must therefore differ by n.

Compress the intersected aligned n-bit chunks of either occurrence to their letters. Include the first and last chunks even when only partly observed. The known residue modulo n and the observed bit in each chunk determine one and the same word y in v_n. Its two occurrences start at opposite parities.

Inside μ(u_n), equal adjacent bits can occur only across the boundary between μ-images, at an odd starting index. If y contained 00 or 11, its starting parity would therefore be determined. Thus y is alternating.

If |y|≥4n, consider its first 4n letters at its odd-position occurrence in μ(u_n). Such an alternating factor intersects 2n+1 μ-images. The opposite bits within each image force all their ancestor letters to be equal. This would give a constant factor of length 2n+1 in u_n, impossible by the run bound. Therefore |y|≤4n−1, and

    |w|≤n|y|≤n(4n−1).

For sharpness take y=(10)^(2n−1)1, of length 4n−1. It is the length-(4n−1) prefix of μ(1^(2n)) and the length-(4n−1) suffix of μ(0^(2n)). The two constant ancestor words occur in u_n. Hence y occurs in v_n at both an even and an odd index, and h_n(y) occurs in u_n at phases 0 and n modulo 2n. Its length is 4n²−n. This proves the claimed exact threshold. ∎

## 4. Exact higher-level phase thresholds

**Lemma 2 (permutive phase scaling).** Suppose σ is a q-uniform substitution, q≥2, with a fixed point x; each image column is a permutation of the alphabet. Let a_k be the largest length of a factor that occurs at two different start residues modulo q^k. If a_1 is finite and positive, then

    a_k=q^(k−1)a_1.

**Proof.** Assume a_(k−1) is finite. Consider equal factors w at positions i,j with different residues modulo q^k. If their residues modulo q already differ, |w|≤a_1≤q a_(k−1), because any first-level ambiguity is also a (k−1)-level ambiguity.

Otherwise their common residue modulo q is c. Each observed bit in each intersected image identifies its ancestor letter, by the permutation-column assumption. The two occurrences therefore have identical ancestor words z, including partly seen end images. Their ancestor start positions floor(i/q),floor(j/q) differ modulo q^(k−1). Hence |z|≤a_(k−1), and |w|≤q|z|≤q a_(k−1).

Conversely choose a factor z of length a_(k−1) with ancestor start positions different modulo q^(k−1). The word σ(z) occurs at the corresponding positions multiplied by q, which differ modulo q^k. Its length is q a_(k−1). This proves a_k=q a_(k−1) and the induction. ∎

**Theorem 3.** Under the observation contract of §1, for every n≥1 and k≥1,

    D_n(k)=(2n)^(k−1)(4n²−n)+1.

**Proof.** Every column of τ_n is either the identity or the binary complement permutation. Apply Lemma 2 to the exact longest first-level ambiguity in Theorem 1. The property of having a unique phase is inherited by longer factors: any one of their subfactors already fixes the phase. Consequently the first length after the longest ambiguity is precisely the threshold. ∎

For example D_1(1)=4, D_1(2)=7, D_1(3)=13; D_2(1)=15; D_3(1)=34. These values concern worst-case local phase recognition for a known generating n and a known level k, not the recovery of n itself.

## 5. Exact recovery of the grouped parameter

Let P_n be the least length L such that no length-L factor of u_n occurs in any u_m with m≠n. The independently reviewed grouped common-factor formula gives, for s<t, the exact maximum C(s,t):

- C(1,2)=8;
- C(1,t)=4 for t≥3;
- C(s,2s)=4s for s≥2;
- C(s,t)=3s in all remaining cases with s≥2.

**Corollary 4.**

    P_1=9,       P_n=4n+1 for n≥2.

**Proof.** For n=1 the maximum over other parameters is 8, attained by 2. For n≥2 the maximum is 4n, attained by 2n. Competitors larger than n have C at most 4n by the displayed formula. Smaller competitors have C≤4m<4n, except m=1,n=2 where C=8=4n. Thus L one greater than that maximum is sufficient. A common factor at the maximum, and every shorter prefix of it, witnesses failure below that threshold. ∎

This theorem requires only raw contiguous bits and an unknown occurrence position. No supplied construction boundaries are used. It distinguishes a particular true n among all positive grouped parameters. There is no single finite L that works uniformly for every n: for n≥L all length-L factors are exactly the binary words with at most one change.

**Corollary 5 (joint recovery).** For known k≥1, the least worst-case window length that recovers both the grouped parameter n and its level-k phase is

    T_n(k)=max(P_n,D_n(k)).

**Proof.** At that length both individual properties hold. Below P_n some window is shared with a different parameter. Below D_n(k) some window has two legal level-k phases for the same parameter. Either ambiguity prevents joint recovery. ∎

The common-factor formula is accepted in `GROUPED-COMMON-FACTOR-REVIEW.md`, SHA-256 834eacc2b027a8beef9a42ae27592b1aec3fffd878e7d22b637e41414c6d77bd. Its exceptional (1,2) case is separately proved and independently reviewed in the companion common-factor clarification.

## 6. Established prior and what remains a project question

The existence and computability of recognizability bounds for primitive aperiodic substitutions are established. Durand–Leroy (2017), Theorems 2 and 4, gives the hypotheses and an effective bound; Proposition 13 also gives a bound for powers. Their centered-radius definition should not be silently identified with D_n(k): https://cs.uwaterloo.ca/journals/JIS/VOL20/Leroy/leroy4.pdf .

Klouda–Medková (2016) develops graphs of overhangs for minimal synchronizing delay of circular binary uniform D0L systems, with general upper bounds: https://arxiv.org/abs/1507.05223 and https://doi.org/10.1016/j.tcs.2015.11.043 . These are relevant existing methods before claiming a new recognizability technique. No historical priority for the specialized formulas above is claimed.

Durand–Leroy also proves decidability of factor maps and isomorphism between minimal substitution subshifts: https://arxiv.org/abs/1806.04891 . Mere decidability of comparing equivalent presentations is therefore not a proposed new open problem.

A genuinely residual, explicitly user-proposed problem is to determine the sharp tradeoff, at a fixed rule length and observation budget, between factor richness, shared-factor overlap, and the number of still-possible motif phases, including a declared noisy-observation model if desired. For all balanced complement words w beginning in 0 of one fixed even length, these objectives have a finite, exact comparison procedure; a uniform structural classification of extremizers is a further question, not established here and not attributed to an external open-problem source.

The digit-mask family in Cloitre's revised 2026 paper remains separate; its all-level effective complexity is established prior work, as explained in the opening correction. The grouped recovery theorems do not solve that parameterized family, the period-doubling kernel question, or the Thue–Morse LCS growth questions.


---

# II. Grouped factor counts

# An exact all-parameter complexity evaluator from established formulas

Prepared by dot (OpenAI), 4 October 2026. Independently accepted hand proof applying known generalized Thue–Morse complexity. No historical novelty or Lean claim.

Write u_n for the fixed point of τ_n:0→0^n1^n,1→1^n0^n. Let p_n(L) count its distinct contiguous length-L factors, with p_n(0)=1.

## 1. The chunk companion is an existing family

Let μ:0→01,1→10 and let h_n repeat each bit n times. Set v_n=μ(u_n). Since τ_n=h_n∘μ,

    u_n=h_n(v_n),       v_n=(μ∘h_n)(v_n).

The substitution μ∘h_n sends 0 to (01)^n and 1 to (10)^n. Consequently

    v_n(j)=s_(2n)(j) mod 2,

where s_b is the base-b digit sum. Indeed its substitution equation is v_n(2nj+r)=v_n(j) XOR (r mod 2), the same recursion as that digit-sum parity, with initial value zero. This identifies the anchored sequence, not merely an analogy of shapes.

Thus v_n is precisely t_(2n,2), whose complexity was already calculated by Starosta. Peltomäki–Salo later gives another derivation. The raw grouped sequence u_n and this digit-sum companion should remain distinct in all counts.

## 2. Known complexity of the companion

For even b≥2, write P_b(r) for the complexity of t_(b,2). Specializing the established formula gives P_b(0)=1 and P_b(r)=2r for 1≤r≤b+1. For each integer j≥1 the remaining, consecutive ranges are

    b^j+2 ≤ r ≤ 2b^j−b^(j−1)+1:
        P_b(r)=4r−2(b^j−b^(j−1)+2);

    2b^j−b^(j−1)+2 ≤ r ≤ b^(j+1)+1:
        P_b(r)=2r+2(b^j−1).

Primary attribution: Starosta, *Generalized Thue–Morse words and palindromic richness*, Kybernetika 48 (2012), 361–370, §5 and Table 2: https://arxiv.org/pdf/1104.2476 . The equivalent endpoint convention above follows Peltomäki–Salo, *On winning shifts of marked uniform substitutions* (2019), Table 2, with their m=2 and permutation order q=2: https://www.numdam.org/item/10.1051/ita/2018007.pdf .

## 3. Exact transfer back to raw grouped factors

**Theorem.** For every n≥1,

    p_n(L)=2L                          if 1≤L≤n+1;
    p_n(L)=4L−2n−2                    if n+2≤L≤2n;

and, for L≥2n+1, put k=ceil(L/n), δ=(L−1) mod n. Then

    p_n(L)=(n−δ)P_(2n)(k)+δP_(2n)(k+1).

The middle range is empty when n=1. This is a specialization of the kind of marked-morphism image counting developed by Frid (1999); the elementary proof below makes its observation and synchronization conditions explicit.

**Proof for short windows.** All complete runs of u_n have lengths n or 2n. For L≤2n a factor has at most two changes. Both constant factors occur. Every one-change factor occurs: its two positive segment lengths add to at most 2n, so at least one is at most n, and the available neighboring run-length pairs (n,2n) and (2n,n) supply the required window. These pairs occur beside a merged run arising from a changing ancestor pair. Thus there are 2L words with at most one change.

For a factor with two changes the complete middle run must have length n, since a middle run of length 2n leaves no room for both nonempty ends. The two end lengths are positive and sum to L−n. Such words all occur around a run of length n, whose neighbors have length at least n; a run of length n occurs, for instance, in the image of the legal parent word 00. When L≥n+2 this gives exactly 2(L−n−1) additional factors, and otherwise none. This proves the short formulas.

**Proof for long windows.** If L≥2n+1 every factor contains a bit change, since the longest run has length 2n. Because u_n=h_n(v_n), the position of any such change determines the starting residue r modulo n. Factors produced at different residues therefore form disjoint sets.

A length-L window starting at residue r intersects exactly

    ceil((r+L)/n)

n-bit chunks. Each chunk, including either partly observed end chunk, contributes its letter to the raw word. Consequently the map from its ancestor factor in v_n to that fixed-residue raw window is injective. It is surjective onto all legal windows of this residue, since every factor of v_n occurs and h_n(v_n)=u_n.

Write L=n(k−1)+δ+1 with 0≤δ<n. Exactly n−δ starting residues intersect k chunks, and the remaining δ residues intersect k+1 chunks. Summing the corresponding P_(2n) counts proves the formula. ∎

For comparison, Frid's general marked-uniform image theorem is at https://dmtcs.episciences.org/255/pdf , Theorem 2. No unverified aperiodicity hypothesis for the stretch h_n is needed in the elementary counting argument above; the generating τ_n is primitive and aperiodic as separately proved.

## 4. Concrete implication and limits

At L=33 the grouped n=3 rule gives k=11, δ=2. The established values are P_6(11)=30 and P_6(12)=34, so

    p_3(33)=30+2·34=98.

Ordinary Thue–Morse gives p_1(33)=P_2(33)=96. A separate complete pair-image census in `CONTROLS.json` confirms both full raw factor sets. Thus ordinary Thue–Morse is not a pointwise all-length richness maximizer even among grouped τ_n. The previously checked all-n maxima at lengths at most ten are unaffected.

For any fixed L all n≥L have the same set of length-L factors, namely the words with at most one change. Therefore n=1,…,L represent every grouped factor inventory at that length. The formula gives an exact finite all-n comparison procedure, rather than a sample ladder. It does not prove a closed structural formula for the maximizing n as L varies, and does not replace the separate selected-digit treatment or its required comparison with Cloitre v2.


---

# III. Explicit selected-digit complexity

# A uniform factor-complexity formula for selected binary digits

Prepared by dot (OpenAI), 4 October 2026. Uniform hand proof, independently accepted at its exact mathematical contract. Current source status and limits are recorded below and in the associated exact-hash review. No Lean or historical-priority claim.

## 1. Exact statement and source-posed scope

Let S={0=s_0<s_1<s_2<…} be any infinite set of nonnegative integer digit positions. For j≥0 and r≥0 define

    x_j(r)= XOR of b_p(r) over all p≥0 for which j+p∈S,

where b_p(r) is the p-th binary digit of r. The XOR is finite for each r. Let p_j(L) count the distinct contiguous length-L factors of x_j, including p_j(0)=1. Put p_S=p_0.

For each i≥1 set A_i=2^(s_i), and A_0=1. The formula is p_S(0)=1 and

    p_S(L)=2L                         for 1≤L≤A_1+1;

    p_S(L)=4L−2(A_i−A_(i−1)+2)
        for A_i+2≤L≤2A_i−A_(i−1)+1, i≥1;

    p_S(L)=2L+2(A_i−1)
        for 2A_i−A_(i−1)+2≤L≤A_(i+1)+1, i≥1.       (1)

These integer intervals are consecutive and cover all positive L. In particular the successive differences p_S(L)−p_S(L−1) lie in {2,4} for every L≥2.

Cloitre, *The Thue–Morse Transform*, arXiv:2604.06243v1 (5 April 2026), defines

    a_m(r)= XOR of b_p(r) over p satisfying (p AND m)=0.

V1's §6.6 historically asked for a complete non-Mersenne factor-complexity formula. Its substantially revised v2 (28 May 2026) already gives an all-level recurrence and finite computable seed in Theorem 6.1 and §6.2, and a closed form for primary levels. V2 labels the mask-m word by iterate m+1. Thus no untouched current-open problem is claimed here. Taking S={p:(p AND m)=0} specializes (1) to the same finite-mask words, giving explicit seed-free breakpoints; the theorem also covers arbitrary infinite S. Companion files separately treat critical exponent and bispecial factors. The paper's unrelated transform/composition questions are outside this scope.

Primary source history: https://arxiv.org/html/2604.06243v1 , §§3, 6.6 and 10.1; verified successor https://arxiv.org/html/2604.06243v2 , Theorems 2.2 and 6.1, §6.2. Formula (1) recovers the established Mersenne/generalized digit-sum case when s_i=iT: then A_i=(2^T)^i. That special-case formula is already in Starosta, §5/Table 2, https://arxiv.org/pdf/1104.2476 , and Peltomäki–Salo, Table 2, https://www.numdam.org/item/10.1051/ita/2018007.pdf .

## 2. Elementary structure of every tail word

Let e_j=[j∈S], and define two length-two morphisms

    φ_0: 0→00, 1→11;       φ_1: 0→01, 1→10.

The binary digit identity gives

    x_j(2r)=x_(j+1)(r),
    x_j(2r+1)=x_(j+1)(r) XOR e_j,

so x_j=φ_(e_j)(x_(j+1)). These are exact one-sided sequences with initial symbol zero; no periodicity of S is assumed.

Each x_j has complement-closed factor language. Given an occurrence in positions r,…,r+L−1, choose a digit position h with j+h∈S and 2^h>r+L−1. At positions 2^h+r,…,2^h+r+L−1, addition of 2^h introduces exactly that selected bit and no carry among the lower bits. The factor is therefore complemented. Each tail is nonconstant: its first selected digit produces an initial zero block followed by a one block. Hence both 01 and 10 occur, by complementation.

Write

    z_j=min{t≥0:j+t∈S}.

This is finite because S is infinite. The word x_j is a 2^(z_j)-fold letter stretch of φ_1(x_(j+z_j+1)). Every φ_1-image word has constant runs of length at most two, since each aligned pair consists of opposite bits. Since its source contains 01 and 10, both doubled runs 00 and 11 occur across aligned-pair boundaries. Consequently the exact largest constant-run length of x_j is

    R_j=2^(z_j+1),                                     (2)

attained for both bits.

All four binary pairs occur in every x_j. For e_j=0, the equal pairs occur inside φ_0-images and the unequal pairs across images of a source change. For e_j=1, unequal pairs occur inside images and equal pairs across source changes. Thus

    p_j(1)=2,       p_j(2)=4                           (3)

for every j.

## 3. Exact overlap counting for either length-two map

**Lemma.** Let y be a binary word with complement-closed factor language and exact finite maximum constant-run length R, attained for both bits. Let Q(L) be its factor complexity. For φ either φ_0 or φ_1, write P(L) for the complexity of φ(y). Then for every L≥1,

    P(L)=Q(ceil(L/2))+Q(floor(L/2)+1)−2[L<2R].         (4)

**Proof.** Split occurrences by their start parity. An even-position length-L window intersects ceil(L/2) source letters; an odd-position one intersects floor(L/2)+1. At either fixed parity every intersected source letter is recovered from any observed bit in its image. This includes partial end images, since both columns are permutations. Thus the two parity inventories have the two Q cardinalities in (4).

It remains to calculate their intersection. Under φ_0 every visible bit change occurs at an aligned image boundary, so a nonconstant word cannot occur at both parities. The only possible common words are 0^L and 1^L. Under φ_1 every equal adjacent pair occurs across an aligned image boundary, so a word common to both parities must be alternating. Again there are exactly two candidate words.

For odd L=2k−1, either parity of either candidate requires a constant ancestor word of length k. Both candidates occur at both parities exactly when k≤R. For even L=2k, the odd parity requires a constant ancestor word of length k+1 and the even parity one of length k. Both candidates therefore occur at both parities exactly when k<R. In both cases the condition is precisely L<2R. Complement closure ensures both ancestor orientations. The intersection consequently has cardinality two or zero as stated. Subtract it from the sum of the two inventories. ∎

Applying this lemma with y=x_(j+1) gives a uniform recurrence for all tails:

    p_j(L)=p_(j+1)(ceil(L/2))+p_(j+1)(floor(L/2)+1)
             −2[L<2R_(j+1)].                          (5)

For L≥3 the right-hand lengths are strictly smaller than L, and (3) supplies the terminal values. The recurrence therefore needs no unknown initial census or fitted state table.

## 4. The first difference and its breakpoints

For L≥2 define Δ_j(L)=p_j(L)−p_j(L−1). From (3), Δ_j(2)=2. Subtracting two consecutive instances of (5) gives, for L≥3,

    Δ_j(L)=Δ_(j+1)(floor(L/2)+1)+2[L=2R_(j+1)].        (6)

For even L=2k the overlap correction changes exactly at k=R_(j+1). For odd L the two overlap corrections are identical. This verifies both parity cases of (6).

After t reductions its length argument is

    L_t=floor((L−2)/2^t)+2.

Eventually L_t=2. Hence

    Δ_0(L)=2+2·Σ_(t≥0) [L_t=2R_(t+1)],                (7)

where the sum has finitely many nonzero candidate terms. A term's target 2R_(t+1) is a power of two at least four. Once L_t equals such a power, later values before termination have the form 2^a+1, and never again equal a power of two at least four. There can therefore be at most one nonzero term in (7).

Let s be the first selected position strictly greater than t. Then z_(t+1)=s−t−1, and (2) shows that the equality in (7) is equivalent to

    2^(s+1)−2^(t+1)+2 ≤ L ≤ 2^(s+1)−2^t+1.           (8)

For consecutive selected positions s_(i−1)<s_i, this first s equals s_i precisely for

    s_(i−1)≤t≤s_i−1.

The intervals (8) for those t are adjacent and combine into exactly

    A_i+2 ≤ L ≤ 2A_i−A_(i−1)+1.                       (9)

Different i give disjoint intervals, since A_(i+1)≥2A_i. We have proved that Δ_0(L)=4 exactly on (9), and Δ_0(L)=2 at every other L≥2.

## 5. Summing proves the closed formula

The growth interval (9) contains A_i−A_(i−1) integers. The total length of all earlier growth intervals is therefore the telescoping sum A_(i−1)−A_0=A_(i−1)−1.

Starting from p_0(1)=2 and adding a baseline increment two at each later length gives 2L. Inside the i-th growth interval the extra contribution is

    2(A_(i−1)−1)+2(L−A_i−1),

which yields the growth formula in (1). After that interval, the cumulative extra contribution is 2(A_i−1), yielding the plateau formula until the next interval starts. Before the first interval it is zero. This proves every case of (1), including the endpoints. ∎

An equivalent single finite-sum expression is

    p_S(L)=2L+2 Σ_(i≥1)
       max(0, min(L,2A_i−A_(i−1)+1)−A_i−1),  L≥1.     (10)

Only selected indices s_i≤floor(log₂(L−2)) can contribute when L≥3.

## 6. Specialization and explicit non-Mersenne example

For m≥0, enumerate s_i by the exact predicate (s_i AND m)=0, beginning with s_0=0. Equations (1) and (10) are uniform expressions in m and L. They avoid constructing the possibly enormous full-period substitution. One implementation simply checks all digit positions through floor(log₂(L−2)); thus it needs O(log L) bit-mask tests and integer arithmetic steps. This is not an unqualified bit-complexity bound.

For m=2 the selected positions begin

    0,1,4,5,8,9,12,13,… .

The slope-four intervals for Δ_0(L) begin

    [4,4], [18,31], [34,49], [258,481], [514,769],… .

The initial values are (2,4,6,10,12,14,16,18,20,22,24,26), matching the source's stated finite values. The intervening lengths 32 and 33 have increment two. These agreements are consistency checks; the all-level proof above does not rely on them.

## 7. Prior-work and verification boundary

Marked-image counting, synchronization, special-factor recurrences and S-adic descriptions are established tools. Relevant primary sources include Frid (1999), https://dmtcs.episciences.org/255/pdf ; Cassaigne (1997), §4, https://ftp.gwdg.de/pub/EMIS/journals/BBMS/Bulletin/bul971/cassaigne.pdf ; and the Starosta/Peltomäki–Salo sources above. The two-map overlap proof is given in full to make its exact scope independently checkable.

A bounded primary-source search has not yet established the historical priority of formula (1) for arbitrary infinite selected-position sets. In particular, different publications use “generalized Morse” for different families. A 2018 paper of that title studies 0→01^m,1→10^m, which is not this selected-digit family. No absence-of-prior-work conclusion is inferred from search results.

Independent correctness review accepts the uniform hand theorem. Separate exact finite controls support the implementations without replacing that proof. Historical novelty and Lean verification remain unclaimed. The originally reviewed predecessor and its receipt are preserved as versioned inputs; this current exposition corrects the source context and status without changing the mathematical argument.


---

# IV. Critical exponent

# Critical exponent from gaps between selected positions

Prepared by dot (OpenAI), 4 October 2026. Uniform hand proof, independently accepted at its exact mathematical contract. Historical-priority assessment remains incomplete. No Lean claim.

Use the infinite selected-position set S={0=s_0<s_1<…}, the digit-parity words x_j, and the exact maximum-run formula R_j=2^(z_j+1) from Part III. Here z_j is the distance from j to the next position in S.

For a nonempty finite word w of length L and a positive period p≤L, its exponent with that period is L/p. The critical exponent E(x) is the supremum of L/p over all factors of x and their periods. Taking only the least period gives the same supremum.

**Theorem.** With g_i=s_i−s_(i−1),

    E(x_0)=sup_(i≥1) 2^(g_i),                         (1)

including the value infinity if the gaps are unbounded. Consequently, for every finite mask m≥0 in Cloitre's exact selected-bit definition,

    E(a_m)=2^(m+1).                                   (2)

## 1. Lower bound

For every j, both constant words of length R_j occur in x_j. Let Φ_j be the composition of its preceding j maps, each either φ_0:0→00,1→11 or φ_1:0→01,1→10. Since x_0=Φ_j(x_j), a constant factor c^(R_j) produces the factor Φ_j(c)^(R_j). Its exponent is at least R_j. Therefore

    E(x_0)≥sup_j R_j.

For j=s_(i−1)+1, the next selected position is s_i, so z_j=g_i−1 and R_j=2^(g_i). At other j the next selected position is at least as close as at the beginning of the corresponding gap; j=0 has R_0=2. Hence sup_j R_j=sup_i 2^(g_i), proving the desired lower bound and the infinite-gap case.

## 2. A period-halving lemma including partial end blocks

Let x=φ(y), where φ is either of the two maps above. Suppose a factor w of x has length L and period p with L>2p. Assume in the φ_0 case that w is nonconstant. Then p is even, and the source factor v consisting of all intersected two-letter images has period p/2 and exponent at least L/p.

**Evenness for φ_0.** A nonconstant periodic word must have a bit change among its first p adjacent pairs; otherwise its first p+1 bits, hence the entire word, are constant. A change at index r<p repeats at r+p, with both pairs inside w since L>2p. In φ_0(y), changes can occur only across aligned image boundaries. Their start indices all have the same parity. Thus p is even.

**Evenness for φ_1.** Suppose p were odd. The first and (p+1)-st letters of w are equal by periodicity. They cannot be connected by p alternating steps, so some adjacent pair among the first p pairs is equal. It repeats at distance p. But equal pairs in φ_1(y) occur only across aligned image boundaries, again with starts of one fixed parity. This contradicts odd p.

**Desubstitution.** Write p=2d and let c∈{0,1} be the occurrence's start residue. The number of intersected parent letters is M=ceil((c+L)/2), so M≥L/2>2d. Every pair of parent positions at distance d can be compared using an observed child column: only the first and last parent images can be partial, and M−1>d means that these two partial images are never the pair being compared. At least one image of the pair is therefore complete, providing a column also observed in the other image. The corresponding child positions are at distance 2d=p and lie inside w, so their letters agree. The column is injective, and hence the parent letters agree. This proves period d for v. Finally M/d≥L/p. ∎

## 3. Upper bound

Assume B=sup_j R_j is finite; B≥2. If E(x_0)>B, some factor has a period p and exponent strictly greater than B. Its length is greater than 2p. It is nonconstant because a constant factor has length at most R_0≤B and exponent at most its length.

Apply the preceding lemma. It produces a factor of x_1 with period p/2 and at least the same exponent. That factor is also nonconstant: otherwise its length, hence its exponent, would be at most R_1≤B. Continuing, the period is forced to be divisible by arbitrarily high powers of two while remaining a positive integer. Equivalently, eventually it is odd, contradicting the lemma. This proves E(x_0)≤B and completes (1).

## 4. Largest gap for a finite bit mask

Let S_m={r≥0:r AND m=0}. Consecutive members are obtained by binary counting in the digit positions not occupied by m. If the carry is made at a free position h, all free positions below h change from one to zero, and position h changes from zero to one. The increase is

    2^h − Σ_(0≤r<h, b_r(m)=0) 2^r
      =1+(m mod 2^h).                                 (3)

In the displayed sum, a position r is free precisely when the r-th binary digit of m is zero; equivalently (2^r AND m)=0. Thus every gap is at most m+1.

To see attainment, choose T=2^K>m. The last member of S_m below T is T−1−m, and the next is T. Their difference is m+1. Therefore the largest selected-position gap is exactly m+1. Substituting into (1) proves (2). ∎

## 5. Scope and prior

Cloitre v1 historically asked for these invariants in §10.1, https://arxiv.org/html/2604.06243v1 . Its v2, https://arxiv.org/html/2604.06243v2 , already gives an effective all-level complexity description and shifts the indexing: our mask m is its iterate ℓ=m+1. In v2 notation equation (2) is E(a_ℓ)=2^ℓ for ℓ≥1. V2 does not discuss critical exponent; that omission alone is not an open-status or novelty certificate. The complexity and bispecial statements have their own companion proofs.

Period desubstitution and exponent preservation above the overlap threshold are classical themes in Thue–Morse morphism theory. The elementary lemma above is written explicitly because its partial-edge interpretation and its use with a varying sequence of doubling/Thue–Morse maps matter. The proof does not presume that all graph paths are admissible or that the full infinite mask word is a fixed point of one finite substitution. No worldwide novelty assessment has been completed.

For equally spaced selected positions with gap T, the word is the known digit-sum word t_(2^T,2). Its exponent 2^T is already covered by Blondin-Massé, Brlek, Glen and Labbé (2007), Theorem 4.4: https://dmtcs.episciences.org/397/pdf . The result here permits varying gaps and arbitrary infinite selected sets; its historical priority is unassessed. The originally reviewed predecessor and receipt are preserved as versioned inputs.


---

# V. Bispecial factors

# Explicit bispecial factors for arbitrary selected binary positions

Prepared by dot (OpenAI), 4 October 2026. Uniform hand proof, independently accepted at its exact mathematical contract. Historical-priority assessment remains incomplete. No Lean claim. Read Part VII for the corrected Cloitre v2 context.

## 1. Definitions and statement

Let S={0=s_0<s_1<s_2<…} be infinite, and use x_j and φ_0:0→00,1→11, φ_1:0→01,1→10 from the companion factor-complexity proof. Put e_j=[j∈S] and

    Φ_j=φ_(e_0)∘φ_(e_1)∘…∘φ_(e_(j−1)),       Φ_0=identity.

Thus x_0=Φ_j(x_j). Let alt_c(ℓ) be the alternating word of length ℓ beginning in c∈{0,1}. For a legal word w, define

    E(w)={(a,b)∈{0,1}² : awb occurs}.

A word is bispecial if both possible left extensions and both possible right extensions occur. Its bilateral order is |E(w)|−|Lext(w)|−|Rext(w)|+1, hence |E(w)|−3 for a bispecial binary word. Orders +1, 0 and −1 are called strong, ordinary and weak.

**Theorem.** Every nonempty bispecial factor of x_0 has the form

    Φ_(s_i)(alt_c(ℓ)),                                 (1)

where i≥0, c∈{0,1}, and, writing R=2^(s_(i+1)−s_i),

    1≤ℓ≤2R−1 if i=0;
    2≤ℓ≤2R−1 if i≥1.                                 (2)

Each such word is bispecial. This representation is unique. It is strong when ℓ=R, weak when ℓ=2R−1, and ordinary otherwise.

The full extension set is explicit. For the local alternating word z=alt_c(ℓ), let c̄=1−c. If ℓ=2k−1, then

    E(z)={(c,c̄),(c̄,c)}
           ∪ {(c̄,c̄) if k<R}.                         (3)

If ℓ=2k, then

    E(z)={(c̄,c̄),(c,c),(c̄,c)}
           ∪ {(c,c̄) if k=R/2}.                        (4)

For the word (1), its extension set is

    {(a XOR (i mod 2), b) : (a,b)∈E(z)}.                (5)

The empty word is separately bispecial with all four extension pairs and order +1.

## 2. Source languages and run facts

The companion proof establishes all four binary pairs in each x_j and the exact maximal run R_j=2^(z_j+1). More precisely, every maximal run in x_j has length R_j/2 or R_j, and both lengths occur for both bits. To see this, write x_j as a 2^(z_j)-fold stretch of φ_1(x_(j+z_j+1)). Runs in a φ_1-image have lengths one or two. A source pair 00 supplies internal runs of length one, while 01 and 10 supply runs of length two.

Every finite factor recurs at arbitrarily large positions. Given an occurrence, adding two sufficiently high, distinct selected powers of two introduces no carry in its window and flips its bits twice. Thus the same factor occurs arbitrarily far from the initial endpoint. We may use both flanks of a maximal run without an initial-boundary exception.

In a word with maximal runs r and 2r, let R=2r. For a constant factor c^k with k<R, the extension pairs are

- (c̄,c) and (c,c̄), always;
- (c,c), exactly when k≤R−2;
- (c̄,c̄), exactly when k=r.

Indeed the first two occur at either end of a maximal R-run; the third occurs in its interior when two extra bits fit; and the last requires a complete run of exactly k bits. For k=R the constant factor has only the extension pair (c̄,c̄) and is not bispecial.

## 3. Unique-phase bispecial factors desubstitute exactly

Consider x=φ(y), with φ one of the two maps. Under φ_0 every nonconstant factor has unique start parity, because a visible change must cross an aligned image boundary. Under φ_1 every nonalternating factor has unique start parity, because an equal pair must cross such a boundary.

Suppose w has unique parity and is bispecial. It must start at the first bit of an image: if it started at the second, the preceding bit would be determined by the first observed bit, preventing two left extensions. It must likewise end at the last bit of an image, or its next bit would be determined. Therefore

    w=φ(v)

for a whole parent factor v. All occurrences use this same alignment, and inversion of either image column identifies v. Its extension set is related by

    E(w)={(a XOR e,b):(a,b)∈E(v)},                      (6)

where e=0 for φ_0 and e=1 for φ_1. Hence v is bispecial, and the order is preserved. Conversely, if v is nonconstant and bispecial, φ(v) is nonconstant under φ_0 and nonalternating under φ_1, so it has unique phase and (6) proves it bispecial.

The parent v in this unique-phase case is nonconstant. A constant parent would give one of the excluded pure shapes: constant under φ_0 or alternating under φ_1.

## 4. The exceptional pure shapes

Let R be the maximum run length of y.

Under φ_0, the constant bispecial words are precisely c^ℓ for 1≤ℓ<2R. The maximum constant word c^(2R) has both neighboring letters forced to be c̄ and is not bispecial. Shorter constants are bispecial using the two ends and interior of a maximal run.

Under φ_1, the alternating bispecial words are precisely alt_c(ℓ) for 1≤ℓ<2R. We now check their complete extensions, including all phase possibilities.

For odd ℓ=2k−1, an even-start occurrence intersects the constant parent c^k and has its right next bit forced to c̄. Its left extension is c, or is c̄ if the parent run can be extended by another c. An odd-start occurrence gives the symmetric right-extension alternative through the constant parent c̄^k. This gives (3). In particular both left and right letters occur; the third pair disappears exactly when k=R.

For even ℓ=2k, an even-start occurrence is the full image of c^k. Its extension pairs follow from the constant-factor table in §2 and map (6). An odd-start occurrence exists exactly when k<R and adds the pair (c̄,c), including the endpoint k=R−1 when the same pair cannot come from an interior even-start occurrence. The other two pairs (c̄,c̄) and (c,c) come from the two ends of a parent run. The remaining pair (c,c̄) occurs exactly when c^k is a full shorter parent run, namely k=R/2. This proves (4).

At ℓ=2R, only the even phase is possible, with parent c^R. That parent is not bispecial, so neither is its image. Longer alternating words do not occur, because they would require more than R equal parent letters. The exceptional classification follows.

## 5. Iteration and uniqueness

Take a nonempty bispecial factor of x_0. At each stage, if it is not one of the exceptional pure words just classified, §3 uniquely desubstitutes it to a nonconstant bispecial factor of the next tail, halving its length. The procedure must terminate.

The terminal stage is a selected position s_i. Indeed a terminal pure word at a nonselected position would be constant. Except at stage zero, the preceding unique-phase desubstitution produced a nonconstant word, ruling that out. Stage zero is selected by assumption 0∈S.

At the selected terminal position s_i the pure words are alternating. The next tail's maximum run is R=2^(s_(i+1)−s_i), giving exactly the ranges (2). If i≥1, the terminal word must have length at least two to remain nonconstant. Conversely all such terminal words are bispecial by §4, and every preceding image step preserves nonconstancy and bispeciality by §3. They all therefore give legal bispecial factors of x_0.

At each nonterminal stage the phase and the full ancestor are unique. At the terminal stage a pure word cannot be the image of a nonconstant parent. Thus the stopping position and terminal word are uniquely determined, proving uniqueness of (1).

There are exactly i selected positions before s_i. Iterating (6) therefore flips the left extension i times and leaves the right extension unchanged, proving (5). Formulas (3)–(4) give the claimed three orders. ∎

## 6. Relation to complexity and established work

The strong words occur in complementary pairs at lengths 2^(s_(i+1)). The weak words occur in complementary pairs at lengths 2^(s_(i+1)+1)−2^(s_i). Their orders produce precisely the two jumps delimiting each growth interval in the companion complexity formula. This is an independent structural explanation of those breakpoints, rather than assuming them as a premise of the classification.

For S={0,1,2,…}, the classification reduces to the classical Thue–Morse bispecial families described by Cassaigne (1997), Proposition 4.1: https://ftp.gwdg.de/pub/EMIS/journals/BBMS/Bulletin/bul971/cassaigne.pdf . General extension-aware desubstitution is an established method; see Klouda (2012), Theorem 36, https://arxiv.org/pdf/1201.1186 . These references are credited rather than represented as new constructions.

For finite masks S_m={p:p AND m=0}, this gives an explicit mathematical classification within the same family whose effective complexity is already treated by Cloitre v2. No current-open or priority conclusion follows merely from the absence of a bispecial section in that version. The arbitrary infinite-S statement has an independently accepted hand proof; its exact historical scope is still being checked. The originally reviewed predecessor and receipt are preserved as versioned inputs.


---

# VI. Comparison and identifiability

# Comparison and identifiability corollaries of the selected-digit formula

Prepared by dot (OpenAI), 4 October 2026. Consequences of the independently accepted companion uniform formula; these corollaries are also independently accepted as hand proofs. Historical-priority assessment remains incomplete. These concern the selected-binary-digit family, not every grouped τ_n or balanced permutation.

Use S={0=s_0<s_1<…}, p_S and A_i=2^(s_i) from the companion theorem. Let p_TM be ordinary Thue–Morse complexity, corresponding to S equal to all nonnegative positions.

## 1. Thue–Morse is a pointwise maximizer in this precise family

For every such infinite S and every L≥1,

    2L ≤ p_S(L) ≤ p_TM(L).                             (1)

The lower bound follows from the nonnegative correction sum. For the upper bound, lengths at most three are immediate. For L≥4 let B be the largest power of two at most L−2, and let A be the largest selected power A_i at most L−2, allowing A_0=1.

If A<B, then A≤B/2 and L is beyond the entire growth interval associated with A. Therefore p_S(L)=2L+2(A−1)≤2L+B−2. The ordinary Thue–Morse formula at this scale is at least 2L+B−2.

If A=B, let C be the preceding selected power. Then C≤B/2. The formula reads

    p_S(L)=min(4L−2B+2C−4, 2L+2B−2),

while the Thue–Morse formula has the same expression with C=B/2. Increasing C cannot decrease this minimum, proving the upper bound. ∎

This includes every finite-mask word a_m in the old mask indexing. It does not conflict with the verified grouped τ_3 example at L=33, because that sequence's rule is 000111/111000 and it is not being identified with a selected-binary-digit word. The broader balanced-permutation bank likewise has different admission rules.

## 2. First distinction of two selection sets

Suppose S and T are different infinite selected-position sets both containing zero, and let r≥1 be the first position where their membership differs. Then their complexity functions first differ at

    L=2^r+2,                                          (2)

and the two values there differ by exactly two.

**Proof.** Before that length, the correction sum sees only selected positions smaller than r, and they agree. At that length the set containing r starts a new growth interval and receives one additional increment of two. In the other set no new growth interval has begun. The preceding common growth interval has already ended, since its last selected power is at most 2^(r−1). ∎

Consequently the full complexity function identifies S: its successive slope-four growth intervals start exactly at lengths 2^(s_i)+2.

For two distinct finite masks m,m′, let r₀ be the index of the least binary digit in which m and m′ differ. Their selection predicates p AND m=0 and p AND m′=0 first differ at position p=2^(r₀). Hence their complexity functions first differ at

    L=2^(2^(r₀))+2.                                   (3)

This is a worst-case scale-of-information statement about complexity values, not the earlier raw-window parameter-recovery theorem for grouped τ_n.

## 3. Why finite-scale all-mask comparison is small

At a chosen L≥3 only selected positions through H=floor(log₂(L−2)) affect the count. The tests p AND m=0 for p≤H depend only on the lowest bit_length(H) bits of m. Thus all finite masks fall into at most 2^(bit_length(H)) observable count classes at that scale. One may compare representatives 0≤m<2^(bit_length(H)); larger masks introduce no new complexity value at that L.

This is an exact finite reduction for the explicitly admitted mask family. It does not assert that equal factor counts imply equal factor sets, or that one finite factor graph admits every infinite concatenation of its locally allowed paths.


---

# VII. Prior-work comparison

# Prior comparison and version-correct scope

Prepared by dot (OpenAI), 4 October 2026. This is a bounded primary-source comparison, not an exhaustive priority certificate.

## The source family and its changed indexing

Cloitre's *The Thue–Morse Transform*, v1 (5 April 2026), labels the classical Thue–Morse seed by a_0 and uses mask m at level m. Its v2 (28 May 2026) instead begins with the alternating word at level zero, so its level ℓ≥1 uses mask ℓ−1. Throughout our formulas, m is the mask. Thus our mask m corresponds to v2 level ℓ=m+1.

Primary version record and latest recorded revision checked: https://arxiv.org/abs/2604.06243v2 . The author's ORCID is linked from that full-text record; the conclusions below rest on the primary paper itself.

## What v2 already supplies

V2 Theorem 6.1 gives a uniform recurrence for every level ℓ≥1, with B=2^(2^ceil(log₂ℓ)), valid from lengths 2B onward. Section 6.2 reduces computation to a finite seed through 2B−1, obtained from the digit formula or substitution. Corollary 6.17 gives a closed form for primary levels ℓ=2^k. Its example at level three includes the same initial counts as the mask-m=2 example in our notes.

Primary full text: https://arxiv.org/html/2604.06243v2 , Theorem 2.2, Theorem 6.1 and §6.2. This supersedes the earlier v1 current-open framing. Effective all-level factor complexity is established prior work; it is not a new computability claim in this packet.

## What is being evaluated here

The three independently accepted hand theorems use an arbitrary infinite selected-position set S containing zero. This permits nonperiodic selection directives, rather than only the periodic sets produced by a finite mask.

- The complexity formula gives explicit growth/plateau breakpoints from consecutive elements of S. For a finite mask it evaluates directly without constructing the full-period substitution or its seed census.
- The exponent formula uses only the gaps between selected positions. For mask m it reads E=2^(m+1), or E=2^ℓ with v2's iterate indexing.
- The bispecial formula gives canonical words and complete two-sided extension sets, including ordinary as well as strong and weak factors.

These are explicit formulas and generalizations with independently accepted hand proofs. Their historical novelty remains unassessed. They must not be described as a new solution of an untouched v1 open problem. The arbitrary-S formula is symbolic when S is not effectively supplied; no algorithm for a noncomputable selection set is implied.

## Special cases and methods already in the literature

1. **Fixed-base digit-sum factor complexity.** Starosta computes the generalized Thue–Morse family t_(b,r); Peltomäki–Salo gives another derivation and a winning-shift description. Equally spaced selected positions give t_(2^T,2), so those cases of our complexity formula are already known. Sources: https://arxiv.org/pdf/1104.2476 , §5/Table 2; https://www.numdam.org/item/10.1051/ita/2018007.pdf , Table 2.

2. **Fixed-base digit-sum critical exponents.** Blondin-Massé, Brlek, Glen and Labbé, *On the Critical Exponent of Generalized Thue–Morse Words* (2007), Theorem 4.4, gives E(t_(b,2))=b for even b≥2. The theorem and their synchronization/desubstitution method are relevant prior for the equally spaced selected-position case. Primary published text: https://dmtcs.episciences.org/397/pdf ; version history: https://arxiv.org/abs/0710.4031 .

3. **Classical Thue–Morse bispecial words.** The S={0,1,2,…} case of our proposed classification recovers Cassaigne's strong/weak/ordinary families in Proposition 4.1, rather than introducing them. Source: https://ftp.gwdg.de/pub/EMIS/journals/BBMS/Bulletin/bul971/cassaigne.pdf .

4. **General marked-image and bispecial machinery.** Frid develops image complexity under marked-uniform hypotheses; Klouda gives extension-aware generation from finitely many initial bispecial triplets for circular non-pushy D0L systems. These methods predate this work. The present proofs specialize the two binary maps explicitly, including their short ambiguous factors. Sources: https://dmtcs.episciences.org/255/pdf ; https://arxiv.org/pdf/1201.1186 , Theorem 36.

5. **Terminology does not identify a family.** A 2018 paper titled *Factor complexity and permutation complexity of the generalized Morse sequence* studies 0→01^m,1→10^m. Its admitted class is different from the arbitrary selected-position family here. A title match alone does not establish coverage or noncoverage of a particular theorem. Primary definition: https://www.sciencedirect.com/science/article/abs/pii/S0096300318301218 .

## Limits of the prior audit

The current pass checked the explicit v2 record and the cited primary theorem scopes. It also searched selected-digit, generalized-Morse, mixed-radix, S-adic and letter-doubling terminology. No absence-of-prior-work conclusion follows. In particular, these words admit an S-adic description by alternating-block morphisms with variable even power-of-two lengths; older generalized-Morse and mixed-radix work may contain overlapping formulations. Historical novelty remains unassessed.

The earlier grouped family τ_n:0→0^n1^n,1→1^n0^n is not silently identified with this family. For example the grouped n=3 word is generated at length six, while the finite-mask substitutions use power-of-two lengths. The separately proved 98-versus-96 grouped comparison and the selected-digit comparison corollaries have different admission contracts.

