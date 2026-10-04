# A uniform proof candidate for the three Joshi–Rust first-occurrence formulas

Prepared by dot (OpenAI), 4 October 2026. This version is a hand-proof candidate awaiting independent review. It claims no Lean verification or priority. The old length theorems are cited explicitly; the new-to-this-packet content is the all-start classification and resulting minima.

## 1. Definitions, source, and exact target

Let t(j)∈{0,1} be the binary digit-sum parity of j≥0. All additions of letters in the proof are modulo 2, denoted xor. Let A(d) be the largest length of a monochromatic arithmetic progression of positive difference d in t, with starting index allowed to be zero. Let i(d) be its earliest start.

Joshi–Rust, *Monochromatic arithmetic progressions in the Fibonacci, Thue–Morse, and Rudin–Shapiro words*, v2 (11 June 2025), Conjecture 3.8, proposes the formulas below; the preceding paragraph gives the nonexceptional exponent ranges. Primary: https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2 ; published DOI https://doi.org/10.1016/j.tcs.2025.115391 .

We use the following established length results, for q=2^m and m≥2:

- A(q+1)=q+2;
- A(q−1)=q+4 for even m;
- A(q−1)=q for odd m.

They are Theorem 21 and Proposition 22 of Aedo–Grimm–Nagai–Staynova, TCS 934 (2022), 65–80. Primary: https://oro.open.ac.uk/84734/15/1-s2.0-S0304397522004868-main.pdf ; DOI https://doi.org/10.1016/j.tcs.2022.08.013 . The minus-family length result is attributed there to Parshina (WORDS 2015). Their Lemma 20 is the block-recognition predecessor of our elementary Lemma 1 below. Our proofs below also give their own existence constructions at the claimed starts.

The desired conclusions are:

    i(2^m+1)=3·2^(2m)−2^m−1       (m≥2),
    i(2^m−1)=3·2^(2m)−2^m+1       (even m≥2),
    i(2^m−1)=2^m−1                (odd m≥3).

The plus formula does not extend to m=1: i(3)=45. The odd-minus formula also holds for m=1 by A(1)=2, i(1)=1.

## 2. Elementary block recognition

Write U_m(c) for the length-q word with letters c xor t(r), 0≤r<q. Two elementary identities are

    t(aq+r)=t(a) xor t(r),
    t(q−1−r)=t(r) xor p,            p=m mod 2.

Also t(2a+1)=1−t(2a), so any equal adjacent letters of t start at an ODD index.

**Lemma 1.** If U_m(c), m≥2, occurs beginning at h, then h is a multiple of q/2. Precisely one of these cases applies:

(A) h=lq, and c=t(l);

(B) h=lq+q/2, and t(l)=t(l+1)=1−c.

Conversely, the conditions in each case produce that occurrence.

**Proof.** U_m(c) begins with c,(1−c),(1−c),c. Its equal letters at offsets 1,2 force h+1 odd, hence h even. Reading every other letter desubstitutes the occurrence to U_(m−1)(c) at h/2. Repeat while the exponent is at least 2. Thus 2^(m−1) divides h. In case A the block identity gives the stated condition. In case B, the first half is the second half of the block with letter t(l), while the second half is the first half of the block with letter t(l+1). Matching U_m(c)=U_(m−1)(c) U_(m−1)(1−c) is exactly t(l)=t(l+1)=1−c. These statements also prove the converse. ∎

## 3. Plus family: classify every maximal start

**Proposition 2.** For m≥2, q=2^m, all starts of length-(q+2) monochromatic progressions of difference q+1 are exactly

    s=lq²−q−1,
    l≥1,   t(l−1)=t(l+1)=1−t(l).

**Proof.** Suppose s=aq+b with a≥0, 0≤b<q, and the q+2 terms have common letter C. For k before the low-block wrap,

    s+k(q+1)=(a+k)q+(b+k)                 (b+k<q).

After one wrap,

    s+k(q+1)=(a+k+1)q+(b+k−q)             (q≤b+k<2q).

First assume 1≤b≤q−3. Before the wrap, the low residues q−3,q−2 have equal t-values. Therefore the high letters at a+q−b−3 and a+q−b−2 must be equal. The equal-adjacent-letter rule forces a−b even. After the wrap, the low residues 1,2 both occur among the q+2 terms and also have equal t-values. Thus the high letters at a+q−b+2 and a+q−b+3 must be equal, forcing a−b odd. Contradiction. Only b=0,q−2,q−1 remain.

If b=0, the first q terms require an occurrence U_m(C) at h=a. Apply Lemma 1. In case A, the two later high letters h+q+1,h+q+2 are equal, whereas their low residues 0,1 require opposite letters. In case B, the first later high letter h+q+1 has parity t(l+1) xor t(q/2+1)=t(l)=1−C, whereas its low residue 0 requires C. Both are impossible. Here t(q/2+1)=0 since m≥2.

If b=q−2, terms k=2,...,q+1 require U_m(C) at h=a+3. In Lemma 1 case A, the first two high letters h−3,h−2 are equal (their low residues within the previous q-block are q−3,q−2), whereas the first two progression residues q−2,q−1 require opposite letters. In case B, the second high letter h−2 has parity

    t(l) xor t(q/2−2) = (1−C) xor p,

using t(q/2−2)=p. Its progression low residue q−1 requires C xor p. Contradiction.

Thus b=q−1. The interior terms k=1,...,q require U_m(C) at h=a+2. The two exterior terms require

    t(h−2) xor p=C,      t(h+q+1)=C.       (1)

In Lemma 1 case B, t(h−2) xor p=t(l)=1−C, contradicting (1). Hence h=lq, C=t(l), and s=lq²−q−1. Nonnegativity of a=h−2 implies l≥1. Equation (1), using t(q−2)=p xor 1, becomes

    t(l−1) xor 1=C,      t(l+1) xor 1=C.

This is exactly the stated condition. Conversely, those same block computations verify all q+2 progression terms whenever the condition holds. ∎

The Thue–Morse prefix is t(0),...,t(4)=0,1,1,0,1. Neither l=1 nor l=2 satisfies the condition, whereas l=3 does. Proposition 2 and the inherited length theorem therefore prove

    i(q+1)=3q²−q−1.

## 4. Even-exponent minus family: the same index condition

**Proposition 3.** For even m≥2, q=2^m, all starts of length-(q+4) monochromatic progressions of difference q−1 are exactly

    s=lq²−q+1,
    l≥1,   t(l−1)=t(l+1)=1−t(l).

**Proof.** Write s=aq+b, 0≤b<q, with common letter C. At a wrap from low residue 0 to q−1, the high index is unchanged. Because m is even, these two residues have equal parity 0. Let H be this repeated high index. The two terms before the wrap, if present, have high indices H−2,H−1 and low residues 2,1. The two terms after it have high indices H+1,H+2 and low residues q−2,q−3. All four low residues have parity 1. Consequently, if both preceding and both following terms are present, then

    t(H−2)=t(H−1)=1−C,
    t(H+1)=t(H+2)=1−C.

The first equality forces H−2 odd; the second forces H+1 odd, a contradiction.

For b≥2, the first wrap occurs at progression indices k=b,b+1. Both preceding indices b−2,b−1 and following indices b+2,b+3 lie in 0,...,q+3, so the contradiction applies. For b=0, use the second wrap at k=q,q+1; again both preceding and both following terms are present. Thus b=1 is necessary.

For b=1, terms k=2,...,q+1 give a full occurrence U_m(C) at h=a+1: their high indices increase from h to h+q−1, and their low residues decrease from q−1 to 0. Reflection preserves t on these residues because m is even. Terms k=1 and k=q+2 duplicate the endpoint conditions. The two remaining exterior terms k=0 and k=q+3 require

    t(h−1)=1−C,      t(h+q)=1−C.          (2)

In Lemma 1 case B, t(h−1)=t(l) xor t(q/2−1)=t(l) xor 1=C, contradicting (2). Hence h=lq and C=t(l). Since t(q−1)=0, (2) becomes t(l−1)=t(l+1)=1−t(l), while s=(h−1)q+1=lq²−q+1. Here h=a+1≥1, so l≥1. Conversely, these conditions verify every term by the same formulas. ∎

Again the first eligible l is 3. With the inherited A(q−1)=q+4, we obtain

    i(q−1)=3q²−q+1.

## 5. Odd-exponent minus family

For odd m≥3, q=2^m, the q terms starting at q−1 have indices

    (q−1)+k(q−1)=kq+(q−1−k),       0≤k<q.

Their parities are all t(k) xor t(q−1−k)=1. For any earlier start 0≤s<q−1, the terms at progression indices k=s and k=s+1 are sq and sq+(q−1), respectively. Both lie within the first q terms, and their parities differ. Therefore q−1 is exactly the earliest start of a length-q monochromatic progression. Using A(q−1)=q gives i(q−1)=q−1.

## 6. Interpretation and prior-work limits

The proofs classify unbounded starting indices; no finite cutoff is used in exclusion. The plus and even-minus families share the same scale-free condition on l: an occurrence of aba centered at l, with a≠b. In particular their complete maximal-start sets differ by exactly 2 when m is even. This is an additional exact description, with novelty unassessed.

The proof method is elementary binary block recognition, directly related to Aedo et al.'s Lemma 20 and their block-diagonal length proofs. Our existing matching-height recurrence and average formulas are not used as hypotheses. Parshina's “arithmetic index” measures the least difference for an arithmetic word, a distinct quantity from i(d); her carry arguments and length results remain relevant prior work. This manuscript establishes no worldwide novelty claim and does not report a Lean build.
