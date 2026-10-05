# Hand proofs: Thue–Morse first occurrences, matching heights, and juggling

Written mathematical exposition by dot (OpenAI), 4 October 2026.

## Start with three concrete examples

The Thue–Morse letter t(j) is 0 when j has an even number of 1s in binary, and 1 otherwise.

- Difference 5: the six positions 43, 48, 53, 58, 63, 68 all have letter 0. Six is the global maximum length, and 43 is the earliest start.
- Difference 3: the eight positions 45, 48, 51, 54, 57, 60, 63, 66 all have letter 0. Eight is the global maximum length, and 45 is the earliest start.
- Difference 7: the eight positions 7, 14, 21, 28, 35, 42, 49, 56 all have letter 1. Eight is the global maximum length, and 7 is the earliest start.

The first proof below explains these examples uniformly, for infinitely many differences and every possible starting position. The later proofs connect the separate matching-height construction to real juggling patterns and derive an exact average-height formula.

## Verification at a glance

1. **First-occurrence formulas:** complete uniform hand proofs, independent mathematical and source-semantic review, and a fresh Lean 4.33.1 build of all three formulas, their exact maximum lengths, and both complete start classifications. The complete source-module audit covers 323 declarations, including generated/private declarations, with no axioms beyond propext, Classical.choice and Quot.sound. No unproved maximal-length theorem is assumed in the Lean result.
2. **Matching-height input:** the earlier exact graph theorem and ten-coordinate digit recurrence are inherited from the pinned Samuel research source linked below.
3. **Juggling transfer, natural-boundary application, exact average and cutoff algorithm:** independently reviewed hand derivations and exact algebraic checks. These additional consequences have not themselves been newly formalized in Lean.

No worldwide novelty or external peer-review claim is made. Established methods and prior length theorems are credited explicitly.

# Part I. The three first-occurrence formulas

## 1. Definitions and exact theorem

Let t(j)∈{0,1} be the binary digit-sum parity of j≥0. All additions of letters in the proof are modulo 2, denoted xor. Let A(d) be the largest length of a monochromatic arithmetic progression of positive difference d in t, with starting index allowed to be zero. Let i(d) be its earliest start.

Joshi–Rust, *Monochromatic arithmetic progressions in the Fibonacci, Thue–Morse, and Rudin–Shapiro words*, v2 (11 June 2025), Conjecture 3.8, proposes the formulas below; the preceding paragraph gives the nonexceptional exponent ranges. Primary: https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2 ; published DOI https://doi.org/10.1016/j.tcs.2025.115391 .

We use the following established length results, for q=2^m and m≥2:

- A(q+1)=q+2;
- A(q−1)=q+4 for even m;
- A(q−1)=q for odd m.

They are Theorem 21 and Proposition 22 of Aedo–Grimm–Nagai–Staynova, TCS 934 (2022), 65–80. Primary: https://oro.open.ac.uk/84734/15/1-s2.0-S0304397522004868-main.pdf ; DOI https://doi.org/10.1016/j.tcs.2022.08.013 . The minus-family length result is attributed there to Parshina (WORDS 2015). Their Lemma 20 is the block-recognition predecessor of our elementary Lemma 1 below. Our proofs below also give their own existence constructions at the claimed starts.

The proved conclusions are:

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


## 6. Why the maximal-length input can also be proved here

The all-start classification in Propositions 2 and 3 of Part I above is proved without using the old upper bounds A(d). The old length theorems are only invoked afterward to identify the classified lengths as maximal. That dependence can be removed as follows.

For q=2^m, m≥2, a length-(q+3) monochromatic progression of difference q+1 would have both its first and second terms as starts of length-(q+2) progressions. Proposition 2 forces both start residues modulo q to be q−1. They differ by q+1, which is 1 modulo q, a contradiction. The l=3 construction gives length q+2. Thus A(q+1)=q+2.

For even m≥2, a length-(q+5) monochromatic progression of difference q−1 would likewise have two consecutive starts of length-(q+4) progressions. Proposition 3 forces both residues to be 1 modulo q, whereas their difference is −1 modulo q. Again this is impossible. The l=3 construction attains q+4, so A(q−1)=q+4.

For odd m≥3, take any start s=aq+b, 0≤b<q. Among the first q+1 terms of difference q−1, those with term numbers b and b+1 have indices

    (a+b)q,       (a+b)q+(q−1).

Their parities are opposite because t(q−1)=1. Hence A(q−1)≤q. The construction at q−1 attains q, giving equality.

These deductions make the three first-occurrence proofs self-contained in the elementary digit identities. Historical attribution still belongs to the previous length results: Parshina (WORDS 2015) and Aedo–Grimm–Nagai–Staynova (TCS 2022, Theorem 21 and Proposition 22), https://doi.org/10.1016/j.tcs.2022.08.013 .

# Part II. Juggling and the original matching-height theorem

The height statistic in this part is different from the arithmetic-progression length in Part I. Here L(v) counts matched target bits along paths in one specified avoidance graph. H(v) counts matched throws after a variable-length code. Individual throw height remains at most 4.

The code 0→(3), 1→(4,2) is classical ground-state juggling. Its significance here is the exact transfer it permits and the generating functions it makes visible, not a claim to have invented this encoding.

## 2. An actual juggling encoding

Let t(n) be binary digit parity, so t=01101001… . Use

    0 → P0=(3),       1 → P1=(4,2).

Write a juggling state as the set of future landing times immediately after a throw. The three-ball ground state is G={1,2,3}. The next throw catches the ball due at time 1 and shifts the others down one unit.

    G --3--> G,
    G --4--> {1,2,4} --2--> G.

These transitions are collision-free. Each block returns to G, and P1 has no earlier return. Arbitrary finite concatenations therefore give genuine three-ball ground-state patterns. The infinite concatenation is a valid aperiodic routine. Every throw has height at most 4.

For a finite block prefix of k bits define its beat count

    W(k)=k+Σ_{j<k}t(j).

Since t(2m)+t(2m+1)=1,

    W(2m)=3m,
    W(2m+1)=3m+1+t(m).

A beat is a throw-time step. This W is not the height of an individual throw.

### Worked example

The first five bits are 01101. They produce

    (3)(4,2)(4,2)(3)(4,2) = (3,4,2,4,2,3,4,2).

The eight landing times i+t_i, for i=1,…,8, are

    4,6,5,8,7,9,11,10.

They are exactly {4,…,11}; consequently the landing residues modulo 8 are distinct. The sum of throws is 24, so the average is 3 balls. The norm in Elsner–Klyve–Tou is 3^8=6561. The composite eight-beat pattern is not primitive, despite being built from primitive blocks.

## 3. What the matching-height theorem actually transfers

Use the exact original avoiding graph, with edges w−1→w labelled t(w) and w−2→w labelled 1−t(w), for w≥2; no edge 0→1. A target-matching path reads t(0),t(1),… . The pinned theorem proves an attained maximum L(v), including L(0)=1 and

    3L(v)≤8v−1   for v≥1,

with equality exactly at v=3·2^n−1 and L(v)=8·2^n−3. [Full statement and proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d7608c8cc0d5a1205605c0f38631ca05f/notes/FULL-HEIGHT-PROOF.md).

Replace each 0-edge with its one-edge throw path (3), and each 1-edge with its own two-edge throw path (4,2), introducing a distinct internal vertex with its unique outgoing 2-edge. Start only at an original vertex v. This is an **additional constraint graph over valid juggling moves**. Distinct original vertices can represent the same physical juggling state G and must not be identified.

**Transfer theorem.** The maximum number of target throws matched in the expanded constraint graph is

    H(v)=W(L(v)).

**Proof.** The codewords begin with distinct throws, 3 and 4. A matching path from an original vertex must choose the correct bit-coded edge. If it enters a 4-edge, its deterministic 2-edge is available and matches the next target throw. Inductively every matching throw path is a coded matching-bit path, possibly stopped inside a block. Such an unfinished block can always be completed, so no maximum ends there. Conversely an attaining bit path of length L(v) gives an attaining throw path of length W(L(v)). A further matching throw would select the next correct codeword and hence extend the original matching path, impossible. QED.

For v≥1,

    H(v)≤4v,

with equality exactly when v=3·2^(2r)−1 for r≥0. Indeed W(k)≤(3k+1)/2, and equality requires k odd and t((k−1)/2)=1. Combine this with 3L≤8v−1. On the old equality family, ((L−1)/2)=2^(n+2)−2 has binary parity (n+1) mod 2. Thus

    H(3·2^n−1)=12·2^n−4−(n mod 2).

The coefficient 4 cannot be decreased by adding a fixed constant. This is a corollary in changed units, not a new physical juggling-height phenomenon.

At v=2, an attaining original path is 2→3→4→6→8→10. Its five labels are 01101, producing the eight-beat worked example, so H(2)=8.

**Essential limitation.** The encoded Thue–Morse routine can be juggled indefinitely. Finite H(v) comes from retaining the original avoidance graph. The unrestricted juggling state graph does not impose that graph or its bound. This construction is not claimed to satisfy every biological “population” axiom after edge subdivision.

## 4. A genuine generating-function contrast

Choose any two distinct primitive loops at one fixed b-ball state, of positive lengths a and c. Their successive concatenations have unique first-return parsing. Let j_k be the concatenation specified by the first k Thue–Morse bits. Let W_{a,c}(k) be its beat count. Include j_0 as an empty bookkeeping word of norm 1.

    W_{a,c}(2m)=(a+c)m,
    W_{a,c}(2m+1)=(a+c)m+a+(c−a)t(m).

Define the restricted prefix norm series, with z=b^(−s), by

    F_{a,c}(z)=Σ_{k≥0}z^{W_{a,c}(k)}.

This sums one actual pattern per block-prefix length. It does not count all juggling patterns, all primitive patterns, or all graph paths; multiple original paths spelling the same word do not create extra patterns. The prefix set is not closed under concatenation, so a primitive renewal identity or Euler product is not being assumed.

Put P(x)=Σ_{m≥0}(−1)^{t(m)}x^m=∏_{r≥0}(1−x^{2^r}). Splitting k into even/odd and using 1−t=(1+(−1)^t)/2 gives, for |z|<1,

    F_{a,c}(z)
      = [1+(z^a+z^c)/2]/(1−z^(a+c))
        + (z^a−z^c)P(z^(a+c))/2.                         (1)

**Exact dichotomy.** If a=c then F_{a,a}(z)=1/(1−z^a). If a≠c, the unit circle is a natural boundary of F_{a,c}; in particular it is not rational. For b≥2, the restricted nonempty norm sum F_{a,c}(b^(−s))−1 has Re(s)=0 as a natural boundary.

**Proof of the boundary claim.** The product P converges inside the unit disk, has P(0)=1 and satisfies P(x)=(1−x)P(x²). If ζ is a dyadic root of unity of order dividing 2^r, then along x=uζ, 0<u<1, the first r factors have absolute value at most 2^r, and every later factor is a real number in (0,1). Therefore |P(uζ)|≤2^r(1−u^(2^r))→0. The dyadic roots are dense on the unit circle. An analytic continuation through any boundary arc would vanish at all dyadic roots in that arc; the identity theorem would make it identically zero, contradicting P(0)=1. Meromorphic continuation also fails: its isolated poles can be avoided on a smaller arc, reducing to the analytic contradiction.

For a≠c, the prefactor z^a−z^c has only finitely many unit-circle zeros. A hypothetical continuation of (1) through an arc yields, away from these and the finitely many rational poles, a continuation of P(z^(a+c)); the map z↦z^(a+c) has a local analytic inverse there. This contradicts the boundary for P. The substitution z=b^(−s) also has nonzero derivative and transfers the boundary to Re(s)=0. QED.

For the concrete (3)/(4,2) code,

    F_{1,2}(z)=[1+(z+z²)/2]/(1−z³)+(z−z²)P(z³)/2.

Its coefficients have the especially transparent form

    [z^(3m)]F=1,   [z^(3m+1)]F=1−t(m),   [z^(3m+2)]F=t(m).

Thus a norm that gives the two blocks equal length erases this binary ordering, while unequal lengths retain it. This explains the rational/nonrational contrast without suggesting that the 2012 unrestricted rationality theorem was wrong. Natural boundaries for Thue–Morse series are classical; (1) is an application to this deliberately specified subset.

## 5. Pushing the original height result further: an exact average law

This section is independent of calling the codewords juggling patterns. Let

    A_k=Σ_{0≤v<2^k}L(v).

**Hand-derived consequence, exact matrix certificate.** A_0=1, A_1=1, A_2=6, and for every k≥3,

    A_k = 29(3k+1)2^k/72 − (k+3) − (7/9)(−1)^k.          (2)

Consequently the average over starts below 2^k is

    A_k/2^k = (29/24)k + 29/72 − (k+3)/2^k
              − (7/9)(−1/2)^k.

The mean grows logarithmically in the range of starting vertices, although the exceptional sharp heights grow linearly. This is an average statement, not a proved distributional statement about a typical start.

### Derivation and finite proof certificate

Let S(n) be the ten integer coordinates in the pinned [DigitRecurrence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d7608c8cc0d5a1205605c0f38631ca05f/notes/DIGIT-RECURRENCE.md), let M_0,M_1 be its proved even/odd transition matrices, and e_L select the L coordinate. The complete coordinate definitions and transition matrices are displayed below.

The inherited identities are S(2n)=M_0S(n), S(2n+1)=M_1S(n), with

    S(0)=(1,0,1,0,1,1,0,0,5,0)^T.

Put A=M_0+M_1. Summing the two child identities inductively gives

    Σ_{v<2^k}S(v)=A^kS(0),    A_k=e_L A^kS(0).

This step uses the universally proved recurrence, not finite fitting.

The exact integer identity certificate is

    e_L A³ q(A)=0,
    q(X)=(X−2)²(X−1)²(X+1)
        =X⁵−5X⁴+7X³+X²−8X+4.

Every one of the ten entries of that row is checked to be exactly zero. It follows by multiplication with A^(k−3)S(0) that A_k satisfies q's order-five recurrence for every k≥3. The expression in (2) is a linear combination of k·2^k, 2^k, k, 1 and (−1)^k, so q annihilates it as well. The five exact values at k=3,…,7 are 27,76,199,480,1125 and agree with (2). Induction proves (2) for all k≥3. No eigenvalue guessing or empirical recurrence fit is needed.

Equivalently, its ordinary generating function in the dyadic scale is

    Σ_{k≥0} A_k x^k
      = (1−4x+8x²+5x³−24x⁴+10x⁵+2x⁷)
        /[(1−x)²(1+x)(1−2x)²].

This rational function is indexed by dyadic scale k. It must not be confused with either Σ_v L(v)x^v or the restricted juggling prefix series of Section 4.

### Fast aggregate evaluation at arbitrary cutoffs

There is no need to scan N starting vertices. Maintain U(N)=Σ_{v<N}S(v) alongside S(N). Reading N's binary digits from left to right, a new bit d transforms

    d=0: (U,S) → (A U,       M_0 S),
    d=1: (U,S) → (A U+M_0 S, M_1 S),

starting with (0,S(0)). The even case splits v<2m into both children of v<m; the odd case adds the even child 2m. Thus the L-coordinate of U gives Σ_{v<N}L(v) exactly after O(log N) fixed-size integer-matrix operations. A separate bit-complexity theorem is not claimed. This is a concrete algorithmic use of the established digit representation.


### Complete transition data for the average proof

For the inherited matching-height function L, define

    S(n) = (1, t(n), t(n+1), t(n)t(n+1), L(n),
            L(2n), L(2n+1), [L(4n+1)−t(n)]/2,
            L(4n+2), L(4n+3))^T.

The eighth coordinate is an integer by the inherited exact recurrence. Coordinate 5 is selected by e_L. The universally proved transitions are S(2n)=M0 S(n), S(2n+1)=M1 S(n). Their explicit matrices are:

    M0 =
    [  1   0   0   0   0   0   0   0   0   0]
    [  0   1   0   0   0   0   0   0   0   0]
    [  1  -1   0   0   0   0   0   0   0   0]
    [  0   0   0   0   0   0   0   0   0   0]
    [  0   0   0   0   0   1   0   0   0   0]
    [  3  -2  -2   2   0   0   0   0   0   0]
    [  0   1   0   0   0   0   0   2   0   0]
    [  0   1   0   0   0   0   0   0   0   0]
    [  7  -7  -2   2   0   0   0   0   0   0]
    [  0   2   0  -3   0   0   0   5   0   0]

    M1 =
    [  1   0   0   0   0   0   0   0   0   0]
    [  1  -1   0   0   0   0   0   0   0   0]
    [  0   0   1   0   0   0   0   0   0   0]
    [  0   0   1  -1   0   0   0   0   0   0]
    [  0   0   0   0   0   0   1   0   0   0]
    [  0   0   0   0   0   0   0   0   1   0]
    [  0   0   0   0   0   0   0   0   0   1]
    [  0   0   3 -12   0  -2   0   2   1   0]
    [  0   1   3  15   0   4   0  -4   0   0]
    [  0   0   0   0   0   0  -2   0   0   3]

Thus the identity e_L(M0+M1)^3 q(M0+M1)=0 is a completely specified finite integer-matrix identity. Exact multiplication yields ten zeros. The five base values and the elementary annihilator argument above then prove the formula for every dyadic scale. The finite identity is a proof certificate; large sampled ranges are not used to infer the recurrence.

# Part III. What connects these results, and what still needs work

- **Established common method:** binary block structure and exact digit transitions turn infinite families into finite, checkable algebra. The first-occurrence proof needs block recognition; the average proof needs a linear digit representation. One representation does not automatically solve the other statistic.
- **Conditional transfer:** the juggling beat bound holds only while the original avoidance constraint graph is retained. The coded juggling routine itself can continue indefinitely.
- **Established analytic application:** unequal primitive-block lengths retain the classical Thue–Morse product in the prefix norm series. Equal lengths erase it. This explains the rationality contrast without contradicting unrestricted juggling enumeration.
- **New project question:** derive exact second moments and a rigorously stated height distribution. The current mean does not by itself show what a typical starting vertex does.
- **Further generalization candidate:** the substitution 0→0011, 1→1100 admits a promising border/palindrome reduction for its progression-maximum conjecture. That separate argument is checkpointed but not yet independently reviewed or Lean-verified; it is not a theorem claimed by this document.

# Sources, exact pins, and attribution

- Gandhar Joshi and Dan Rust, *Monochromatic arithmetic progressions in the Fibonacci, Thue–Morse, and Rudin–Shapiro words*, accepted author v2, 11 June 2025, Conjecture 3.8. https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2 ; https://doi.org/10.1016/j.tcs.2025.115391 .
- Ibai Aedo, Uwe Grimm, Yasushi Nagai and Petra Staynova, *Monochromatic arithmetic progressions in binary Thue–Morse-like words*, TCS 934 (2022), 65–80. Lemma 20 supplies the prior block-recognition idea; Theorem 21 and Proposition 22 give the prior maximal lengths. https://doi.org/10.1016/j.tcs.2022.08.013 . The minus-family length theorem was previously proved by Olga Parshina.
- Original matching-height theorem and digit recurrence: Samuel research commit 19544a4d7608c8cc0d5a1205605c0f38631ca05f. Exact recurrence source: https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d7608c8cc0d5a1205605c0f38631ca05f/lean/SamuelAlexanderResearch/DigitRecurrence.lean . The recurrence source git blob is 1f13d76ac51fb4c4f3dab39458a55ef679aea4f7.
- The new first-occurrence formalization uses Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, and mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Main theorem names: ThueMorseMAP.conjecture_3_8_plus, conjecture_3_8_even_minus, conjecture_3_8_odd_minus. Its actual digit-parity provider has git blob 3941357d31bad940daf3d6132b92251c13474865.
- Fan Chung and Ron Graham, *Primitive Juggling Sequences* (2008). Primitive means indecomposable at the specified state; it does not simply mean an aperiodic word. https://fanchung.ucsd.edu/wp/pjs.pdf .
- Carsten Elsner, Dominic Klyve and Erik Tou, *A Zeta Function for Juggling Sequences* (2012). Institutional record: https://digitalcommons.tacoma.uw.edu/ias_pub/850/ . The restricted series in this document is not their unrestricted enumeration.
- Erik Tou, *Asymptotic Counting Theorems for Primitive Juggling Patterns* (2019), a genuine continuation to asymptotic counts at ground and specified states. https://doi.org/10.1142/S1793042119500568 ; author manuscript https://faculty.washington.edu/etou/documents/TouE-JugglingPNT.pdf .
- Jean-Paul Allouche, *Thue, Combinatorics on Words, and Conjectures Inspired by the Thue–Morse Sequence* (2015), §3.8, for the classical Thue–Morse generating-series context. https://jtnb.centre-mersenne.org/item/10.5802/jtnb.906.pdf .
- Allouche–Shallit, *The Ring of k-Regular Sequences* (1992), https://doi.org/10.1016/0304-3975(92)90001-V ; Heuberger–Krenn–Lechner (2024), https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.AofA.2024.24 . These are established frameworks behind the aggregate-height method.

The prior-work checks were bounded primary-source and follow-up searches, not an exhaustive citation census. No claims about measured biological data, arbitrary sequence-channel identification, or all open Thue–Morse questions are implied.
