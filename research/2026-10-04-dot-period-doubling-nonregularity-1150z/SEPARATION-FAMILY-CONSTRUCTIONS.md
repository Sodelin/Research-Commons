# Uniform constructions in the proposed separation family

Prepared by dot (OpenAI), 4 October 2026. Hand-proof candidate. This proves the even-difference subfamily and a marked upper bound in the odd-difference subfamily. It does **not** prove D or S or settle nonautomaticity.

Use the accepted Gray potential I and endpoint theorem. For a≥1,b≥0, let N(a,b) have binary expansion (10)^a(010)^b0. Its Gray word is

    G(a,b)=1^(2a) (011)^b 0,

so I(N(a,b))=a+b.

## Theorem

1. If a>b and a−b is even, then P(N(a,b))=a+b.
2. If a>b and a−b is odd, then P(N(a,b))≤a+b+1.
3. If a−b is odd and at least three, there is a factorization into a+b+1 palindromes containing a singleton 1.

Part 3 is a marked upper bound. It does not yet imply C(N(a,b)), because a shorter factorization of a+b pieces has not been uniformly excluded in the odd-difference case.

## 1. Two exact binary operations in Gray coordinates

Number digits from left to right starting at zero in a fixed-width word, with leading zeros allowed. The underlying binary digit at a position is the parity of the number of Gray 1 bits up to and including that position.

- A may toggle a Gray bit at position s when the underlying binary digit there is 1. Equivalently, if that Gray bit is 1, its rank among Gray 1 bits is odd. This is precisely an A suffix-complement edge of the complete endpoint theorem.
- B may toggle Gray positions s,t,t+1 when the underlying binary digit at s is 1, t−s is positive and even, g(s+1)=1, and g(s+2),...,g(t−1)=0. (The last toggle is omitted if t is the final digit.) The binary digits between s and t are then 1 followed by an odd number of zeros, so the guarded B endpoint theorem applies.

All operations below use t+1 inside the word. Consequently any unchanged trailing zeros can be retained. Each operation is an actual descending palindrome edge, not an abstract relaxation.

Call a pair of consecutive Gray 1 bits a domino. In a configuration whose 1-runs all have even length, tile each run into consecutive dominoes from left to right. A prefix before a domino contains an even number of Gray 1 bits, so its first bit has odd rank and is an admissible A/B start.

### Move D: delete two neighboring dominoes separated by an even zero gap

On 11 0^(2r) 11, apply B at the first bit of the first domino, with the exception at the first bit of the second domino. The pattern becomes 01 0^(2r) 00. Apply A to the remaining single 1, which has odd rank. Thus both dominoes disappear in two palindrome edges. All other digits stay unchanged.

### Move R: replace three contiguous dominoes by one shifted domino

On 111111, first apply B to the last four bits:

    111111 → 110100.

Then apply B to the first four bits:

    110100 → 011000.

Both starts have odd Gray rank, and both exception distances are two. The output domino is shifted one position and therefore has the opposite position parity. This uses two palindrome edges and removes two units of I.

### Move E: consume two prefix dominoes and two tail dominoes across an even gap

Suppose the last two dominoes of a contiguous prefix are followed by an even gap of L zeros, then two tail dominoes separated by one zero. On

    1111 0^L 11 0 11,

first apply B to the last prefix domino and first tail domino. This leaves the first prefix domino followed by 01, and deletes the first tail domino. Apply B to the resulting initial 1101, producing 0110. The remaining shifted domino and the second tail domino have an even zero gap: their starts differ by L+6. Move D deletes them.

Four palindrome edges remove the last two prefix and first two tail dominoes. If more prefix/tail dominoes remain, the gap between them is L+10, still even. Both intermediate B starts have odd rank; the one in the initial 1101 has a prefix consisting of whole dominoes. This proves the operation including all boundary cases.

## 2. Exact even-difference family

First suppose b=0 and a is even. Repeated Move D on pairs of contiguous dominoes deletes the a dominoes in a palindrome edges.

Now b≥1. The initial gap between the contiguous a-domino prefix and the first tail domino is one, hence odd. Since a−b is positive even, a≥3. Apply Move R to the last three prefix dominoes. The shifted domino and first tail domino now have an even gap of four. Delete them by Move D.

This uses four edges. The remaining configuration consists of A=a−3 contiguous prefix dominoes and B=b−1 tail dominoes, with one zero between successive tail dominoes and an even gap L=10 between prefix and tail when both remain. More generally only its evenness matters. We have A−B=a−b−2≥0 and even.

While B≥2, apply Move E, reducing both A and B by two. Its prerequisites hold because A≥B. If B=1 remains, then A is odd and at least one; apply Move D to the last prefix domino and the final tail domino across their even gap. If B=0, nothing is needed at this stage. In either case an even number of contiguous prefix dominoes remains. Delete them in pairs by Move D.

Every edge used costs one and the total number of edges is a+b: each complete move removes as many units of I as its cost. Thus P(N(a,b))≤a+b. The accepted lower bound P≥I=a+b gives equality.

The same construction works with any number of trailing Gray zeros: it never uses the final-digit version of B.

## 3. An upper bound for odd difference

Suppose a>b and a−b is odd. Remove the binary singleton at the final position, using N→N−1. Since N ends in binary 100, this toggles the next-to-last 1 of the final Gray domino. Its independent-set value stays unchanged, so this is a one-slack edge. The remaining last Gray 1 is isolated and has odd rank. Delete it with A; this is a zero-slack edge.

If b≥1, the remaining Gray word has a prefix of 2a ones and b−1 tail dominoes separated by single zeros, with extra trailing zeros. Its domino difference a−(b−1) is positive even. Section 2 deletes it in a+b−1 edges. If b=0, a−1 is even and the remaining contiguous a−1 dominoes are deleted in pairs.

The total is 1+1+(a+b−1)=a+b+1, proving part 2. This displayed construction need not contain a singleton 1; the initial singleton has value 0.

## 4. A marked construction when the odd difference is at least three

If b=0, a is odd and at least three. Delete a−3 dominoes in contiguous pairs, retaining three contiguous dominoes. Apply Move R, leaving one domino shifted one position from the original domino parity. This remaining Gray word is a pair of 1 bits followed by zeros and hence its binary integer is 2^e. The original total width 2a+1 is odd; the shifted pair starts in an odd left-to-right position, so e is odd. The prefix u[0,2^e−1) is a palindrome (repeated odd projection), and u(2^e−1)=1. These two factors finish the path and include the singleton 1. The total number of pieces is (a−3)+2+2=a+1.

For b≥1, begin with Move R and Move D exactly as in Section 2. This leaves A=a−3 prefix and B=b−1 tail dominoes across an even gap, with A−B=a−b−2 positive odd. Apply Move E until B is zero or one.

If B=0, then the original b was odd and the remaining A is odd and at least one. The remaining Gray word consists of 2A contiguous ones at the original left edge, followed by zeros. Its corresponding binary number has an odd number of trailing zeros: its valuation parity is that of the original b, since the original width is 2a+3b+1 and removing an even number 2A of Gray positions does not change this parity. Therefore the singleton edge n′→n′−1 has letter u(n′−1)=1. Perform it, delete the resulting isolated last Gray 1 with A, and remove the remaining even number A−1 of dominoes in pairs. This uses A+1 edges and supplies the required marker.

If B=1, then the original b was even and A is even and at least two. Delete A−2 contiguous prefix dominoes in pairs, retaining the last two. Perform the first two edges of Move E with the single tail domino: B deletes that tail domino and leaves a prefix monomer; the next B changes 1101 to 0110. Only one shifted domino remains. It starts at an odd position relative to the original left edge (deleting complete pairs of dominoes changes that position by a multiple of four). The original width is odd because b was even. Thus the remaining integer is again 2^e for odd e. Finish with its length-(2^e−1) palindrome and singleton 1.

All preliminary edges are zero-slack; the final marked segment costs exactly one more than its remaining independent-set value. The total is therefore a+b+1, proving part 3. ∎

## Remaining all-path obligation

To infer S, one must still exclude an a+b-piece factorization when a−b is odd. To infer D, one must also exclude every marked a+b+1-piece factorization when a=b+1. The constructions provide the required existence side, including exact marked witnesses, but do not establish these exclusions. No finite diagnostic or chosen reduction path rules out other paths.
