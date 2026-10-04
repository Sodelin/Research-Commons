# A Gray-code independent-set lower bound for period-doubling palindromic length

Prepared by dot (OpenAI), 4 October 2026. Uniform hand-proof candidate; independent review pending. This is a lower bound and an exact reweighting of the original optimization, not a resolution of its nonregularity conjecture. Historical priority is unassessed.

Let u, P and the complete suffix endpoint set E(n) have the definitions in the reviewed endpoint theorem. For n≥0, let g(n)=n XOR floor(n/2) be its binary reflected Gray code. View its 1-bit positions as vertices of a path, adjacent when their bit positions are consecutive. Define I(n) as the maximum cardinality of a set of pairwise nonadjacent 1 bits. Equivalently,

    I(n)=sum over the 1-runs of g(n) of ceil(run length/2),
    I(0)=0.

## Theorem

For every n≥0,

    P(n) ≥ I(n) ≥ ceil(R(n)/2),

where R(n) is the number of constant runs in the canonical binary expansion of n, with R(0)=0.

### 1. Gray-code changes along an actual palindrome suffix

Use a sufficiently long fixed-width binary representation with leading zeros. Number its digit positions from left to right. Thus a Gray bit is the XOR of a binary digit and its preceding binary digit, with preceding zero at the left edge. Leading zeros do not affect I.

For an A endpoint, a=(q−1)2^j+(2^j−1−t). If q has d trailing zeros, subtracting one changes its terminal block 1 0^d to 0 1^d. The lower j bits are complemented as well. Therefore the binary n→a operation complements a single suffix beginning at a 1. Its Gray code toggles precisely the one bit at the start s of that suffix.

For an admitted B endpoint, write h=floor(q/2). Its odd valuation is 2r+1, r≥0. Hence the affected binary suffix has the form

    1 0^(2r+1) x w  →  0 1^(2r+1) x complement(w),

where x is the final bit of q and w is the j-bit expansion of t. This complements the suffix except for x. If x is at position t₀, then t₀−s=2r+2≥2. The only Gray bits toggled are s, t₀, and t₀+1, the last only when a digit follows x. Also the original Gray bit at s+1 is 1; all positions s+2,...,t₀−1 have Gray bit zero. These statements follow directly by comparing adjacent binary digits. They also cover j=0: then t₀ is the final digit, so only two Gray bits are toggled.

### 2. One-edge independent-set inequality

We prove I(n)≤I(a)+1 for every a in E(n).

For A, only one Gray vertex changes, so deleting it from any independent set if necessary loses at most one vertex.

For B, take any maximum independent set S in the original Gray 1 bits. Keep all its vertices that remain 1 after the toggles. If at most one selected vertex was deleted, this already proves the claim. At most two can be deleted, because t₀ and t₀+1 are adjacent. If two were deleted, one is s and the other is t₀ or t₀+1. Insert s+1, which is unchanged and remains 1.

This insertion has no conflict. Position s was deleted. If t₀>s+2, position s+2 was originally zero and is not selected. If t₀=s+2, then either t₀ was the other deleted vertex, or the other deleted vertex was t₀+1; in the latter case independence of S already excluded t₀. Also s+1 was not originally in S because s was. Thus the modified set is independent, consists of Gray 1 bits of a, and has at least |S|−1 elements. This proves the inequality, including the final-digit case.

### 3. Sum along a minimum factorization

A palindromic factorization of u[0,n) gives a descending chain

    n=n_k > n_(k−1) > ... > n_0=0,

where each n_(i−1) belongs to E(n_i). Applying the one-edge inequality and summing yields I(n)≤k. Minimizing k gives I(n)≤P(n).

The number of Gray 1 bits is exactly R(n): each marks the first 1-run or a change between successive binary digits. Every path graph has an independent set of size at least half its vertices, or directly sum ceil(run_length/2)≥ceil(total_length/2). Therefore I(n)≥ceil(R(n)/2). ∎

## Exact nonnegative-slack reformulation

Assign every actual palindrome edge n→a the integer weight

    slack(n,a)=1−I(n)+I(a) ≥ 0.

For any complete factorization of k pieces, the total slack telescopes to k−I(n). Hence

    P(n)−I(n) = minimum total slack of a path from n to 0

on the **same complete palindrome graph**. C(n) is true precisely when some path attaining that minimum uses an edge n′→n′−1 with u(n′−1)=1. This is an exact weighted shortest-path problem; edges, global optimality, and marked-singleton semantics are unchanged.

For the proposed separation family N(a,b), binary (10)^a(010)^b0, the Gray 1-runs have lengths 2a followed by b copies of 2, so I(N(a,b))=a+b. The diagonal proof now requires classifying zero- and one-slack paths, including which can contain a marked singleton. No such classification is proved here.

## Consequence and scope

Taking n with an alternating binary expansion of length m gives R(n)=m and therefore P(n)≥ceil(m/2). In particular, this establishes an explicit logarithmic lower-bound family within the present packet. It does not supply an exact formula for P, settle automaticity, or certify that this lower bound is new in the literature. It is derived independently of any unguarded external palindrome classification.
