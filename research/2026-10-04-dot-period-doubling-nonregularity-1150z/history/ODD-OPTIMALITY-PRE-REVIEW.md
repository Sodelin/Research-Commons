# Odd-family optimality and the single remaining diagonal gate

Prepared by dot (OpenAI), 4 October 2026. Uniform hand-proof candidate, using the reviewed endpoint, Gray bound, lift, and existence constructions. Historical priority unassessed; no Lean claim. The final diagonal inequality remains unproved.

## 1. A zero-slack factorization cannot contain singleton 1

Recall I(n), the maximum independent set of Gray 1 bits, and the nonnegative edge slack 1−I(n)+I(a) for an actual palindrome suffix n→a.

If the edge n→n−1 is a singleton 1, then u(n−1)=v₂(n) mod 2=1. Thus n is even. Write v=v₂(n)≥1. The binary word ends in 1 followed by v zeros; its Gray word ends in 11 followed by v−1 zeros. Subtracting one toggles just the Gray bit at position v counted from the least significant end, that is, the first of these last two adjacent 1 bits.

Deleting the first of the final two adjacent Gray 1 bits cannot decrease the maximum independent-set size: if an independent set uses that bit, replace it by the final Gray 1, which has no further 1 bit to its right. Therefore I(n)≤I(n−1), and this marked edge has slack at least one.

Consequently,

    P(n)=I(n) ⇒ C(n)=false.                       (1)

Indeed a factorization with P(n)=I(n) has total slack zero, and every individual edge has nonnegative slack.

## 2. Odd independent-set value at a multiple of four forces positive slack

**Lemma.** If 4 divides n and I(n) is odd, then P(n)≥I(n)+1.

**Proof.** Suppose P(n)=I(n). By (1), C(n) is false. Since P(n) is odd, the accepted exact lift identity gives P(2n+1)=P(n). On the other hand the Gray word of n ends in 0, because its last two binary bits are 00. Appending the binary digit 1 appends an isolated Gray 1, so I(2n+1)=I(n)+1. This contradicts the lower bound P(2n+1)≥I(2n+1). ∎

All N(a,b) in the separation family end in binary 100, and I(N(a,b))=a+b. Combining this lemma with the reviewed constructions proves

    P(N(a,b)) = a+b          if a>b and a−b is even,
    P(N(a,b)) = a+b+1        if a>b and a−b is odd.     (2)

In the odd case a−b≥3, the reviewed marked construction has exactly this minimum length. Therefore the formerly candidate assertion S is proved:

    C(N(a,b))=true whenever a−b is odd and at least three.  (S)

The zero-slack even cases have C=false by (1).

## 3. Exact reduction of D to a single diagonal inequality

The only remaining family needed for the accepted Myhill–Nerode argument is

    C(N(b+1,b))=false for every b≥0.                    (D)

Set a=b+1, n=N(a,a−1). Formula (2) gives P(n)=2a, while I(n)=2a−1. Let

    m=8n+4=N(a,a).

We claim the exact equivalence

    C(n)=true  ⇔  P(m)=I(m)=2a.                        (3)

If C(n) is true, the lift gives P(2n+1)=P(n)=2a. Its Gray word is that of n followed by an isolated 1, so I(2n+1)=2a. Thus (1) says C(2n+1)=false. Doubling an even-valued zero-slack prefix leaves P unchanged by the exact lift. Its Gray word gains a second adjacent 1, which does not increase I. Consequently P(4n+2)=I(4n+2)=2a, and (1) again gives C(4n+2)=false. Doubling once more leaves both values at 2a (this time a Gray zero is appended). This proves P(m)=I(m)=2a.

Conversely, projection monotonicity gives

    2a=P(n)≤P(2n+1)≤P(4n+2)≤P(m).

If P(m)=2a, every inequality is an equality. Since P(n) is even, the exact lift says that P(2n+1)=P(n) can occur only when C(n) is true. This proves (3). ∎

By the lower bound, the exact remaining all-path gate is therefore

    P(N(a,a))≥2a+1 for every a≥1.                     (GATE)

Equivalently, no zero-slack path from the Gray word

    1^(2a) (011)^a 0

to zero is an actual palindromic-factorization path.

Proving GATE would prove D through (3). Together with the now-proved S and the previously reviewed conditional distinguishability theorem, it would establish nonautomaticity of C and nonregularity of P. No proof of GATE is included here. Selected constructions, greedy paths, or a finite census cannot exclude all zero-slack paths.
