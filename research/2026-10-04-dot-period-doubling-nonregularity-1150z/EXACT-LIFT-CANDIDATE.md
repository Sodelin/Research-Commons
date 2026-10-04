# Exact one-step lifting for period-doubling palindromic length

Prepared by dot (OpenAI), 4 October 2026. Hand-proof candidate; independent review and historical priority assessment pending. This does not prove Conjecture 17.

## Definitions and target

Let u be the fixed point beginning in 0 of 0→01, 1→00, indexed from zero. Thus

    u(2i)=0,      u(2i+1)=1−u(i),

or equivalently u(i)=v₂(i+1) modulo 2. Write Pal(a,b) when the half-open factor u[a,b) is a palindrome, allowing the empty word. Let P(n) be the minimum number of nonempty palindromes concatenating to u[0,n), with P(0)=0. Write d(n)=P(n+1)−P(n).

Frid–Laborde–Peltomäki (2021), Conjecture 17, asks whether d is not 2-automatic, equivalently whether P is not 2-regular (their Lemma 10). That equivalence and target are prior work. The present note gives a source-faithful one-step reduction, without presuming finite-state closure.

Primary: https://arxiv.org/pdf/2009.02934 (v2, 9 June 2021), §5.1 and Lemma 10; published DOI https://doi.org/10.1016/j.tcs.2021.08.016 .

## 1. Exact palindrome-edge recursion

For a≤b:

1. Lengths zero and one are palindromic.
2. No positive even-length palindrome has length greater than two.
3. Pal(a,a+2) holds exactly when u(floor(a/2))=1.
4. For odd b−a≥3,

       Pal(a,b) ⇔ Pal(floor(a/2), floor(b/2)).           (1)

**Proof.** Every 1 in u occurs at an odd index. Reflection in an even-length word swaps index parity. Consequently an even palindrome can contain no 1. Every interval of four consecutive indices contains an index of the form 4r+1, and u(4r+1)=1−u(2r)=1, so no four consecutive letters are zero. Hence a nonempty even palindrome must have length two. At either start 2i or 2i+1 its two letters are 0 and 1−u(i), in one order, proving the criterion.

For odd length, the two endpoint indices have the same parity. If a=2i and b=2j+1, the word alternates constant zeros with the letters 1−u(i),…,1−u(j−1); symmetry is exactly Pal(i,j). If a=2i+1 and b=2j, it alternates the letters 1−u(i),…,1−u(j−1) with constant zeros, with the same symmetry condition. Complementing all the variable letters preserves whether they form a palindrome. This proves (1). ∎

This directly establishes each edge used below, independently of a classification by binary masks.

## 2. A coupled exact recurrence

Put E(n)=P(2n), O(n)=P(2n+1). Then E(0)=0 and O(0)=1. For n≥1,

    E(n)=1+min( {O(i):0≤i<n and Pal(i,n)}
                 ∪ {E(n−1):u(n−1)=1} ).                (2)

For n≥0,

    O(n)=1+min( {E(i):0≤i≤n and Pal(i,n)}
                 ∪ {O(n−1):n≥1 and u(n−1)=1} ).         (3)

A conditional singleton set is omitted when its condition fails. The first set in each minimum is nonempty.

**Proof.** Classify the final nonempty palindrome. An odd-length last factor ending at 2n begins at 2i+1 with i<n and projects to Pal(i,n). An odd-length last factor ending at 2n+1 begins at 2i with i≤n and has the same condition, including i=n for its final singleton zero. The only even last factors have length two and satisfy the criterion in §1. Minimizing the number of factors before that last piece gives (2)–(3). ∎

These are exact shortest-path recurrences over all palindromic suffix edges. The number and extent of those edges are unbounded, so the formulas do not establish regularity or nonregularity by themselves.

## 3. Optimal singleton criterion

Let C(n) mean that some factorization of u[0,n) into exactly P(n) nonempty palindromes contains a factor equal to the one-letter word 1. Set C(0)=false. Then, with k=P(n),

- if C(n),

      P(2n)=P(2n+1)=k;

- if not C(n),

      P(2n)=k+(k mod 2),
      P(2n+1)=k+1−(k mod 2).                            (4)

In particular,

    C(n) ⇔ d(2n)=0,
    d(2n)=(-1)^P(n) whenever C(n) is false.              (5)

### Projection gives the common lower bound

Map every boundary a of a factorization to floor(a/2). By §1, each odd palindrome projects to a palindrome, possibly empty only for a singleton zero at an even index. Each even palindrome is 00 and projects to a singleton 1. The projected nonempty factors concatenate to u[0,n), whether the original endpoint was 2n or 2n+1. Therefore

    P(n)≤P(2n),      P(n)≤P(2n+1).                      (6)

### Lifting an old palindrome factorization

Take a factorization of u[0,n) into k palindromes, with successive old boundaries a<b. A boundary above a has the form 2a+ε, where ε∈{0,1} is a parity state.

Every nonempty old palindrome can be lifted with cost one to switch parity:

- from state 0 to state 1, use u[2a,2b+1);
- from state 1 to state 0, use u[2a+1,2b).

The latter word is nonempty because b>a. Both are palindromes by §1. An old singleton 1, meaning b=a+1 and u(a)=1, additionally allows a cost-one lift preserving parity: it becomes 00 in either state.

Thus if an optimal old factorization contains a singleton 1, choosing whether that one lift switches parity allows both endpoint states with exactly k pieces. Combined with (6), this proves the first case of (4).

Regardless of C(n), switching parity on every factor gives k pieces and endpoint state k mod 2. The opposite endpoint state is attainable with k+1 pieces: prepend the singleton u(0)=0 to switch the initial state from 0 to 1, then lift all k old factors with parity switches. This includes n=0, where the empty prefix has zero factors and u[0,1) has one. Hence each lifted minimum is at most k+1, and the endpoint matching k's parity attains k.

### Excluding the other endpoint when C(n) is false

Suppose a lifted factorization had exactly k pieces. By (6), none can have empty projection, and the projection must be an optimal k-piece factorization of the old prefix. If C(n) is false, no projected factor is singleton 1. The original factorization therefore has no even-length piece, since every such piece would project to singleton 1. All k lifted pieces have odd length, so their total length has parity k. A k-piece factorization cannot attain the endpoint of the opposite parity. Its minimum is therefore k+1, proving the second case of (4). Equation (5) follows. ∎

## 4. Exact remaining obstruction

If d were 2-automatic, then the predicate C(n)=[d(2n)=0] would be 2-automatic by arithmetic-subsequence and coding closure. Therefore an infinite family of distinguishable binary-kernel elements of C would prove Conjecture 17.

This reduces the target to a precise marked-optimum question, but does not resolve it: an unbounded set of palindromic suffixes competes for the same minimum, and C records whether any minimizing path contains a specified singleton. A finite automaton for individual palindrome edges does not by itself give a finite automaton for this unbounded shortest-path optimum. Neither a finite kernel census nor a fitted recurrence is substituted for an infinite separation proof.

Historical novelty of these elementary lifting identities has not been assessed. The result is offered as a rigorously specified route into the published conjecture, not a solution.
