# When remainder counts cannot see a Goldbach pair

**Status:** Hand-proved finite obstruction for a specified observation model, with exact executable checks. Not a proof or disproof of binary Goldbach, not Lean-verified, and not a priority claim.

## Statement

Let (W>2) be even and let (d ≥ 2) and (B ≥ 1) be integers. Put (N=WdB), and let (U) consist of the integers (1 ≤ x<N) coprime to (W). There are two subsets (A_+,A_-) of (U), each with density exactly (1/d) **within** (U), with these properties:

1. For every divisor (q) of (W), their whole-interval residue counts agree exactly in every class modulo (q).
2. For each prefix ([1,t]) of that interval and each class (a mod q), put (h(q,a)=|{r mod W : gcd(r,W)=1, r ≡ a mod q}|). The count in either set differs from (1/d) times the count in (U) by strictly less than (h(q,a)) if (h(q,a)>0), and is zero if (h(q,a)=0). In particular, the discrepancy is less than one in each allowed class modulo (W).
3. Every element of (A_+) has its (N)-complement in (A_+); no element of (A_-) has its (N)-complement in (A_-). Thus their ordered representation counts are exactly (|U|/d) and zero. Neither set contains (N/2): the midpoint is a multiple of (W/2>1).

## Construction and proof

The reduced residue classes come in distinct pairs ({r,-r} mod W). They are distinct because (2r ≡ 0 mod W) and (gcd(r,W)=1) would imply (W divides 2). Take the representative (1 ≤ r<W/2). Every element in the two classes has exactly one of the forms (a_j=r+jW), (b_j=N-a_j), for (0 ≤ j<dB). The partner map interchanges (a_j,b_j) without changing (j).

For (j=0,d,2d,…,(B-1)d), put (a_j,b_j) into (A_+), and (a_j,b_{j+1}) into (A_-). All indices exist since (d ≥ 2). Within an orbit the two residue classes each contain exactly (B) selected elements, so counts match for (q=W) and on summing for any (q divides W). The selected indices in each class occupy one complete congruence class modulo (d). Intersecting with a value prefix selects an initial segment of the indices for (a_j), or a terminal segment for (b_j). In either case the discrepancy from the segment length divided by (d) is strictly less than one. Adding that bound over compatible reduced classes gives item 2.

Complementation does not mix different residue pairs. Inside a pair the selected indices are equal on both sides for (A_+), but occupy distinct classes modulo (d) for (A_-). This proves item 3.

## What this excludes, and what it does not

Take (W=lcm(1,…,Q)) for any fixed (Q ≥ 3). The test then covers all the moduli through (Q) at once; at modulus (W) it even has a prefix discrepancy of less than one per admissible class. You can make the sets sparse by increasing (d). These are artificial integers that pass **only the specified marginal tests**; they are not claimed to satisfy RH/GRH, the prime number theorem, Chen's sieve hypotheses or uniform simultaneous estimates over growing moduli. No barrier for all sieve methods or all uses of GRH follows. We have not established novelty beyond this explicit construction.

A useful screening question for a proposed proof: which exact hypothesis fails for (A_-)? If the argument uses only the marginal properties above, it cannot establish positivity for the chosen sum. For an actual prime sequence, a separate signed estimate on Chen's cohort could in principle distinguish prime partners from products of two primes; the construction supplies no such estimate. An exact reformulation is (2P=C-L), where (C) counts Chen candidates, (L) sums their partner Liouville signs, and (P) counts candidates with a prime partner. One needs (L<C), not necessarily cancellation around zero. That identity identifies the missing information, not a way to bound it.

## Prior work and reproduction

- [Tao, parity obstruction for binary Goldbach with bounded error](https://terrytao.wordpress.com/2014/07/09/the-parity-problem-obstruction-for-the-binary-goldbach-problem-with-bounded-error/): a substantially broader sieve obstruction. This note is a small direct test for residue and prefix observations, not a replacement for it.
- [Chen theorem blueprint](https://subfish-zhou.github.io/goldbach-lean/blueprint/chap-chen.html): the prime-plus-at-most-two-factors candidate set and signed sieve.
- [Lichtman, Goldbach beyond the square-root barrier](https://arxiv.org/abs/2309.08522): larger weighted moduli and stronger **upper** bounds; not positive lower bounds.
- [Li and Liu, fourth moments and exceptional sets](https://arxiv.org/abs/2610.26756): their October 2026 preprint's zero-location hypothesis is met by [the checked Dirichlet GRH statement](https://math.mit.edu/~drew/grh/#what-was-verified). Its claimed square-root-scale exceptional-set bound, up to logs, still allows individual failures. This note does not independently verify that preprint.

Run `python3 -B replay.py | diff -u REPLAY.txt -` in this directory. The finite replay checks support, exact class counts, prefix bounds, and the two complementary-pair outcomes. The general guarantee is the hand proof above, not the computation. [VibeMath draft](VIBEMATH.md) is an exposition draft, not a submission.
