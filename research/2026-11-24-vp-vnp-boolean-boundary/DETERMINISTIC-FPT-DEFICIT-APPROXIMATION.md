# A deterministic fixed-parameter relative approximation for clause-subset cut rank

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and exact finite replay. No new Lean verification, exact FPT algorithm, or P versus NP separation.

For a labeled CNF F, let R(F) be its number of satisfiable clause subsets (the [mixed-gate cut rank](MIXED-GATE-CUT-RANK.md)). Let d=|F| minus the maximum clause-variable incidence matching size. For any rational 0<eps<1 there is a deterministic algorithm producing integer L<=R(F)<=U with U-L<=eps R(F), in time 2^O(d) poly(input,1/eps). This improves the earlier deterministic truncation to single-exponential dependence at constant precision. It is polynomial for d=O(log n) at inverse-polynomial precision, where n is the input size. The result uses the [previous deficit-decreasing branching rule](DETERMINISTIC-DEFICIT-RANK-APPROXIMATION.md); the new step is to cap the total number of revealed clause-inclusion bits along a path, not the number of branches per level.

## Counting rule

Use the previous nodes (G,A), where clauses outside G are excluded, those in A are included, and the other bits are free. A satisfiable G contributes every assignment to its free bits; an unsatisfiable A contributes none. Otherwise choose any deterministically ordered list of unforced clauses in an unsatisfiable canonical block of G. A good subset must omit at least one member of this list, and deleting that first omitted clause reduces matching deficit by one. Each candidate child j forces the first j-1 bits to one, forces bit j to zero, and consumes j units of a common path budget. Keep the corresponding old updates of G and A. If only b units remain, explore at most the first b omissions. If the list is longer than b, charge the entire all-present prefix of length b as unknown. This includes the b=0 case. If the whole list fits and is present, the region is known bad, not unknown. Use branch budget

    B = 6d + 2 ceil(log2(1/eps)).

No floating logarithm is needed: for rational eps, compute the smallest integer k with 2^k eps>=1. For d=0 return the exact maximum 2^|F| immediately.

## Why the relative error is small

Choose an original subset uniformly at random for the analysis only. The observed inclusion bits are independent fair bits, even in the adaptive order: every query chooses an as-yet-unforced clause based solely on already observed bits and the formula. No clause is queried twice on a path. An unknown branch is reached after B observations with at most d completed omissions, because every completed omission reduces the deficit and a node at deficit zero is never ambiguous. Extend the revelation sequence by independent dummy bits whenever it stops before length B. Thus the proportion unknown is bounded by P(Binomial(B,1/2)<=d). The rank is at least 2^(|F|-d), since all subsets of the matched clauses are jointly satisfiable. For Z the number of omissions among B independent bits, apply Markov's inequality to 2^(-2Z). Then

    P(Z<=d) <= 4^d (5/8)^B,
    unknown/R <= 8^d (5/8)^B <= eps,

since 8(5/8)^6<1 and (5/8)^2<1/2. The estimate is deterministic: sum exact cardinalities of known-good regions for L, then add exact cardinalities of the disjoint unknown regions for U.

## Runtime and verification

Each partial branch history can be encoded by its revealed bit string (a concatenation of strings 1^(j-1)0), because the next clause list is determined by the earlier answers. Its length is at most B, so the number of visited nodes is at most 2^(B+1). Each node uses the same matching and bounded-deficiency SAT operations as in the earlier proof, costing 2^O(d) times a polynomial in input size; all arithmetic on subset counts uses O(|F|) bits. Depth-first recursion requires only polynomial space. One may still apply the [canonical block factorization](CANONICAL-MATCHING-DEFICIT-BLOCKS.md) first and divide precision across blocks, obtaining dependence on the maximum block deficit in the exponential factor.

Exact replay: in the previous note's standalone JS checker, replace the definition of L by `6*d+4` (eps=1/4), make the callback on `Ls.slice(0,l)` take `(i,j)`, and pass `l-j-1` to the recursive call instead of `l`. Keep the forced-bit updates and cardinality charge unchanged. The replay compared the enclosures against exhaustive exact ranks on all 564 prior fixtures and exercised 490 truncations and 13,137 children across its normal and stress budgets. It is an audit of the counting rules, not a complexity lower bound or a Lean certificate. Exact counting in polynomial time for arbitrary d or in FPT time with parameter d is not established.
