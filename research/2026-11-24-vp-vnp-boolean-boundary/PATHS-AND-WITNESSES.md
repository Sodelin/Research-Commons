# Which Boolean-to-arithmetic bridges survive?

24 November 2026 · Dot and internal proof review · Scoped hand deductions and finite checks. Not Lean-verified and not a P vs. NP result. The distinct-path refinement was found on the independent bridge pass; the witness argument is a standard transcript indistinguishability argument in this explicitly defined oracle model. No priority claim.

## Do not merge paths that request different variables

Keep the syntactic supports V(g), multiplication overlaps O(g), and circuit conventions from [LOCAL-WIDTH](LOCAL-WIDTH.md). Define a family of masks M at each reachable gate. Start with M(output)={∅}. Along a parent g to child h, propagate each mask R in M(g) to (R ∪ O(g))∩V(h). Merge equal masks but not different masks. A mask denotes the variables fixed in that call, not their values.

The [local-width compiler](LOCAL-WIDTH.md) needs only states (g,R,a) with R in M(g) and a∈{0,1}^R. Indeed both children of a product fix O(g) in addition to the previous assignments, restriction to either child commutes with mask propagation, and addition introduces no variables to fix. Along a path, branching allows each Boolean assignment to every new overlap; restriction deletes bits but does not impose a relation on those remaining. Induction therefore gives exactly the full cube of assignments for each reachable mask (no constant-based pruning is needed). This is an accounting change; the multilinearity, Boolean agreement and uniqueness proof are unchanged.

There are 2^|R| values to cache for each (g,R), at most 2^|O(g)\R| branches each, and O(1+|O(g)\R|) arithmetic gates for a branch, including its selector. Thus the output circuit can be built with size
```
O( sum_g  sum_{R in M(g)} (1 + |O(g) \ R|) 2^|R ∪ O(g)| ).
```
Writing w for the largest |R∪O(g)| and K for the largest number of distinct masks at a gate gives O(s K (1+w) 2^w). This is an arithmetic gate bound, not a bit-complexity claim over arbitrary fields. Masks themselves can be propagated and deduplicated in topological order with polynomial overhead per propagated mask in a finite support encoding.

Strict improvement: for g=Σ_j x_j used by all branches of Σ_i (1+x_i)g, the merged mask at g in the old bound contains all n variables. The reachable masks at g are the n singletons. The maximum path width is one throughout the circuit. An exact n=12 replay gave 12 masks at g, old width 12, and path width 1; this also follows directly from the definitions.

**Limit.** Width alone does not make the memo-table construction efficient. Take k disjoint groups X_j each of size b, put H₀=Σ_i x_i, and set H_j=Σ_{x∈X_j} (1+x)H_{j−1}, sharing the single H_{j−1} gate. The circuit has O(kb) gates, each multiplication has a singleton overlap, path width k, and there are exactly b^k masks at H₀, one variable from each group. Taking b=2^k makes path width logarithmic in circuit size but gives superpolynomially many masks. This is not a lower bound on the best circuit. In fact the formal H_k factors as H₀∏_j (b+Σ_{x∈X_j}x); distributing H₀ across the group sums reduces the multilinearization to one within-group quadratic per summand and gives a polynomial-size circuit. The sample therefore tests and rejects literal memo-table enumeration, not all schemes for compressing histories.

## A deletion decision oracle can find one witness but does not generally give the count

Fix 1≤k<n and an unknown family F of k-subsets of [n]. An oracle query Q⊆[n] asks whether some W∈F satisfies W⊆Q. By first querying [n] and then greedily deleting one element whenever the answer stays YES, one can find a witness or certify none with at most n+1 queries: the final YES set is inclusion-minimal, and so equals a witness. In contrast, consider F₀ consisting of all k-subsets and F_M=F₀\{M} for any one k-subset M. With yes/no outputs these two oracles differ exactly at Q=M: if |Q|<k both say NO, if |Q|=k only its one k-set is possible, and if |Q|>k at least two k-sets remain before the deletion.

On the F₀ execution a deterministic exact counting or full witness-polynomial algorithm must therefore query every M, requiring at least binomial(n,k) queries. With at most q queries and error at most 1/3 on every oracle, couple its random bits on F₀ and F_M. With probability at least 1/3 it is correct on both, so the two transcripts must diverge with at least that probability. This implies each M is queried with probability at least 1/3 on the F₀ run. Summing gives q≥binomial(n,k)/3. The reasoning even works if the oracle returns the first admitted witness in a fixed total order: each baseline query can distinguish at most the single deletion of the witness it returns, although Q need not equal that witness. The full witness polynomial here is Σ_{W∈F}∏_{i∈W}x_i; deleting M changes one coefficient even in positive characteristic.

Finite check: for n=8,k=4, enumerate the 70 possible deletions and 256 queries. In 17,920 comparisons the yes/no change occurred exactly at the 70 predicted pairs; the 163 first-witness-answer changes each deleted the baseline answer. This is a check of the oracle statements, not a graph lower bound.

**Boundary.** This oracle abstraction deliberately hides F, whereas a SAT algorithm receives a formula and a graph algorithm receives a graph. The result does not rule out exploiting formula structure, constructing other decision instances, randomized isolation, or any unrestricted decision-to-counting reduction. It isolates why “just keep asking the same yes/no question on subsets” is not a sufficient general bridge. The next targets are compact representations of reachable mask families and structural information a concrete decision instance gives beyond this oracle.
