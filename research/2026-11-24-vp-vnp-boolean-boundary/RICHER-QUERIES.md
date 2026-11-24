# Richer decision queries: approximate counting works, exact counting still has a black-box barrier

24 November 2026 · Dot and internal proof review. Hand deductions and finite check. Approximate counting by randomly hashing witnesses is classical (see [Stockmeyer](https://doi.org/10.1145/800061.808740) and the isolation techniques of [Valiant–Vazirani](https://doi.org/10.1016/0304-3975(86)90135-0)). No novelty claim, no Lean replay, and no result on P vs. NP itself. This is a follow-up to [the deletion-oracle boundary](PATHS-AND-WITNESSES.md).

## What XOR restrictions buy

Let F be an unknown subset of the n-dimensional Boolean cube and let T=|F|. The oracle accepts an affine restriction Ax=b over F₂ and answers whether it contains a witness from F. For a concrete SAT formula, checking satisfiability after adding such constraints is still a SAT question, via a polynomial-size encoding of the XORs with auxiliary gate variables. In this paragraph the oracle answers only existence.

Draw A and b independently and uniformly with d rows, and let Z count witnesses obeying the restriction. A given witness survives with probability 2^(−d). A distinct pair survives jointly with probability 2^(−2d), since each row gives independent constraint values on the two distinct vectors when b is random. Write μ=T/2^d and q=Pr(Z>0). Then E[Z]=μ, Var(Z)≤μ, and
```
μ/(1+μ) ≤ q ≤ min(1,μ),
μ − T(T−1)/(2·2^(2d)) ≤ q.
```
The first lower bound follows from Cauchy–Schwarz and E[Z²]≤μ+μ²; the second follows from the first two inclusion–exclusion terms for the survival events. This is why the chance of getting a YES estimates the count even though each answer is one bit.

For a concrete guarantee, first query d=0 and return zero if empty. For d=0,…,n+2, estimate q_d to additive error 1/8 with total failure probability at most δ/2, using O(log((n+3)/δ)) independent queries per scale and Hoeffding. Take the largest d whose estimate is at least 1/2. On the good event it exists and is less than n+2. Then q_d≥3/8 and q_(d+1)<5/8, so 3/8≤μ_d<10/3. This already gives a constant-factor interval.

For 0<ε<1, use d'=d+ceil(log₂(8/ε)). On the same good event 3ε/128≤μ'=T/2^d'≤5ε/12. The inclusion–exclusion bound makes the downward bias μ'−q' at most (5ε/24)μ'. With O(ε^(−3) log(1/δ)) fresh queries, a multiplicative Chernoff bound estimates q' to relative error ε/4 with failure probability at most δ/2, because q'≥μ'/(1+μ')≥(3ε/256). Multiplying the estimated hit rate by 2^d' gives relative error less than ε with total failure probability at most δ. This does not recover an exact integer count in general: separating T from T+1 by relative accuracy alone can require ε of order 1/T.

Exact finite check: enumerate all 255 nonempty subsets of the 3-bit cube and all affine restrictions at d=1 and d=2. All 510 family/scale cases satisfy the three displayed inequalities by integer comparison. No simulation extrapolation is needed for the hand bounds.

## What even richer yes/no queries still cannot do exactly

Now let the oracle answer arbitrary DNF queries on the hidden membership bits of F, with any number of terms but at most t literals per term. This includes an existential query about at most t possible witnesses or nonwitnesses satisfying any explicitly allowed relation, including shared XOR restrictions. Fixing partial membership bits, answer YES if any term is consistent and set at most t new bits to make that term true; otherwise answer NO because every term is already contradicted. All answers remain valid under every completion. After q queries at most qt bits are fixed. If qt<2^n, toggling one unset bit gives the same transcript but changes both the exact cardinality and its residue modulo any fixed integer >1. Hence deterministic exact or modular counting in this oracle model needs at least ceil(2^n/t) queries. For parity and unrestricted query descriptions, this is tight by testing parity on blocks of at most t membership bits and adding their answers modulo two.

This lower bound does not apply to algorithms reading the formula itself, to compact queries that globally constrain many membership bits, or to approximate counting. Conversely, the hashing estimate does not produce a small circuit computing the required formal witness polynomial. Together these give a precise boundary: richer yes/no questions can recover quantitative information, but exact counting and formal circuit size are separate barriers.
