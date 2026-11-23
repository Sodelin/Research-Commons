# VibeMath draft: remainder counts cannot see a Goldbach pair

**Submission type:** Scoped mathematical note and reproducible obstruction example.  
**Claim status:** Hand proof plus exact executable fixtures. No Lean check. Not a Goldbach solution or a novelty claim. Not submitted.

Could very accurate remainder counts force two selected numbers to sum to one given even target? Not by themselves. For every even wheel modulus W > 2 and integers d ≥ 2 and B ≥ 1, take N = WdB and keep only integers below N coprime to W. We build two sets of density 1/d among those integers. They have identical counts in all residue classes modulo every divisor of W. For each reduced residue class modulo W, every prefix count differs from the prescribed density by less than one. Yet one set has no pair at sum N and the other has exactly |U|/d ordered pairs, where U is the set of eligible integers.

The construction is a shift inside one residue class. In each pair of opposite reduced residues, enumerate the complementary pairs (a_j, b_j). At indices divisible by d, choose either (a_j, b_j) or (a_j, b_{j+1}). The shift by one index changes the pairing without changing the residue counts or increasing the prefix error past one. The two chosen index classes in the shifted version are disjoint.

This is a test for arguments that use only these specified marginals, not a claim about prime behavior or about what can be deduced from Dirichlet GRH. It sits beside, and is much weaker in scope than, [Tao's sieve parity obstruction](https://terrytao.wordpress.com/2014/07/09/the-parity-problem-obstruction-for-the-binary-goldbach-problem-with-bounded-error/). For context, see [Lichtman's upper bounds](https://arxiv.org/abs/2309.08522) and the [Chen theorem blueprint](https://subfish-zhou.github.io/goldbach-lean/blueprint/chap-chen.html).

[Full assumptions and proof](README.md) · [Exact replay code](replay.py) · [Recorded output](REPLAY.txt)
