# G3 v2: observable three-block moment NO certificates

This is a strict improvement over the existing pairwise pilot, not a full G3 recognizer. Hand derivation and executed exact arithmetic; no Lean, historical novelty, or physical source realization claim.

## Inputs and scope

Use the same [original G3 natural all-panel assumptions](../g3_obstructions/README.md), with a supplied natural rooted unranked labelled topology row resolving the restriction to twelve same-taxon copies, divided into three disjoint four-copy groups. No extrapolated observation is given to the checker. For a fixed alleged physical source, natural within-taxon copy symmetry and original same-source all-panel projectivity tie every hypothetical copy extension to that exact same source and physical tuple. This holds separately for either natural inheritance mode. It does not assume that groups are independent, change the original controls or introduce any source graph bound. If the supplied projection hides the needed events do not apply the test.

Let p, q, r be the probabilities that the first one, two, or three groups respectively all have balanced rooted restrictions. For any hypothetical number of groups N ≥ 3, let K be their balanced count and Y=K/N. Pair and triple exchangeability and projectivity give exact ordinary moments:
 
```
E[Y]   = p
E[Y²] = ((N−1)q+p)/N
E[Y³] = ((N−1)(N−2)r + 3(N−1)q+p)/N².
```

The coefficients count ordered index triples with three distinct indices, exactly two, or all identical. For every finite N, the expectation of [u+vY]², Y[u+vY]², and (1−Y)[u+vY]² is nonnegative for every u,v. Taking N→∞ by the explicit formulas yields these necessary inequalities:

* **Pairwise v1:** q−p² ≥ 0.
* **Success-weighted:** p r−q² ≥ 0, the determinant of [[p,q],[q,r]].
* **Failure-weighted:** (1−p)(q−r)−(p−q)² ≥ 0, the determinant of [[1−p,p−q],[p−q,q−r]].

In fact the two weighted matrices sum to the unweighted moment matrix, so joint PSD of the weighted matrices implies v1. The inequalities are symmetric under swapping event and complement. All three diagonals are already nonnegative for a valid 3-bit distribution. Strict limiting failure implies a finite contradiction; the checker doubles N until an exact finite determinant is negative. This terminates when it starts, by the rational formulas and their limits. A pass means UNKNOWN, not that the actual physical fibre is occupied. These closed inequalities also cannot exclude any point in the closure of the source image.

## Strictly positive stronger fixture

On rooted nonplane labelled 12-tip binary trees, mix:

* weight 209/280: a uniform relabelling of a root with 5-tip and 7-tip combs for children;
* weight 143/840: a uniform relabelling of a single 12-tip comb;
* weight 1/12: uniform among all 13,749,310,575 distinct labelled topologies.

These are mathematical row distributions, not proposed preparations. Every topology has positive mass from the third component. Rows on fewer copies can be consistent by literal restriction; the whole four-copy restriction is the ordinary Kingman marginal because balance has probability 1/3 and label symmetry gives uniformity inside each shape.

In the first component, a four-copy block is balanced exactly when it takes two labels from each side of the original root. A restriction within one side is a comb; a 3+1 split is also a comb. Thus p=14/33, q=2/11, r=0: after two balanced blocks use four of the five left-side labels there are not enough remaining for the third. The second component gives p=q=r=0. The third is counted by an exact root-split recursion on counts in each of the three labelled groups. For any ordered root split, multiply child counts and the binomial choices of labels for each group, then divide by two across all ordered splits. A group of exactly four leaves balances iff it splits 2+2 at this root or all four are on one side and its child already balances. The recursion checks totals against (2n−3)!! and independently reproduces the v1 eight-tip exhaustive event counts.

The mixture has
```
p = 1/3
q = 6289/45045
r = 299773/290990700
q−p² = 428/15015 > 0
p*r−q² = −50200346813/2621535216300 < 0.
```
It passes the old pairwise test and the failure-weighted test, but fails the success-weighted test. Reflecting the bit outcomes interchanges these two weighted determinations and is included as an arithmetic control, not a separate physical example.

A simpler independent certificate for this fixture uses **four** hypothetical groups. For any K, K(K−2)² is nonnegative, but projectivity would force its expectation to be 4p−12q+24r = −699554/2204475. Indeed K(K−2)² = K − K(K−1) + K(K−1)(K−2). This uses one hypothetical extra group, no extra input data, and rules out all admitted sources at once. The checker also finds a negative finite PSD determinant at N=4.

## Replay

Run `python -B g3_obstructions_v2/obstruction.py | diff -u g3_obstructions_v2/fixture_result.json -` from the workspace root. It checks positive support of the uniform component, exact masses and finite contradiction, the independent four-block polynomial, the v1 uniform-tree count control, and equality controls at Bernoulli parameters 0, 1/3, and 1. Runtime code implements rational inputs only; the hand proof applies to exact real algebraic comparisons as well. A higher-cap implementation should only use moments actually determined by the supplied observation map.
