# G3 v3: fourth-moment rejection on an original observable row

**New result over the pilots:** An exact full-support natural topology response on 16 same-taxon copies passes all v2 moment inequalities and the earlier strict 5/12 quartet bound, but cannot be extended to even 20 same-taxon copies of any admitted source. The checker finds a negative fourth-moment determinant; a shorter separate integer-count certificate gives the same rejection.

This is a bounded hand derivation with an executed exact rational checker, not a full G3 recognizer or Lean verification. The underlying moment method is standard. An overlap check of the prior reconciliation found different Hankel/finite-rank results (including why a finite-rank assumption does not apply), no matching fixture; historical novelty is not claimed. V1 and v2 are unchanged.

## Observable input, no extra measurements

Read one supplied natural, completed, rooted unranked labelled topology-response row that resolves the restriction to sixteen copies of one taxon. Divide those copies into four disjoint groups of four. Each group's event is that its restriction is a balanced rooted quartet (2+2 at its own root). One can retain the same four original taxa and observation adapter from the [original-observation quartet NO](https://github.com/Sodelin/Research-Commons/blob/f4ba57788564192f4705309b0aeb2cce404e35db/research/2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/README.md); only the supplied target's chosen copy count differs. Do not apply if the supplied observation map lacks the event probabilities. The checker takes a complete, normalized, block-symmetric four-bit event table, not source parameters.

Let m_k be the probability the first k groups all balance, with m_0=1. Write p,q,r,s for m_1 through m_4. In the [original G3 scope](https://github.com/Sodelin/Research-Commons/blob/ca0076c5603f46f02eb0d4065de9f482f928fbbc/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md), every realizing source must retain its original graph, completion and one physical tuple at any hypothetical larger size. Natural within-taxon equivariance and the existing [same-source unranked all-panel projectivity](https://github.com/Sodelin/Research-Commons/blob/e43167ff700bd101ecdf581764c870c2f3308edf/research/2026-10-11-dot-accepted-connected-union1591-1247z/source-store/4936fb211505d9c5961256ba4f1a4c63db0065c7c94ccadf3fcd67a320f270c3.lean) hold separately in COMMON and INDEPENDENT. Neither independence across the four groups nor reuse of their marginal law as a new physical source is presumed.

## Fourth-moment screen and finite proof

Let K denote the number of balanced groups out of N hypothetical groups of four, all measured under one alleged source. For j≤4, expectation of the falling factorial (K)_j is exactly (N)_j m_j, since it counts ordered distinct successful groups. Consequently the jth ordinary moment of Y=K/N converges to m_j as N grows. The checker computes those ordinary finite moments by expanding powers into falling factorials.

The following matrices must be positive semidefinite:
```
H = [ 1  p  q ]
    [ p  q  r ]
    [ q  r  s ]

G = [ p-q  q-r ]
    [ q-r  r-s ].
```
Indeed their finite versions encode expectation of a square of a quadratic in Y and expectation of Y(1−Y) times a square of a linear polynomial in Y. Both are nonnegative for every finite N. Taking limits proves the claim; no de Finetti assumption or infinite source is needed. In particular q*s≥r², which was unavailable in v2. A strict negative limit principal minor implies a finite negative minor; the code tries N=5,10,20,… only after a strict limiting failure and termination then follows from convergence. This searches a certificate size, not physical networks, source parameters, or source words. A pass is UNKNOWN, not YES. The scheme can extend to larger supplied copy counts by using moment and localizing matrices of degrees permitted by the observed row; those larger cases are not implemented here.

## Fixture, cross-check and independent finite rejection

Give weight 999/1000 to a uniformly relabelled rooted tree that joins a 7-tip comb and a 9-tip comb. Give weight 1/1000 to the uniform distribution over all 6,190,283,353,629,375 labelled rooted nonplane binary 16-tip trees. This defines a mathematical target row, not an admitted physical mixture. Every eight-to-sixteen-copy target topology in its corresponding restriction has positive probability, and compatible prescribed smaller rows can be obtained by restricting the same tree distribution.

For the first component, a quartet balances exactly when it has two leaves from each side. Counting the successive draws without replacement gives (p,q,r,s)=(27/65,126/715,54/715,0): four successes would require eight leaves on the 7-leaf side. The positive uniform component is counted by v2's root-split dynamic program, independently checked against the exact 8- and 12-tip counts and the 16-tip tree total. It never enumerates all individual trees. The rational mixture has:

```
p = 13493/32500               < 5/12
q = 203389/1155000
r = 1829878363/24249225000
s = 146277641/41021605625000  > 0
```

All v2 gaps are strictly positive. The v3 checker computes exact negative principal minors of H, including its lower 2×2 determinant q*s−r², and certifies a negative full 3×3 determinant already with N=5.

A separate short exact proof uses just the fact that the five-block count K is an integer: (K)_2(K−3)²≥0, also at K=0 or K=1 where the first factor vanishes. Expanding as (K)_4−(K)_3+(K)_2, the alleged source would force
```
E[(K)_2(K−3)²] = 120*s−60*r+20*q
               = −237932438462/236663109375 < 0.
```
The required extra quartet is hypothetical. This contradiction is source-universal and needs no actual 20-copy reading.

## Replay and limits

From the workspace root:
```sh
set -o pipefail
python -B g3_obstructions_v3/obstruction.py | diff -u g3_obstructions_v3/fixture_result.json -
```
Replay checks exact normalization and symmetry, nonzero full-support component, smaller-count controls, finite impossibility, positive v2 gaps, an invalid asymmetric input, two endpoint controls and a nontrivial two-atom Bernoulli mixture. These are rational input checks; there is no exact algebraic parser yet. Neither the PSD tests nor the fixture excludes any point inside the closure of the legal source image. No physical sufficiency, strict-boundary exclusion, rate identification, or global G3 termination follows.
