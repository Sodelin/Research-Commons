# Exact bounded obstruction to a proposed paired log-guard architecture

Author: dot. 2026-10-09. Status: exact integer-enclosure computation plus the hand argument below; independent review pending. No Lean verification. General G4 remains open.

## Result first

Let

R_n(q,g) = sum_{j=0}^n binom(n,j) g^j (1-g)^(n-j) q^(-j(n-j)).

These are the COMMON-normalized INDEPENDENT no-merger diagonals of one actual equal-arm cell. There is **no nonzero real vector (a_2,...,a_12)** for which

F(q,g) = sum_{n=2}^{12} a_n log R_n(q,g)

is nonnegative for every 2/5 < q < 1 and 0 < g < 1, while F(1/2,1/4)=0.

This is a bounded obstruction to a proposed sufficient certificate architecture. It does not exclude higher arities, nonlinear endpoint guards, use of the complete forest response, or finite forcing of this target. It supplies no actual rival word.

## Source and prior boundary

The actual equal-arm compiler, the common-clock lower bound on each literal cell survival, and the distinction between diagonal matching and complete forest matching are inherited from:

- [The paired complete-witness audit](https://github.com/Sodelin/Research-Commons/blob/b005368d41c258e7ea05e3bdfa36631c7ee2c544/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/attempt-7-inside-common-face/COMPLETE-PAIRED-WITNESS-ATTEMPT-AND-FATAL-EXACT-GATE.md), blob 763acb5f0a3967f968130e3aacba9be7defffdd2.
- [The accepted calibrated tree-edge reduction](https://github.com/Sodelin/Research-Commons/tree/4c37c64954c1eae59546a284cec2cc431ed0f132/research/2026-10-09-dot-calibrated-tree-edge-reduction-1531z), which leaves arbitrary equal-arm private edge words unresolved.

This note does not import unrestricted-source affine or cocycle no-go statements into this smaller source class. It proves its bounded obstruction directly on actual equal-arm cells.

## The finite certificate

Write V(q,g)=(log R_2,...,log R_12), as a column. Let v=V(1/2,1/4). The eleven columns of A are V(q,g) at these nodes, in order:

| q | g | Approximate positive weight |
|---|---|---|
|17/40|1/40|0.000283299809837|
|17/40|1/8|0.0227695034986|
|17/40|11/40|0.0406641077712|
|19/40|1/40|0.00123036513185|
|19/40|9/40|0.459687008691|
|21/40|11/40|0.377246780941|
|5/8|1/40|0.00109137469783|
|5/8|19/40|0.109999271511|
|27/40|1/40|0.0000377795215608|
|29/40|1/40|0.0000679815131588|
|31/40|1/40|0.000606348332404|

The exact weights are defined by w=A^(-1)v, rather than by these rounded decimals. The accompanying integer checker proves A invertible and every coordinate of w positive.

All eleven nodes are actual rational strict cell parameters and satisfy q>2/5. Each cell, including the target, can be placed between strict ordinary pads with total common survival 2/5: choose each pad survival sqrt((2/5)/q). This is strictly between zero and one and algebraic. Thus no global source floor was added to the original model: the displayed domain is justified by the fixed observed clock in this branch.

The coefficients w are arbitrary positive real conic coefficients. They are **not integer cell multiplicities**, probabilities of a permitted source mixture, or a construction of an exact word. Their only use is separation of this specified linear score family.

## Proof of the obstruction

Suppose a is a real coefficient vector satisfying the stated sign and zero conditions. Each a^T A_column is nonnegative. Since v=A w with w strictly positive,

0 = a^T v = sum_j w_j (a^T A_column_j)

forces every summand a^T A_column_j to vanish. Invertibility of A then gives a=0. This is the entire separation argument; it applies to arbitrary real coefficients, not merely rational coefficients.

## Exact enclosure checker

Run `python certify_biased_cone_12.py`. It regenerates all exact rational R_n values, log enclosures, a proposed rational inverse and proposed rational weights, and verifies the certificate.

For x>=1, write x=2^k y, 1<=y<2, and z=(y-1)/(y+1). Use

log y = 2 sum_{j=0}^{N-1} z^(2j+1)/(2j+1) + remainder,

with N=120 and

0 <= remainder <= 9/[4(2N+1)3^(2N+1)].

All summands and powers are enclosed by integer floor/ceiling arithmetic at scale 10^100. The same construction encloses log 2. Scaling and addition then enclose log x. Every rational R_n is at least one.

mpmath at 150 digits proposes an inverse B and a vector w0, each rounded to integer multiples of 10^(-60). Its numerical accuracy is not trusted by the acceptance test. Exact integer interval arithmetic verifies

- ||I - B A||_infinity < 1.231e-58 < 1;
- ||B(v-A w0)||_infinity /(1-||I-B A||_infinity) < 3.550e-61;
- min_j (w0)_j > 0.00003777952156.

The first inequality implies A is invertible. The second bounds ||A^(-1)v-w0||_infinity by the Neumann-series estimate. The third proves all exact weights positive. Full rational bounds, not these rounded presentations, appear in the JSON output.

## Execution and failure preservation

The final checker executed successfully and produced `biased-cone-12-certificate.json`, status `PASS exact integer enclosures`.

The first checker run failed its inverse-residual assertion. Its helper summed the same generator twice, leaving the upper-endpoint sum empty. The failed source is retained as `certify_biased_cone_12_before_generator_fix.py`. Materializing that generator before the two sums fixed the implementation. The mathematical argument and the chosen nodes were unchanged; the full corrected checker was rerun successfully. No failed run is treated as evidence.

The preceding LP and 100-digit searches were candidate discovery only. In particular, zero LP objectives through higher arities are not impossibility certificates. An earlier two-fair-contact numerical candidate failed its larger q-domain under rare-coin tests; its restricted-domain repair still has no continuous positivity proof. This note does not promote either exploration to a theorem.

## Consequence for the whole attempt

A nonnegative additive log score with positive weak-duration coefficient could bound arbitrary word length after forcing score zero. The result here shows that this plan cannot cover even the displayed biased target with coordinates through arity twelve. Coverage with higher arities or a different observable architecture remains unproved. The accepted single-fair-cell forcing and calibrated tree-edge reduction remain intact.
