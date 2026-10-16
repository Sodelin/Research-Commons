# Direct obstruction 11: normalized untilted dense-prior chi-square diverges

Date: 2026-10-16. Prepared by dot for Nolan. Status: complete hand-proof candidate, not independently reviewed or Lean-verified. This concerns the actual normalized Gibbs mixture. It is distinct from the Gaussian partition-function tilt and from dropping denominators.

## Statement

Fix an integer k>2 and fixed b>0. Let D=binom(n,k), a=b/√D, and draw all k-subset coefficient signs s independently and uniformly once before all samples. Set
F_s(x)=aΣ_{|S|=k}s_Sχ_S(x),
P_s(x)=exp(F_s(x))/Σ_y exp(F_s(y)).
Let Q_T=E_s[P_s^{⊗T}] and U be uniform on the n-spin cube.

For every fixed c₀>0 and T=ceil(c₀√D/b²),
χ²(Q_T,U^{⊗T})→∞ as n→∞.

Every member remains an exactly k-local Gibbs state with coefficients ±b/(β√D), admitted whenever β≥b/√D. The prior is untilted and the density is normalized exactly.

This theorem rejects this unconditioned chi-square proof route. It does not show TV(Q_T,U^T) is large, and it does not reject the good-event-conditioned prior of note 10.

## 1. A rare ferromagnetically biased set of coefficient signs

Take η=1/100 and write h(η)=−ηlogη−(1−η)log(1−η)<1/16. Define the fixed k-dependent constant
c=2log2/[1−(1−2η)^k].
For n sufficiently large, set
α=cn/(b√D)≤1/2.
Let π_α be the product sign law with E s_S=α, and π₀ the uniform product sign law. The biased law is used only to lower-bound the mass of a set under the original prior.

Write K(x)=Σ_{|S|=k}χ_S(x), and decompose
F_s(x)=cn K(x)/D+R_s(x),
R_s(x)=aΣ_S(s_S−α)χ_S(x).

For fixed x, Hoeffding's inequality gives
π_α(|R_s(x)|>3b√n)≤2exp(−9n/2).
A union bound over all 2^n configurations implies
π_α(||R_s||_∞≤3b√n)≥1−2exp[−(9/2−log2)n].

Also, with S=Σ_S s_S,
π_α(S>2Dα)≤exp(−Dα²/2).
Let E be the intersection of these two events. For all sufficiently large n, π_α(E)≥1/2.

The exact prior likelihood ratio is
dπ_α/dπ₀(s)=∏_S(1+αs_S).
On E, log(dπ_α/dπ₀)≤αS≤2Dα². Therefore
π₀(E)≥(1/2)exp(−2Dα²)
=(1/2)exp(−2c²n²/b²).

## 2. Exact Gibbs mass of the all-plus configuration on E

If x has r minus spins and m_x=1−2r/n, sampling k indices with and without replacement gives
|K(x)/D−m_x^k|≤k(k−1)/n.
Indeed their total-variation distance is at most the probability of a repeated index, at most k(k−1)/(2n), and the sampled product has range [−1,1].

For ηn≤r≤(1−η)n, it follows that
cn K(x)/D≤cn(1−2η)^k+ck(k−1).
The number of strings outside this middle range is at most 2exp(nh(η)). For every x, K(x)/D≤1; at the all-plus string +, it is exactly 1.

Thus, on E,
Σ_x exp(F_s(x))
≤exp(3b√n)[2exp(cn+nh(η))
 + exp(nlog2+cn(1−2η)^k+ck(k−1))].
By the choice of c, the second exponent is cn−nlog2+ck(k−1), at most cn for n sufficiently large. Hence
Σ_x exp(F_s(x))≤3exp(cn+nh(η)+3b√n).
Meanwhile F_s(+)≥cn−3b√n. Consequently
P_s(+)≥(1/3)exp(−nh(η)−6b√n).

For fixed b and sufficiently large n, h(η)+6b/√n+(log3)/n≤1/8. Therefore every s∈E satisfies
P_s(+)≥exp(−n/8).

This shell bound works for either parity of k: including both endpoint shells is an upper bound even when only the all-plus endpoint maximizes the mean energy.

## 3. A singleton transcript forces a large chi-square moment

Let A be the T-sample transcript consisting entirely of all-plus strings. Then
U^T(A)=2^{−nT},
Q_T(A)≥π₀(E)exp(−nT/8)
≥(1/2)exp(−2c²n²/b²−nT/8).

For any Q and U, Cauchy–Schwarz on A gives
1+χ²(Q,U)≥Q(A)²/U(A).
Therefore
1+χ²(Q_T,U^T)
≥(1/4)exp[(log2−1/4)nT−4c²n²/b²].

At T=ceil(c₀√D/b²), the positive exponent dominates because √D/n→∞ for fixed k>2. This proves the stated divergence.

## Scope and consequence for the continuing proof

The event E has extremely small original-prior mass. Therefore this lower bound on chi-square cannot be converted into a claim that the mixture has large total variation. The whole phenomenon is consistent with a statistically hard mixture whose chi-square is spoiled by rare prior components.

Moreover E is eventually excluded by the normalization event G in note 10: on E,
Z_s=E_U exp(F_s)≥exp[(c−log2)n−3b√n],
where c>log2, whereas note 10 requires Z_s near cosh(a)^D≤exp(b²/2). Thus this obstruction does not settle the indicator-retaining conditioned moment. It proves why conditioning, or a different divergence/truncated-data argument, is essential.

Exact conditioning construction:
https://github.com/Sodelin/Research-Commons/blob/fa610a15f5e8d4c579d192f550758617fb4735b8/research/2026-10-16-g6-gibbs-certification/DENSE-UNTILTED-GATES-10.md

General P1 remains open. No √D/ε² lower bound, new upper bound, empirical claim, or novelty claim follows from this failed-route result.

## Independent manual review record, 16 October 2026

A separate dot mathematical reviewer read the complete immutable candidate at commit 3da3992cdca0901ddaed1b6fa5d5599aef13fc0d and returned scoped hand-proof PASS. The reviewer checked the Hoeffding and union bounds, prior likelihood-ratio comparison, sampling-without-replacement estimate, shell partition-function bound, all-plus probability, singleton-transcript chi-square lower bound, and final dominance using sqrt(D)/n tending to infinity.

This acceptance retains fixed integer k>2, fixed b>0, fixed c0>0 and n tending to infinity. It makes no jointly uniform b-to-zero claim, no TV distinguishability conclusion, and no claim against the normalization-good conditioned prior. The original dated candidate body above is preserved as history; its initial unreviewed status is superseded only within this stated hand-review scope. No Lean verification, execution, novelty conclusion, or general P1 closure is asserted.
