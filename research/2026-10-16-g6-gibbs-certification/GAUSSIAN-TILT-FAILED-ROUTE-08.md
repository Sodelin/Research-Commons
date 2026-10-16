# Failed-route certificate 08: the untruncated Gaussian partition-function tilt is distinguishable

Date: 2026-10-16. Prepared by dot for Nolan. Status: complete hand calculation, not independently reviewed or Lean-verified. This rules out one proposed lower-bound prior; it is not a lower bound or a solution of P1.

The dense-family obligation and prior audit are recorded at:
https://github.com/Sodelin/Research-Commons/blob/1f08eecab1a4694f0888f542600b1c7721fa7892/research/2026-10-16-g6-gibbs-certification/GENERAL-GAP-AUDIT-07.md

## Proposed cancellation

Let U be uniform on {−1,+1}^n. Let φ(x) be the vector of all D=binom(n,k) degree-k parities, for 1≤k≤n. Thus E_U φ=0 and ||φ(x)||²=D. Draw independent Gaussian coefficients J_S of variance σ²=ε²/D. Write
F_J(x)=Σ_S J_S φ_S(x), Z_J=E_U exp(F_J),
P_J(x)=U(x)exp(F_J(x))/Z_J.

A proposed T-dependent prior replaces the Gaussian law π by
dπ_T(J)=Z_J^T dπ(J)/E_π Z_J^T.
It cancels the denominators in the T-sample mixture. Gaussian integration gives its exact likelihood ratio:
dQ_T/dU^T(x_1,…,x_T)=exp(λA)/C,
A=||Σ_{a=1}^T φ(x_a)||²,
λ=ε²/(2D), C=E_{U^T} exp(λA).

This is a valid probability calculation. The untruncated Gaussian coefficient prior itself also has an admission problem: it is not supported on the coefficient-bounded Gibbs class. The argument below shows a separate, decisive statistical problem even before addressing that admission issue.

## Exact distinguishability bound

Put M=T²D. The triangle inequality gives A≤M. The event that all T strings coincide has U^T-probability 2^{-n(T−1)}, and on it A=M. Therefore
log C≥λM−s, where s=n(T−1)log2.

The relative entropy identity and its nonnegativity give
0≤KL(Q_T||U^T)=λ E_{Q_T}A−log C.
Consequently
E_{Q_T}(M−A)≤s/λ.
Markov's inequality yields
Q_T(A≥M/2)≥1−2s/(λM).

Under U^T the samples are independent and E_Uφ=0, so E_{U^T}A=TD. Another application of Markov gives
U^T(A≥M/2)≤2/T.

Hence, with total variation in the usual half-L1 convention,
TV(Q_T,U^T)≥1−4n(T−1)log2/(ε²T²)−2/T.

In particular TV tends to 1 whenever ε²T/n tends to infinity (and T tends to infinity). For fixed k>2 and T=c√D/ε² with any fixed c>0, this condition holds as n grows. The proposed prior is therefore unsuitable for proving indistinguishability at the conjectured √D/ε² scale. The explicit statistic A already distinguishes its sample mixture from uniform.

## Consequences and limits

The failure is caused by the large partition-function tilt; concentration under the original weak Gaussian prior cannot be carried over without proof. The argument does not reject the original untilted dense Gibbs prior. It does not reject every bounded, truncated, or conditioned replacement: those replacements lose the displayed Gaussian integral identity and require fresh admission, separation, normalizer, and testing proofs.

No Gibbs density was replaced by 1+F. No assertion of novelty is made for this elementary exponential-tilting calculation. The general P1 minimax question and the original dense-prior mixture estimate remain open.
