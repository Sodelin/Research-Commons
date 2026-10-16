# Dense untilted Gibbs prior 10: admission, normalization and separation gates

Date: 2026-10-16. Prepared by dot for Nolan. Status: hand-proof candidate, not independently reviewed or Lean-verified. This supplies three preparatory gates, not the missing testing lower bound. General P1 remains open.

## Setup and standard supplier

Fix 1≤k≤n, D=binom(n,k), and 0<b≤1/(16·3^k). Put a=b/√D. Let s=(s_S) be independent uniform signs indexed by the k-subsets of [n], drawn once before all samples. Under uniform U on {−1,+1}^n, define
F_s(x)=a Σ_{|S|=k}s_S χ_S(x),
Z_s=E_U exp(F_s), B=cosh(a)^D, W_s=Z_s/B,
P_s(x)=U(x)exp(F_s(x))/Z_s.

This is exactly the diagonal Gibbs state of H_s=−F_s/β. It is k-local, has zero identity coefficient, and every nonzero coefficient has magnitude a/β. Admission is therefore the explicit condition β≥b/√D.

We use the classical Bonami–Gross–Beckner inequality ||f||_4≤3^{k/2}||f||_2 for degree≤k Boolean polynomials. Primary mathematical source discussing and proving hypercontractivity:
https://mirror.theoryofcomputing.org/articles/v009a029/
The consequences E f⁴≤9^k(E f²)² and E|f|≥||f||₂/3^k below are standard; no novelty is claimed for them.

## 1. Exact annealed normalization and variance

Independence of the coefficient signs gives E_s Z_s=B, hence E_s W_s=1. Set t=tanh(a), u=t², and K(z)=Σ_{|S|=k}χ_S(z). Averaging the product Z_s² over s and changing variables z=xy gives the exact identity
E_s W_s²=E_z ∏_{|S|=k}(1+uχ_S(z)).
Indeed cosh(a(χ_S(x)+χ_S(y)))/cosh(a)²=1+t²χ_S(xy).

Orthogonality and hypercontractivity imply
E K=0, E K²=D, E|K|³≤sqrt(E K²·E K⁴)≤3^k D^{3/2}.
Also |K|≤D.

For each z, Taylor expansion with an explicit remainder gives
log∏_S(1+uχ_S(z))=uK(z)−Du²/2+R(z),
|R(z)|≤r:=Du³/[3(1−u)].
Similarly,
E exp(uK)≤1+Du²/2+v,
v:=exp(Du)u³ E|K|³/6.

Thus, using exp(−A)(1+A)≤1 for A≥0,
E W²≤exp(r)(1+v).
Because u≤a²=b²/D, b≤1/2, and D≥1, we have r≤(4/9)Du³<log2 and Du≤1/4. Therefore
Var(W)≤2r+2v≤C_k b⁶ D^{−3/2},
where the explicit safe choice C_k=4·3^k suffices.

This bound is finite-n. It uses the full dense degree-k feature set, not a disjoint-block restriction.

## 2. A high-probability event with negligible denominator error

Define η=b²D^{−5/8} and
G={s: |W_s−1|≤η}.
Chebyshev gives
π(G^c)≤C_k b²D^{−1/4}.

For fixed k, G has probability tending to one, uniformly over the stated b-range. In particular it is nonempty once the displayed upper bound is below one. If T≤C√D/b² for a fixed constant C, then Tη≤C D^{−1/8}→0. On G,
B^T(1−η)^T≤Z_s^T≤B^T(1+η)^T,
so replacing a denominator Z_s^T by B^T costs a multiplicative exp(O(Tη))=1+o(1), uniformly over G. This statement is about the explicitly conditioned prior only; it does not discard rare contributions inside an unconditioned high moment.

## 3. Every admitted sign in G is far from uniform

For every sign vector, orthogonality gives E F_s²=b². Hypercontractivity gives E F_s⁴≤9^k b⁴. By moment interpolation,
E|F_s|≥(E F_s²)^{3/2}/(E F_s⁴)^{1/2}≥b/3^k.

Let R_s(x)=exp(F_s(x))−1−F_s(x)≥0. Since E F_s=0,
E R_s=Z_s−1.
The reverse triangle inequality therefore gives
E|exp(F_s)−Z_s|≥E|F_s|−2(Z_s−1).

On G, since η≤b² and log cosh(a)≤a²/2,
1≤Z_s≤(1+b²)exp(b²/2)≤1+2b²≤2.
(The penultimate scalar inequality holds for 0≤b²≤1/4.)
Consequently
||P_s−U||₁≥[b/3^k−4b²]/Z_s≥3b/(8·3^k)≥b/(4·3^k).

In particular take b=8·3^k ε with 0<ε≤1/(128·9^k). Every state in the conditioned prior is then at full trace-norm distance at least 2ε from the maximally mixed state. Its admission condition is β≥8·3^k ε/√D. These are explicit fixed-k small-ε constants, not a statement uniform over arbitrary k and ε.

No prior conditioning on an unproved separation property is used: the all-instance separation follows from the proved normalization event. The state remains the exact Gibbs state throughout.

## 4. The remaining likelihood second moment

For r_S=s_S+s'_S, write Z_r=E_U exp(aΣ_S r_Sχ_S). Under π conditioned on G, the exact T-sample chi-square identity is
1+χ²(Q_T,U^T)
= E_{s,s'|G}[(Z_{s+s'}/(Z_s Z_s'))^T].

Sections 1–2 reduce this, up to 1+o(1) at T=O(√D/b²), to the truncated numerator moment
E_{s,s'}[1_G(s)1_G(s') Z_{s+s'}^T] / [π(G)² B^{2T}].
A bound keeping this quantity close to 1 would provide the sought indistinguishability gate. It has NOT been proved here. In particular, closeness of each individual normalizer in probability does not itself control a likelihood second moment.

Dropping the two good-event indicators is unsafe. For example, in the unconditioned expansion, the sign pair with all coefficients +1 has prior mass 2^{−2D}; its all-plus spin contribution gives
E Z_{s+s'}^T / B^{2T} ≥ 2^{−2D−nT} exp(2aDT)/B^{2T}.
At T=c√D/b², the exponent includes (2c/b−2log2)D−nT log2−2T log B. For fixed k>2 and suitable small fixed b relative to c, this lower bound diverges with n. Such exceptional sign vectors are exactly why the truncated moment cannot be replaced by its unconditioned counterpart. This calculation does not show that the conditioned prior is distinguishable.

The previously rejected Gaussian Z^T-tilt is a different prior and cannot repair this gap:
https://github.com/Sodelin/Research-Commons/blob/8d657330a4f9f0aee087780095c5e2c77312cef1/research/2026-10-16-g6-gibbs-certification/GAUSSIAN-TILT-FAILED-ROUTE-08.md

## Scope

The new work here is a transparent source-faithful proof attempt toward the original dense-family gate. No lower bound of order √D/ε² is claimed. If its remaining moment bound is eventually proved, diagonal sampling would transfer it to collective quantum measurements and to the two-unknown total-copy experiment by the existing simulation argument. That final implication is conditional on the missing statistical bound.

## Addendum: scoped independent manual review (2026-10-16)

An independent dot mathematical review read the complete candidate at fa610a15f5e8d4c579d192f550758617fb4735b8 and returned scoped manual PASS for: coefficient admission; the exact cosh variance identity; the logarithmic remainder; the hypercontractive third-moment estimate and safe C_k; the good-event probability and Tη rates; the all-instance L1 separation and explicit ε/β constraints; the indicator-retaining chi-square identity; and the exceptional-sign demonstration against dropping those indicators. The review does not accept the unproved truncated moment, a √D/ε² testing lower bound, novelty, or Lean verification. Earlier candidate bytes are retained above.

## Addendum: spin-glass prior boundary

Dey and Wu's primary arXiv:2212.14571v2, equations (1), (3)–(5), Theorem 1.9 and Proposition 4.4, study the corresponding cosh/cluster decomposition for symmetric disorder and identify leading zero-field clusters of size 3 for even interaction order and 4 for odd order. Their large-cluster reduction is an L2 statement; their fluctuation theorem is distributional.
https://arxiv.org/pdf/2212.14571v2

The related published article is *Hypergraph Counting and Fluctuations of Mixed p-Spin Glass Models at High Temperature*, Communications in Mathematical Physics 407, 230 (27 September 2026), DOI 10.1007/s00220-026-05748-5. The exact source inspected for theorem details here is the arXiv version, not an assumed identical journal theorem numbering.
https://doi.org/10.1007/s00220-026-05748-5

Our normalization matches their zero-field symmetric-sign model at effective spin-glass inverse temperature a n^{(k−1)/2}=b n^{(k−1)/2}/√D, which tends to zero for fixed k. This effective parameter is distinct from the fixed physical β used in coefficient admission. Their quoted results do not directly bound our good-event-truncated, coupled, growing T-th moment. Uniform finite-n exponential integrability at that T-scale is still required; an L2 error or a limiting Gaussian law cannot be raised to a growing power without that additional proof.
