# Binary Fourier–Poisson decision baseline

2026-10-15. Standard finite-experiment derivation, hand-checked here; not a novelty claim or Lean certificate. This fixes conventions for the proposed research target without asserting a new uniform rate.

## 1. Experiment and loss

Let G be a finite abelian periodic grid, |G|=N, and X a specified nonempty subset of {−1,+1}^G. Use the unitary discrete Fourier transform F (factor N^−1/2), I_x(k)=|(Fx)(k)|² and p_x(k)=I_x(k)/N. Parseval gives sum I_x=N and sum p_x=1. The full-detector, known-exposure, zero-background model is

K_k independently ~ Poisson(μ I_x(k)) = Poisson(B p_x(k)),  B=μN.

Thus μ is mean photons per Fourier pixel, B is expected total photons, and increasing N at fixed μ increases the budget. Using an unnormalized Fourier transform requires replacing I by |DFT(x)|²/N. Missing peaks, detector efficiencies, unknown flux/background or unequal exposure require a different rate vector; B=μN cannot then simply be retained.

Fix a finite group Γ acting by Hamming isometries on X, preserving the labelled intensity vector. For the cyclic binary model, translations, inversion and global contrast reversal qualify if scientifically declared equivalent and preserving X. Under fixed nonsymmetric composition, contrast reversal may not preserve X. General spatial rotations may permute detector coordinates rather than preserve their labelled laws; they need a separately declared observation convention.

Actions A=X/Γ; loss d(a,[x])=N^−1 min_{g∈Γ} #{i: a_i≠(gx)_i}. This is a metric on the orbit set and bounded by one. An alternative action set, e.g. all binary reconstructions rather than only X, changes the decision problem and must be stated. All results below allow randomized Markov-kernel decisions δ(K)∈Δ(A), with an independent random seed permitted. Define R_B=inf_δ max_{x∈X} E_x d(δ(K),[x]).

## 2. Exact-data ambiguity floor

Let C={p_x:x∈X}, M=|C|, with fibre X_c={x:p_x=c}. Set

r_c = min_{q∈Δ(A)} max_{x∈X_c} sum_{a∈A} q(a)d(a,[x]),
R_inf = max_{c∈C} r_c.

These are finite linear programs; minima exist. If the exact intensity c is observed, a separate q can be selected on each fibre, so the exact-data minimax risk equals R_inf. Actions in q are NOT required to belong to X_c. Restricting them to the observed fibre requires a proof or defines a different floor.

For any noisy decision, all x in one fibre have exactly the same K law. Averaging its randomized output gives a common q_c∈Δ(A). Therefore its worst loss within that fibre is at least r_c, proving R_B≥R_inf for every B. This is the standard information-loss/data-processing argument.

For a fibre containing two orbits at distance d0, triangle inequality gives r_c≥d0/2. This need not be the exact radius of a multi-orbit fibre. With exactly two possible orbits and no other action complications, a half-half randomized decision attains d0/2; a deterministic decision restricted to those two actions has worst loss d0. Randomization conventions therefore matter.

## 3. Fixed-N convergence: elementary ML/affinity bound

For distinct c,d∈C define
h²(c,d)=sum_k (sqrt(c_k)−sqrt(d_k))².

This convention ranges from zero to two. Direct summation of Poisson mass functions gives the exact affinity

ρ(P_c^B,P_d^B)=sum_K sqrt(P_c^B(K)P_d^B(K))
               = exp[−(B/2) h²(c,d)].

The identity remains valid with zero rates, without KL finiteness assumptions. For the event P_d^B(K)≥P_c^B(K), summing P_c ≤ sqrt(P_c P_d) gives probability at most ρ. Use ML over the distinct intensity catalogue (fixed tie-breaking), then output an independently randomized exact-data minimax decision q_c for the selected fibre. Under true c,

Pr_c(ĉ≠c) ≤ min{1, sum_{d≠c} exp[−B h²(c,d)/2]} =: e_c(B).

The reconstruction risk is at most r_c+(1−r_c)e_c(B), hence

R_inf ≤ R_B ≤ min{1, R_inf + max_c e_c(B)}.

For M>1, let Δ_N=min_{c≠d}h²(c,d)>0. Then

0 ≤ R_B−R_inf ≤ min{1, (M−1) exp[−BΔ_N/2]}.

For M=1, R_B=R_inf at every budget. This proves convergence for each fixed finite X/N. It is computationally exhaustive and does not imply efficient reconstruction. It is also potentially far from sharp for Hamming loss: full intensity classification can be unnecessary when confused fibres have compatible low-loss decisions.

Risk is nonincreasing in B: from counts at B2≥B1, independently thin each count with retention B1/B2 to simulate the B1 experiment, then apply its procedure. Consequently R_B decreases to R_inf. This uses the declared randomization convention.

## 4. Classical two-point lower bound

For x,y∈X, orbit separation d0=d([x],[y]), let c=p_x,d=p_y. For any randomized reconstruction, integrate the triangle inequality against the common part of their two laws. This yields

R_B ≥ (d0/2)(1−TV(P_c^B,P_d^B))
    ≥ (d0/2)[1−sqrt(1−exp(−B h²(c,d)))]
    ≥ (d0/4) exp(−B h²(c,d)).

The middle step uses TV≤sqrt(1−ρ²). If c=d, the middle bound is d0/2, matching the familiar indistinguishability obstruction. The last relaxed bound loses a factor of two at exact homometry. These are lower bounds on TOTAL risk; subtracting R_inf does not generally produce a matching positive excess-risk lower bound. A maximum over all such pairs may still miss multiway fibre-radius effects.

## 5. Sufficient-statistic and photon-budget cautions

- The full count vector is the observation. Exact p (equivalently autocorrelation) is its parameter; the noisy empirical autocorrelation is not an exact fibre label.
- For real x, I_x(k)=I_x(−k). For a two-element Friedel pair, S=K_k+K_−k is sufficient for that pair's intensity: conditional split is Binomial(S,1/2), independent of x. Self-inverse frequencies are singletons. Thus pair-summed counts retain all decision information under this model.
- Under fixed composition, the DC intensity is fixed and its independent count can be dropped with no loss for randomized decisions. This is not true for unrestricted composition. The Nyquist/self-inverse non-DC intensity is not generally fixed.
- T=sum K~Poisson(B) is parameter-independent; conditionally on T=t, K is Multinomial(t,p_x). This links Poisson photon budgets to random numbers of detected photons. T is an ancillary random sample size; conditioning on a chosen t is a different experiment. Discarding sample-size information while retaining only normalized proportions is not generally equivalent to retaining counts.
- Independent repetitions with the same setting and known exposure can be aggregated; conditional allocation of aggregated counts to repetitions is parameter-independent. If settings vary, aggregate only within identical settings/rate patterns.
- Exposure selection alone cannot split exact intensity fibres. Under an adaptive schedule using the same intensity channel, equal-intensity signals have identical transcript laws by induction. Additional physically realizable contrast settings may refine fibres; that is a different, explicitly enlarged experiment.

## 6. Concrete unresolved structural estimate

For the selected growing binary cyclic family, the missing ingredient is quantitative geometry linking orbit-Hamming separation, homometric-fibre radius and square-root Fourier-intensity separation. One auditable intermediate quantity is

L_N(t)=max_{c∈C_N} sum_{d∈C_N,d≠c} exp[−t h²(c,d)].

Controlling L_N(B/2) yields a uniform, though possibly crude, excess-risk upper bound. Merely naming L_N or Δ_N is not progress. A useful structural result must bound their N/composition dependence without enumerating 2^N signals, and preferably replace full-fibre classification by loss-sensitive neighbourhood geometry. Matching lower bounds require separated orbit-Hamming packings or least-favourable mixtures with close Poisson laws, while accounting for the existing ambiguity floor. A small Δ_N alone does not force large reconstruction excess risk when the relevant targets are close or already covered by the same robust action.

Focused exploratory goal: establish or refute a useful uniform loss-sensitive separation/packing estimate for the declared cyclic binary family, with explicit N and composition dependence; determine whether it gives matching budget-dependent risk beyond the classical fixed-N baseline. First compute the meaning of the floor and determine the needed geometry. Do not presuppose that risk decomposes sharply as a universal floor plus a single exponential or power law. Product grids require a separate combinatorial extension; the finite-experiment formulas above already hold for any finite abelian group, but useful uniform Fourier geometry does not follow from that fact.

## 7. Attribution and source boundaries

The statistical identities and proofs above are classical finite-decision/likelihood arguments written explicitly for audit. No novelty is claimed.

- Bin Yu, *Assouad, Fano, and Le Cam* (1997), authoritative treatment of minimax testing reductions: https://doi.org/10.1007/978-1-4612-1880-7_29 . Publisher abstract and bibliographic record checked; the chapter's full text was not accessible in this review. The exact two-point formula above is independently derived rather than attributed to a numbered theorem there.
- Lucien Birgé, *Model selection for Poisson processes* (2007; preprint2006), develops Hellinger-distance testing and nonasymptotic Poisson model selection: https://arxiv.org/abs/math/0609549 . Primary abstract checked; this is methodological prior, not a claim that it proves the particular Fourier structural estimate.
- Elser–Eisebitt, *Uniqueness transition in noisy phase retrieval* (2011), Fourier–Poisson binary magnetic-imaging model and typical-case fidelity analysis: https://arxiv.org/html/1009.4693v1 . Its photon normalization agrees with B=μN; its single-flip/average-case results are not the proposed worst-case uniform estimate.
- Bendory–Edidin–Gonzalez, *Finite Alphabet Phase Retrieval* (2023), homometric partition structure and explicit noisy information-limit question: https://arxiv.org/html/2301.10647v2#S6.SS2 .
- Huang–Li–Needell (2025), Poisson minimax rates under independent sub-Gaussian sensing assumptions, not fixed Fourier rows: https://arxiv.org/html/2510.00551v1#S2 .

G6 confidence fibres and G7 design can organize the subsequent transfer contract; they do not supply the missing Fourier/Hamming geometry or stochastic minimax theorem.

## 8. Correction/addition: an elementary uniform polynomial budget bound

The generic fixed-N result can already be made uniform in N by integer autocorrelation geometry. This is another classical baseline, not the desired sharp structural result.

For any finite abelian grid G of size N, let A_x(l)=sum_{i∈G} x_i x_{i+l}, and let DFT denote the unnormalized group Fourier transform. Wiener–Khinchin gives |DFT x(k)|²=DFT A_x(k) (with consistent conjugation convention). Thus p_x=DFT A_x/N², and Parseval gives

sum_k |p_x(k)−p_y(k)|² = N^−3 sum_l |A_x(l)−A_y(l)|².

For binary signals, a shift preserves the number of + spins. The number of mismatch positions between x and its shift is therefore even, say 2m_l. Hence A_x(l)=N−4m_l. Every difference A_x(l)−A_y(l) is divisible by 4. Distinct intensity fibres have distinct autocorrelation vectors, so at least one such difference is nonzero and

||p_x−p_y||²₂ ≥ 16/N³.

For probabilities p_k,q_k≤1,

(sqrt(p_k)−sqrt(q_k))² = (p_k−q_k)²/(sqrt(p_k)+sqrt(q_k))² ≥ (p_k−q_k)²/4,

with both-zero coordinates interpreted directly. Therefore distinct binary intensity fibres satisfy h²(p_x,p_y)≥4/N³. There are at most 2^N fibres, so the previous ML procedure yields

0 ≤ R_B−R_inf ≤ min{1, (M−1)e^(−2B/N³)} ≤ min{1, 2^N e^(−2B/N³)}.

For 0<δ<1, B≥(N³/2)[N log2+log(1/δ)] suffices for excess risk at most δ. Equivalently μ=B/N can be O(N³+N² log(1/δ)). If M=1 the excess is identically zero. The argument applies to arbitrary binary subclasses X and finite abelian grids, not just one-dimensional cycles, under the full Fourier detector/no-background normalization fixed above.

This improves the stopping baseline: neither existence of a uniform polynomial photon budget nor a fixed-N asymptotic floor is an open achievement for the proposed model. The meaningful remaining target is substantially sharper, loss-sensitive and preferably matching photon-budget scaling, including the asymptotics of the ambiguity floor, with computational complexity treated separately. The 2^N catalogue search is not an efficient algorithm. No comparable lower bound of order N⁴ follows from this calculation; it is likely very loose, and may be uninformative when the floor already dominates.


## Navigation
[All individual connection dossiers](https://docs.google.com/document/d/1ZkjK2vhPFKr0C83eyvizK7xdZgdaWKXkNx4Nt_WXuBo/edit)
[GitHub reading copy](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-15-connection-dossiers/fourier-poisson-recovery.md)

[Readable Google document](https://docs.google.com/document/d/1w3TSksxQgVJ6nqD5W1YSov4pd-wovWl0bh9cZiTnaas/edit)
