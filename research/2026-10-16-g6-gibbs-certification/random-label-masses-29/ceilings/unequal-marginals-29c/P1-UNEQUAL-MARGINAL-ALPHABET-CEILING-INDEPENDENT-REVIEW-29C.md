# Independent review of the unequal-marginal alphabet ceiling 29C

17 October 2026, 23:30 UTC. Reviewer: dot (OpenAI), in a separate assistant research context from the candidate author. This is an independent assistant-context hand review, not external peer review or a Lean certificate.

## Verdict and exact reviewed object

**PASS for the stated ideal-row statistical theorem**, including arbitrary unequal and zero label masses, the full-L1 promise, the pooled pilot, the imported marginal tester, and a worst-case cap of `804m+8n` ideal rows. No mathematical correction to that theorem was found.

Reviewed file: `P1-UNEQUAL-MARGINAL-ALPHABET-CEILING-29C.md`.

SHA256: `f4079e11dc031c41a23873b67f1232bf511993326afbbf4ced2a74dd4bb0c441`.

Two clarifications must remain explicit when applying or describing the result:

1. Choose `m = ceil(max(100, C_0 max(D^(2/3)/t^(4/3), sqrt(D)/t^2)))`, or another choice within a constant factor of this sufficient order. An arbitrary larger choice still gives a correct tester but need not obey the claimed asymptotic resource order.
2. The physical-distance transfer in Section 7 uses one **common, source-independent CPTP encoding map** for the two ideal row laws, as well as the stated approximation bounds. Exact extraction alone does not transfer a physical far-distance promise to row L1 distance. With that interpretation of the additional embedding premise, the transfer calculation is valid.

The physical wrapper has a fixed total allocation of `6432m+32n` copies, including all discarded copies. Its validity remains conditional on the exact extraction, retention, embedding, and physical-size premises; this review does not establish those premises for a new Gibbs construction.

## 1. Full L1 to overlapping signal labels

Let `d=||pi-nu||_1`, `w_i=min(pi_i,nu_i)`, and `b_i` count differing coordinates. Decomposing each label into common and excess mass yields

    ||P-Q||_1 <= d + sum_i w_i ||P_i-Q_i||_1.

A differing Bernoulli pair has full L1 distance `4delta`, not `2delta`. Product telescoping therefore gives

    ||P-Q||_1 <= d + 4delta sum_i w_i b_i.

If the full distance is at least epsilon and `d<epsilon/2`, then

    sum_i w_i b_i/s >= epsilon/(8alpha) = 2a.

For `J={i:b_i/s>=a}`, the contribution from its complement is at most `a sum_i w_i<=a`. The contribution from J is consequently at least a. Since `b_i/s<=1`, it follows that `sum_J w_i>=a`; by definition each label in J has `b_i>=as` differing coordinates. All factors agree with the candidate. J is used only in analysis.

This argument allows arbitrary and zero marginal masses. A label absent from one source has overlap weight zero. Under the exact null, equality of the full labeled laws implies `pi=nu` and equality of the conditional product laws at every positive-mass label. Taking coordinate marginals then forces equality of their coordinate parameters. Arbitrary assignments at zero-mass labels cannot affect the statistic.

## 2. Imported marginal theorem and bounded amplification

The primary source was inspected directly: Chan, Diakonikolas, Gregory Valiant and Paul Valiant, *Optimal Algorithms for Testing Closeness of Discrete Distributions*, SODA 2014. [Primary PDF](https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf); [DOI](https://doi.org/10.1137/1.9781611973402.88).

Theorem 1.1 is on PDF page 2 (printed page 1194). The Poissonization convention is on PDF page 3, and Proposition 2.1 spans PDF pages 3–4 (printed pages 1195–1196). The applicable guarantee distinguishes equality from full L1 distance at least t with success at least 2/3, using independent Poisson(m) samples from each distribution, for `m>=C_0 max(D^(2/3)/t^(4/3),sqrt(D)/t^2)`. It applies to arbitrary discrete distributions, including zeros. It requires neither tolerant testing nor conditional sampling. The absolute constants are inherited, not numerically extracted in this review.

With `t=epsilon/3` and `m>=100`, capping each of the two internal counts at `2m` adds error at most `2exp(-m/3)<1/1000` per run. Counts must be generated and checked before that run's rows are requested. A run thus succeeds with probability exceeding `1/2+4/25`; 201 independent runs have majority error at most

    exp(-2*201*(4/25)^2) < 1/100.

The cap is `201*2*2m=804m` rows in total, or `402m` per source.

If `d>=epsilon/2`, the marginal alternative guarantee applies. If `0<d<epsilon/2`, its answer need not be reliable: a rejection is already a correct full-distribution answer, while the separate conditional test handles acceptance. Under the full null, its exact-equality guarantee applies. Thus the OR combination uses no tolerant guarantee.

## 3. Pooled pilot, thinning and independence

In the untruncated coupling, `A_i=A_i^P+A_i^Q` is Poisson with mean `x_i=n(pi_i+nu_i)`. For `K_i=L+2A_i`, if `x_i<=L`, then `K_i>=x_i` automatically. Otherwise `K_i<x_i` implies `A_i<x_i/2`, which has probability at most `exp(-x_i/8)<=exp(-L/8)`. Together with the two pilot-total caps this proves the stated failure bound for E.

On E,

    sum_i K_i <= DL+8n <= 9DL,
    n pi_i/K_i <= 1,  n nu_i/K_i <= 1.

The guard E is not an oracle or a tested event. The implementation uses only the observed pilot counts.

Because `L>=1`, the unconditional reciprocal bound is

    E[1/K_i] <= E[1/(1+A_i)]
               = (1-exp(-x_i))/x_i <= 1/x_i

for positive x_i; zero-mass summands contribute zero. No conditioning on E is permissible or needed here.

Independent fresh Poisson batches, with independent random enlarged-label assignments using the common observed K_i, give independent count pairs with respective means `u_i=n pi_i/K_i` and `v_i=n nu_i/K_i`, conditional on the pilot. Conditioning additionally on all those counts leaves selected row contents independent with their correct conditional product distributions. Choosing the first row in each occupied cell does not bias its content. Each row is used once; all its s coordinates stay together.

The finite algorithm is coupled to this untruncated experiment and differs only upon a total-cap failure. Analysis of independent Poisson cell counts is performed in the untruncated experiment, rather than incorrectly asserting their independence conditional on passing a cap.

## 4. Statistic, collision bound and unconditional variance

For the candidate's f, direct evaluation gives `E f=0` on either equal alphabet pair and `E f=-delta^2` on either orientation of a differing pair. Also `|f|<=1`. Conditional independence therefore gives conditional variance at most sK. The null conditional mean is exactly zero, including the zero-mass edge cases described above. On the relevant alternatives, the conditional mean is at most `-a alpha^2 K_J/s`; contributions outside J cannot cancel this negative signal.

On E, the probability of a paired occupancy is at least `u_i v_i/4`. Consequently

    E[K_J | pilot]
      >= (n^2/4) sum_J pi_i nu_i/K_i
      >= (n^2/4) (sum_J sqrt(pi_i nu_i))^2 / sum_J K_i
      >= a^2 n^2/(36DL) = m_0.

The middle step is weighted Cauchy–Schwarz. The last uses `sqrt(pi_i nu_i)>=min(pi_i,nu_i)`, not equality of the marginals. Independent cell occupancies give

    Pr(K_J<m_0/2 | pilot in E) <= exp(-m_0/8).

For the noise, the unconditional reciprocal estimate instead yields

    E K <= n sum_i pi_i nu_i/(pi_i+nu_i) <= n/2,

where zero-over-zero terms are zero and `4pi_i nu_i<=(pi_i+nu_i)^2`. Hence, with `V=Z-E[Z|pilot,counts]`, `E V^2<=sn/2`. This controls the centered noise without dropping the variance of a random alternative conditional mean.

With `tau=a^3 alpha^2 n^2/(144sDL)`, a good alternative has conditional mean at most `-2tau`. The common noise error is at most

    sn/(2tau^2)
      = 10368 s^3 D^2 L^2/(a^6 alpha^4 n^3)
      <= 10368/C^3.

The four capped Poisson batches cost at most `4exp(-n/3)` in total failure probability and at most `8n` rows. Counting the pilot caps once, the guard failure, collision failure, noise event, and marginal error gives precisely the candidate's bound (2).

For fixed positive epsilon and alpha and `D=binom(s,k-1)`, fixed `k>=5`, `n/(DL)` tends to zero, while `a^2 n^2/(DL)` tends to infinity. The selected marginal budget has lower order than n. Thus the stated eventual feasibility and asymptotic total-row order follow. This does not assert the guard `n<=DL` for arbitrary small parameters outside that regime.

## 5. Physical caps and distance transfer

Assume the wrapper's common measurement/retention rule gives exactly the specified IID row law on success, with success probability at least .99 for each fixed source. A source-dependent success probability does not bias the retained-row law. Retained values are IID and independent of the success-pattern information; restricting to the first required retained values is legitimate.

For the conditional test, `16n` physical copies per source have expected retained count at least `15.84n`. Since the required `4n` is below half that mean, the shortage probability is at most `exp(-15.84n/8)<=exp(-n)` per source. Disjoint arrays of `2n` retained values are available for its pilot and fresh requests.

For the marginal test, use `3216m=8*(402m)` physical copies per source. The expected retained count is at least `3183.84m`; needing `402m` gives shortage probability at most `exp(-3183.84m/8)<=exp(-397m)` per source. Its 201 runs use disjoint retained arrays and independent internal randomness. These pools are separate from the conditional-stage pools.

The fixed physical cap is therefore

    2*(3216m+16n) = 6432m+32n,

with an additional error allowance `2exp(-n)+2exp(-397m)`. Every internal Poisson count is checked before consuming its requested rows; all physically collected and discarded copies count toward the cap.

For the far-distance transfer, explicitly let Gamma be a **common source-independent CPTP map** from diagonal row distributions to physical states. If

    ||rho_P-Gamma(P)||_1 <= 2eta,
    ||rho_Q-Gamma(Q)||_1 <= 2eta,

then contractivity and the triangle inequality imply

    ||P-Q||_1 >= ||Gamma(P)-Gamma(Q)||_1
              >= ||rho_P-rho_Q||_1-4eta.

Thus the claimed `epsilon_phys/2` ideal threshold follows when `eta<=epsilon_phys/8`, with the declared `epsilon<=alpha` guard. A common exact extraction rule transfers equality. Extraction alone supplies the opposite contractivity direction for distance and cannot replace the common-embedding approximation premise.

The exponent interpretation still requires the specified label capacity `D=binom(s,k-1)`, physical-size relation, and exact extraction, or independently proved replacements. It is a ceiling for this conditional alphabet and those encodings, not an upper bound for the entire noncommuting Gibbs class or a solution of P1.

## 6. Checked evidence and limits

The adjacent independent script `independent_unequal_marginal_check_29c.py` verifies the candidate SHA and enumerates 64 exact rational full-row examples, including unequal, disjoint, and zero masses. It checks the full-L1 inequality and harmonic-mass bound in every case; 24 cases also exercise the extracted overlap-signal conclusion. It independently checks the displayed constants, amplification inequality, and fixed-copy arithmetic. The saved output is `independent_unequal_marginal_check_29c.log`.

These are bounded exact diagnostics alongside the hand proof. They do not establish the imported theorem, a new physical encoding, historical novelty, or formal Lean verification. The imported theorem's stated guarantee and sampling convention were checked against its primary source; its entire proof was not independently re-proved. Candidate bytes were preserved.
