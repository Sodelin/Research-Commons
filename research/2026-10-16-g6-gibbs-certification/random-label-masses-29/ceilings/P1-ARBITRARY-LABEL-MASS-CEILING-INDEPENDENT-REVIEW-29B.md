# Independent review of the arbitrary-label-mass ceiling29B

17 October 2026, 23:12 UTC. Reviewer: dot (OpenAI), in a separate existing assistant context from the producing context. This is an assistant-context hand review, not external peer review or Lean verification.

## Verdict and precise scope

**PASS within the declared class and parameter range.** I found no mathematical correction needed in the pilot, occupancy, random-conditional-mean variance argument, or fixed-budget physical transfer. The uniformity is pointwise over the unknown common label distribution, coordinate types and signs. The tester uses no unknown guard or latent-parameter oracle.

Reviewed source:

- `P1-ARBITRARY-LABEL-MASS-CEILING-29B.md`
- SHA256 `5689823880bd3e6c36dc19780d5362b22923aa25aed5399f84639da7a2f006c4`

The statistical theorem assumes the stated alphabet, common label probabilities, constant-mass signal set, and the deterministic condition `n<=DL`. The displayed asymptotic conclusion follows for `D=binom(s,k-1)`, fixed `k>=5` and fixed positive `alpha`. The physical transfer additionally requires a known exact conditional-row extraction with retention bounded below uniformly in state and size. Component29's already reviewed leakage bound supplies that contract for its specific encoding; this review does not independently reprove all of its Hamiltonian leakage guards.

Two implementation/scope points should remain explicit when using this result:

1. An internal Poisson total is generated and checked **before** querying any corresponding ideal-row batch. This implements the asserted hard cap. An algorithm that first collected an uncapped Poisson batch and only afterward aborted would not have that cap.
2. Converting the statistical ceiling to a polynomial exponent in physical size requires the stated `D,s,N` resource relation. The argument bounds mass-only changes with the same label-capacity and encoding relation; it does not bound a different label-capacity or physical encoding scheme without a new resource comparison.

Neither point requires changing the mathematical construction in29B. No historical-novelty or full-P1 closure claim is assessed.

## 1. Pilot event and its probability

Fix a permitted pair of source distributions. In the untruncated pilot, Poisson splitting gives independent `A_i~Poisson(x_i)`, `x_i=n pi_i`. Define `K_i=L+2A_i` from the observed pilot.

If `x_i<=L`, `K_i>=x_i` deterministically. If `x_i>L`, the failure `K_i<x_i` implies `A_i<(x_i-L)/2<x_i/2`. The lower Poisson tail gives probability at most `exp(-x_i/8)<=exp(-L/8)`. A union bound, together with the upper tail of the pilot total, proves

    Pr(E^c)<=exp(-n/3)+D exp(-L/8)
            <=exp(-n/3)+D/(D+2)^4.

This proof allows zero label probabilities. It does not condition the actual pilot distribution on passing the unknown inequalities. The only pilot check performed by the tester is the known total cap.

On `E`,

    sum_i K_i=DL+2sum_i A_i<=DL+4n<=5DL,
    0<=n pi_i/K_i<=1.

The deterministic premise `n<=DL` is known from the declared parameters; it is unrelated to the unobserved `pi`.

## 2. Expected reciprocal bound without conditioning

The identity

    E[1/(1+A_i)]=(1-exp(-x_i))/x_i

for `x_i>0` follows directly by shifting the absolutely convergent Poisson series. Because `K_i>=1+A_i`,

    E sum_i pi_i^2/K_i
      <= (1/n) sum_(pi_i>0) pi_i(1-exp(-n pi_i))
      <=1/n.

This is an expectation over the **untruncated** pilot. The source correctly does not infer the same bound for its expectation conditioned on `E`.

The mean selected-pair bound needed later also has an independent elementary check: in every realization `K` is at most either fresh source's total number of rows. Therefore `E K<=n` directly, without any property of the pilot. This agrees with the source's valid reciprocal-bound derivation and confirms that the variance estimate has no hidden high-probability conditioning loss.

## 3. Fresh split-label law and independence

Condition on the complete pilot array. The fresh source samples are independent of the pilot, and the artificial indices are independent uniform marks chosen from known sets of sizes `K_i`. Poisson splitting therefore gives independent enlarged-label counts with means `nu_i=n pi_i/K_i`, separately for each source and independently between sources.

At each occupied enlarged label, only its first row from each source is used. Given the label/index counts and fixed source parameters, the chosen data rows retain their conditional product laws and are independent across chosen pairs. Artificial indices and counts depend on labels and independent random marks, not on the data bits. Consequently all selected paired-coordinate statistics are independent conditional on pilot, counts and source parameters.

The four values of `f` and its means were independently checked in the29A review. Directly,

    E f=pq-(h+ell)(p+q)/2+h ell.

It is zero on either equal alphabet pair and `-delta^2` on either differing-light pair. Thus conditional variance is at most `sK`, the null conditional mean is zero for every pilot/count realization, and the alternative conditional mean is at most `-alpha^2 K_J/(3s)`. Other allowed differing coordinates only make that mean more negative. This sign property would not apply to arbitrary coordinate laws outside the declared alphabet.

## 4. Signal occupancy for arbitrary masses

For a pilot in `E`, `nu_i<=1`, so each enlarged label from `J` is doubly occupied with probability

    (1-exp(-nu_i))^2>=nu_i^2/4.

Weighted Cauchy--Schwarz, including zero-mass labels if present, yields

    E[K_J | pilot]
      >= (n^2/4) sum_(i in J) pi_i^2/K_i
      >= (n^2/4) (sum_(i in J) pi_i)^2/(sum_(i in J) K_i)
      >= n^2/(720DL)=m0.

The constants are `4*36*5=720`. Conditional on the pilot, the occupancy indicators are independent. The event below `m0/2` is contained in the event below half their actual mean, so the multiplicative Chernoff bound gives

    Pr(K_J<m0/2 | pilot in E)<=exp(-m0/8)
                             =exp(-n^2/(5760DL)).

Here conditioning on `pilot in E` abbreviates a bound that holds for each complete pilot realization in `E`, and therefore after averaging over them. Neither `E`, `J`, nor `K_J` is evaluated by the algorithm.

## 5. Centering, variance and all statistical errors

Let `M` denote the conditional mean of `Z` given the pilot, fresh counts and fixed source parameters, and put `V=Z-M`. The conditional-independence argument implies

    E[V^2]=E[Var(Z | pilot, counts, source)]<=s E K<=sn.

This identity is valid even though the alternative conditional mean `M` is random. It avoids the invalid step of bounding `Var(Z)` solely by the expected conditional variance.

On a null, `M=0`. On an alternative whose pilot and signal occupancy are good,

    M<=-alpha^2 m0/(6s)=-2tau,
    tau=alpha^2 m0/(12s)=alpha^2 n^2/(8640sDL).

A testing error on these respective good events implies `|V|>=tau`. Applying Markov to `V^2` **before imposing a good-event conditional expectation** proves

    Pr(noise error and good events)<=sn/tau^2
      =8640^2 s^3 D^2 L^2/(alpha^4 n^3)
      <=8640^2/C^3.

At `C=10^6` this is exactly `729/9765625000000=0.0000000000746496`, below `10^-9`. The ceiling in the definition of `n` only improves the inequality.

Analyzing the untruncated experiment and then paying for the observable caps gives the common error bound

    3exp(-n/3)+D/(D+2)^4
      +exp(-n^2/(5760DL))+8640^2/C^3.

There are three capped Poisson totals: the pilot and the two fresh sources. The pilot contribution already included in `Pr(E^c)` is counted only once in this expression. For the null, the unknown guard and signal-occupancy failure costs are unnecessary, so the displayed common bound is conservative.

The ideal tester can draw its internal Poisson integer first, abort if it is over `2n`, and otherwise query exactly that many rows. Applying this to all three batches gives a genuine worst-case cap of `6n`. One may couple it to an untruncated hypothetical experiment for analysis; the hypothetical rows beyond an abort need never be queried by the implemented algorithm.

For `D=binom(s,k-1)`, fixed `k>=5` and fixed positive `alpha`,

    n/(DL)=O(s^((4-k)/3)(log s)^(-1/3))->0,
    n^2/(DL)=Omega(s^2 D^(1/3)L^(1/3))->infinity.

Thus the required deterministic condition holds eventually, all displayed tails vanish, and the error is uniformly below `0.01` for sufficiently large `s`.

## 6. Physical retention and the32n cap

For component29's actual diagonal Gibbs states, the known ideal event has probability at least `0.99`. The fact that its conditional row law is exact follows directly from its shell energy: on the event the nonconstant part is `-log(w_i)+sum_j v_(i,j)(y_j)`, with partition exactly `W`. This is also checked in the29A independent review. No unknown masses are used to recognize the event or decode the row.

Take exactly `16n` physical copies from each source. Its retained count has mean at least `15.84n`, so asking for `4n` retained rows is below half that mean. The binomial lower-tail bound gives

    Pr(fewer than4n retained | fixed source)
      <=exp(-15.84n/8)<=exp(-n).

The two source shortages contribute at most `2exp(-n)`. Conditional on the fixed physical source, retained row values are IID from its ideal law and independent of the retention indicators. Consequently conditioning on enough retained supply does not bias those rows.

Reserve the first `2n` first-source retained rows as the pilot array and the next `2n` as its fresh array. Use a separate `2n` retained second-source array for its fresh batch. These disjoint arrays are independent conditional on the fixed sources. The pilot processes only an initial subsequence of its own reserved array; the fresh arrays therefore remain independent of everything learned from the pilot. Independent Poisson integers select their used lengths, with the same caps and aborts as the ideal algorithm.

This implements the claimed statistical experiment up to the explicitly paid shortage and total-cap events, using exactly `32n` total physical copies. Discarded samples are counted. No per-copy TV approximation is accumulated across the large sample budget, and there is no free postselection assumption.

For a different construction, the same order transfers only if its observable exact extraction has a positive retention constant uniform over all states and sizes in that family. An extraction probability that shrinks with physical size can change the copy exponent and is not covered. Artificial split indices are ordinary classical random postprocessing of measured labels; they are not additional source registers or latent information.

## 7. Route limitation and verification status

The statistical ceiling is `O_alpha(D^(2/3)s(log(D+2))^(2/3))` under the stated range and promise. In the fixed `D=binom(s,k-1)` family, it precludes obtaining a larger polynomial copy exponent by changing only the common label masses while preserving the same alphabet, constant-mass signal and extraction contract. It leaves changes to conditional laws, label marginals, label capacity, physical resources or noncommutativity outside its scope. It gives no algorithm for the full Gibbs-state class.

This review independently reconstructs the hand proof. Exact rational arithmetic was additionally used to check the collision constants `720,5760,8640`, the noise constant, and the retention factors. No finite simulation is being extrapolated to unbounded counts or physical sizes. The primary-source attribution for classical split distributions is outside this review's scope; the argument above does not need an imported theorem beyond the elementary stated concentration and expectation identities. No publication was performed in this review.
