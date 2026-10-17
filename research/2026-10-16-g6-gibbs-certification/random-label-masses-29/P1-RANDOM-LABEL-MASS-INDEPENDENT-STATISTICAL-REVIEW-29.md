# Candidate29: independent statistical hand review

17 October 2026, 23:00 UTC. Reviewer: dot (OpenAI), in a separate existing assistant context from the producing context. This is an assistant-context hand review, not external peer review or Lean verification.

## Verdict and scope

**PASS for the statistical argument in sections2–5 and9, conditional on the stated physical-encoding guarantees.** I found no error in the full-row likelihood bound, shared random mass normalization, conditioning of the far alternative, or worst-case total-copy reduction. The proof retains all complete rows and their shared counts. The random normalization is never replaced by its mean.

Reviewed source:

- `P1-RANDOM-LABEL-MASS-CANDIDATE-29.md`
- SHA256 `40038740c2e6e3cddd8b50f6f67b3078ddcc8d82415727fd0ea72783c7599bbd`

Sections6–8, the clone/reservoir Hamiltonian, coefficient collisions, leakage guards and physical size envelope are outside this review's independent verification scope. The statistical-to-physical reduction below assumes their asserted uniform TV approximation, exact equality for null draws and resource bound. No prior accepted component is used as a substitute for the likelihood proof. Historical novelty and optimality are not assessed. The original general P1 gap remains open.

## 1. Actual observation law and normalization

Write `C_lambda(a,b)=exp(-2lambda)lambda^(a+b)/(a!b!)`. At one label, the latent mass type is common to both sources and to all data coordinates. Conditional on that type, the two counts are independent Poisson variables with their common raw mean. The coordinates share these counts; they do not have independent clocks.

For fixed counts `(a,b)`, let `L0` be the null prior-averaged one-coordinate law, and `L1` the signal-label alternative one-coordinate law. Independence of the latent coordinate types and signs gives `L0^tensor s` and `L1^tensor s`, respectively. This independence is only used **conditional on the shared counts and the mass type**. Integrating the mass type afterward yields precisely

    N = [mu C_1 + (1-mu) C_mu] L0^tensor s,
    A = mu C_1 L0^tensor s + (1-mu) C_mu L1^tensor s.

Across labels, all latent draws and Poisson clocks are independent before conditioning on the far event. Thus the full unconditioned experiment is a product of these label experiments.

For a fixed complete latent draw, `W=sum_S w_S`. Independent Poisson counts can be generated equivalently by a source total `M~Poisson(W)` and then `M` IID labels of probabilities `w_S/W`, with the corresponding independent conditional data rows. Ordering rows uniformly conditional on the counts supplies exactly this latter description. This equivalence is parameter-independent in the direction used by the simulator: it just randomly orders the observed rows. In particular:

- Both total counts are observed and can reveal information about `W`.
- Conditional on the latent draw, each source's total is independent of its ordered IID row values.
- `W>=B=Dmu` for every draw, without any concentration argument.
- The product-over-labels chi-square calculation includes the information carried by the totals.

The equal unconditioned distributions of `W` under the two hypotheses are not, by themselves, the indistinguishability proof. The joint mixture calculation below is the needed proof.

## 2. Independent derivation of the coordinate and full-row bounds

Use the product Bernoulli(`h=1/2`) law as reference. For each observed bit put `u(1)=2`, `u(0)=-2`. Products indexed by different subsets are orthogonal, and the squared norm of a product on `j` indices is `v^(-j)`, where `v=1/4`.

Let `z=ell-h` and let `tau_i` distinguish the two sources. The light-component likelihood ratio at perturbation `t` is

    L(t)=product_i [1+(z+tau_i t)u_i].

The coefficient on a `j`-element subset in
`(L(delta)+L(-delta))/2-L(0)` has absolute value at most

    (delta^2/2) j(j-1) (|z|+delta)^(j-2).

This follows from the second derivative remainder of the degree-`j` product; it makes no assumption about the allocation of observations between sources. The null density is `(1+L(0))/2>=1/2`, and the alternative-minus-null density is one half the displayed remainder. Consequently

    d <= delta^4/(8v^2)
         sum_{j=2}^n binom(n,j) [j(j-1)]^2 x^(j-2),
    x=(|z|+delta)^2/v<=1.

Here `|z|+delta=1/2-(1-alpha)/s<=1/2`. The identity
`[j(j-1)]^2=(j)_4+4(j)_3+2(j)_2` gives the first expression in(6). Alternatively, bounding each summand's polynomial by `n^2(n-1)^2` and `x^(j-2)<=1` gives directly

    d <= 2 delta^4 n^2(n-1)^2 2^n.

For `n=0,1` the symmetric perturbation is exactly zero, so `d=0`.

For the second bound use the product Bernoulli(`ell`) law `L` as reference and let `M` be the mean of its two opposite perturbations. Since `L0>=L/2` and `L1-L0=(M-L)/2`,

    d <= (1/2) chi2(M||L)
      <= (1/2) [(1+y)^n-1],
    y=delta^2/[ell(1-ell)]=alpha^2/(s-1).

The last inequality is convexity in the first distribution; either sign-perturbed product has the displayed chi-square independently of `(a,b)`.

The complete shared-count row law has exactly

    Ddata=(1+d)^s-1 <= s d (1+d)^(s-1).

The second coordinate bound gives
`(1+d)^(s-1)<=(1+y)^(n(s-1))<=exp(n alpha^2)`. Applying the first bound only once therefore proves

    Ddata <= 2 alpha^4/s^3 * n^2(n-1)^2 3^n,

because `2exp(alpha^2)<=2exp(1/4)<3`. This last exponential factor is essential. No step sums the coordinate chi-squares while dropping the remaining tensor-product factors.

## 3. Shared mass denominator and unbounded counts

The joint count/data densities above give the exact expression

    chi2(A||N)
      = sum_(a,b) [(1-mu)^2 C_mu(a,b)^2
          / (mu C_1(a,b)+(1-mu)C_mu(a,b))] Ddata(a,b).

All denominators are positive. Dropping the factor `(1-mu)^2<=1` and retaining the heavy-count contribution in the denominator yields

    chi2(A||N)
      <= exp(2-4mu+2mu^2)/mu
          E_(a,b IID Pois(mu^2)) Ddata(a,b),

since `C_mu^2/C_1=exp(2-4mu+2mu^2) C_(mu^2)` pointwise. The auxiliary mean `mu^2` is an algebraic likelihood-ratio identity, not a change to the observation experiment.

For `n~Poisson(2mu^2)`, differentiating its probability-generating function gives

    E[(n)_j 3^n]=(6mu^2)^j exp(4mu^2).

Every summand is nonnegative, so the generating-function evaluation also justifies the complete infinite sum. Combining it with the full-row bound proves

    chi2(A||N)
      <= [2alpha^4/(s^3 mu)] exp(2-4mu+6mu^2)
          [1296mu^8+864mu^6+72mu^4]
      <= 4096 alpha^4 mu^3/s^3.

For `0<mu<=1/4`, the bracket after factoring `mu^4` is at most
`2097/16<132`, and `-4mu+6mu^2<=0`. The remaining constant is smaller than `2*132*e^2<4096` (even `e<3` suffices for this last comparison).

Product tensorization across all `D` labels now gives

    chi2(full alternative||full null)
      <= exp(4096 D alpha^4 mu^3/s^3)-1
       = exp(10^-6)-1 < 2*10^-6.

The equality uses exactly `4096/1600^3=10^-6`. Thus TV is below `0.001`, with convention `TV=(1/2)||P-Q||_1`. These bounds are uniform over **all** counts, including rare large counts. The bounded checker accompanying this review is not needed to extend this hand argument to those counts.

## 4. Farness and conditioning

The number of light coordinates at a label is `Binomial(s,1/2)`, and the heavy-mass count is `Binomial(D,mu)` of mean `B`. Union/Hoeffding and the multiplicative Chernoff bound give

    Pr(F^c) <= D exp(-s/18)+exp(-B/3)=zeta_s.

At a signal label retained by `F`, at least `s/6` light coordinates share one sign. Choose such a group of size `j`. Its all-zero event probability gap is

    (1-ell+delta)^j-(1-ell-delta)^j
      >= 2j delta (1-ell-delta)^(j-1)
      >= (alpha/3) exp(-3).

The first inequality follows by integrating the derivative of `(1-ell+t)^j`. The second uses `s/6<=j<=s` and `ell+delta<=3/(2s)`. For instance `log(1-u)>=-u/(1-u)` proves the needed exponential bound for `s>=3`.

An event gap contributes twice its size to the full L1 lower bound. Since `(2/3)e^-3>1/48`, each such conditional product pair has L1 distance greater than `alpha/48`. The label marginals are exactly the same in the two sources for every draw, so the full L1 distance is the label-mass-weighted sum of conditional L1 distances; there is no cancellation between labels.

On `F`, `H<=2B<=D/2` and `W=B+(1-mu)H<=3B`. At least `D/2` signal labels therefore have total normalized mass at least `1/6`. Thus

    ||P-Q||_1 > alpha/288 = (16/9)epsilon.

The latent alternative prior conditioned on `F` differs in TV from the unconditioned latent prior by exactly `Pr(F^c)`. Every complete observation experiment, including its counts, is a channel of the latent prior, so its law changes by at most `zeta_s`. This pays for any conditioning-induced change in the law of `W`, in the light-coordinate counts, and in all their correlations at once. It does not require independence after conditioning. Since fixed `k` makes `D` polynomial in `s` and `B` diverges, the conditioned observation TV is below `0.01` for all sufficiently large `s`.

## 5. Worst-case total-copy reduction, conditional on encoding

Assume the physical construction supplies, uniformly for every latent draw:

1. Gibbs states at the required physical size and coefficient/locality bounds;
2. exact equality of the two states on null draws;
3. TV at most `eta=1/(100B)` from the respective encoded ideal row laws;
4. ideal-to-physical encoding by a deterministic basis map known without the latent parameters;
5. actual full trace distance at least `epsilon` on `F`.

The candidate's ideal farness and TV errors imply item5 if `eta<=epsilon/8`: the actual full trace norm exceeds `(16/9)epsilon-4eta>=23epsilon/18`.

Let a proposed tester use at most `T=floor(B/4)` total copies, including adaptive source choices and arbitrary quantum processing of the supplied copies. The Poisson experiment can first uniformly order each source's rows and reserve its first `T` rows. Given the latent draw, each source count has mean `W>=B`. The standard lower Poisson tail at a fraction `1/4` of the mean gives

    Pr(either source has fewer than T rows | latent)
      <= 2 exp(-9B/32).

Conditional on the latent draw, row values are independent of the totals. Consequently conditioning on sufficient supply does not bias those rows for that draw. It can bias the *latent* law, but no equality of that conditional latent law is used: the shortage probability is uniformly bounded, and the tester's promise guarantee is pointwise in the draw.

Having `T` rows ready from **each** source permits simulation of every possible adaptive allocation of the tester's `T` total-copy budget. This is just a simulation resource; it does not reinterpret the tester's budget as `T` copies per source. The simulator prepares the corresponding basis states and runs the tester. The classical-to-quantum simulation is valid for a diagonal subclass even for collective measurements, since it prepares exactly the mixed input state conditional on each latent draw.

TV between the two ideal `T`-slot arrays and their physical counterparts is at most `2Teta`, by product coupling (equivalently trace-distance tensor telescoping). Composing with the tester cannot increase the acceptance-probability difference. Paying this separately on each hypothesis, and the shortage event separately on each, gives an observable acceptance gap at least

    1/3 - 4Teta - 4exp(-9B/32).

Here `4Teta<=1/100`. The gap is eventually greater than `0.3`, contradicting observation TV below `0.01`. This is a worst-case copy-cap conclusion, not merely an expected-budget statement. It remains valid for the far prior conditioned on `F`, because all approximation and supply bounds are uniform in the latent draw.

Thus the statistical construction supplies `Omega(B)` once the physical hypotheses are checked. Algebraically,

    B = s D^(2/3)/(1600alpha^(4/3))
      = Theta_(k,epsilon)(s^((2k+1)/3)).

If the physical envelope `N_s=O(s(log s)^(1/(k-1)))` and parameter-independent spectator padding are separately established, this yields the exponent claimed in(1). This review does not independently certify that physical envelope.

## 6. Independent bounded diagnostics

Files:

- `independent_statistical_check_29.py`
- `independent_statistical_check_29.log`

The checker was written from the candidate's distributions without reading or importing the producing context's checker. It enumerates exact rational one-coordinate sufficient-statistic probabilities for `s in {10,17,32}`, `alpha in {1/2,1/4,1/16}`, `n=0,...,8`, and every source allocation `a+b=n`:405 cases. It checks both coordinate bounds and the full conditional-row bound using exact `Fraction` arithmetic. It also directly enumerates a two-coordinate joint distribution with rational mixture weights to verify the shared-mass denominator identity. The two-coordinate check is a diagnostic of the mixture algebra, not a substitute for the hand proof for `s` coordinates or the actual Poisson count law.

All checks passed. The small numerical checks of elementary exponential constants are explicitly diagnostic; the hand proof above supplies the unbounded-count and asymptotic statements. No physical Hamiltonians, finite physical sizes, external prior-work comparison, or Lean statements were verified by this checker.
