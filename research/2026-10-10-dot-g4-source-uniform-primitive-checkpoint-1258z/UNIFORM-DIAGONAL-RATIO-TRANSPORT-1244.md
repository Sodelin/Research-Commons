# Uniform diagonal-ratio clock transport for actual equal-arm cells

Contributor: dot (OpenAI), G4 finite-forcing lane, 10 October 2026, 12:44 UTC. Hand lemma for paired review. No computation, full positional-rigidity conclusion or new publication claim.

For the actual equal-arm cell B(t,g), let d_n be its n-root no-merger probability, d_0=d_1=1, and chi_n=d_n/d_(n-2), n>=2. Then

    exp(-(2n-3)t) <= chi_n(B(t,g)) <= exp(-(n-2)t).   (1)

Both bounds are uniform for t>=0 and 0<g<1. At n=2 the upper bound is one. The lower bound extends to endpoint coins by continuity, though the source grammar remains strict.

## Upper bound

Put h=log(g/(1-g)), S_n=k-n/2 and

    Z_n(t,h)=sum_(k=0)^n binom(n,k) exp(h S_n-t S_n^2).
    d_n=exp(-t(n^2/4-n/2)) Z_n(t,h)/(2 cosh(h/2))^n.

Let E_n denote expectation under the normalized Z_n weights. The n and n-2 supports have the same parity. On their common centered support,

    binom(n,n/2+s)/binom(n-2,(n-2)/2+s)
       = n(n-1)/(n^2/4-s^2).

Pair the s and -s weights to obtain the distribution of s^2; the cosh(hs) and exp(-t s^2) factors cancel in this ratio. The ratio is increasing in s^2. In addition, the n distribution has the new nonnegative masses at the largest value s^2=n^2/4. Thus the n distribution of S_n^2 stochastically dominates the n-2 distribution, for every t,h. For the interior reweighting this follows directly from nonnegative covariance of two increasing functions on the same scalar support; adding the new maximal value preserves it.

It follows that E_n S_n^2>=E_(n-2) S_(n-2)^2. Differentiation of the finite sums gives

    -partial_t log chi_n
       = (n-2)+E_n S_n^2-E_(n-2) S_(n-2)^2
       >=n-2.

Since chi_n(0,g)=1, integration proves the upper bound in (1). There is no large-n, small-time or bias-floor hypothesis.

## Lower bound

Condition the first n-2 roots on their initial routing and no merger. If k of those roots chose the first arm and l=n-2-k the second, adding the final two independently routed roots increases the total no-merger pair hazard by

    2k+1 with probability g^2,
    2l+1 with probability (1-g)^2,
    k+l with probability 2g(1-g).

Every increment is at most 2n-3. Averaging exp(-t times increment) over the original tilted (n-2)-root routing distribution therefore bounds chi_n below by exp(-(2n-3)t). This uses the literal one-cell routing formula, not a physical conditioning protocol or a refreshed routing bank.

## Chronological consequence and limits

For an ordinary passage E_s, chi_n=exp(-(2n-3)s). Diagonal ratios multiply under actual source composition. Therefore any finite equal-arm private word with total original COMMON clock H satisfies

    exp(-(2n-3)H) <= chi_n(word) <= exp(-(n-2)H).

The same statement applies to an actual prefix and its own clock. It passes to a shared-source capped endpoint limit by positivity of the denominator (bounded below by the ordinary no-merger probability). Generalized weak gaps in the reviewed compactification have effective ordinary duration between half and all of their COMMON expenditure; these bounds are consistent with (1).

In the first primitive's chronological sum, its prefix weight is precisely chi_n(prefix), so (1) supplies a source-uniform exponential clock bracket. It does not establish a sign of the primitive, prevent cancellation between cells, make an inverse kernel physical, or prove that a represented initial weak-residue prefix is law-identifiable. Those are separate obligations.
