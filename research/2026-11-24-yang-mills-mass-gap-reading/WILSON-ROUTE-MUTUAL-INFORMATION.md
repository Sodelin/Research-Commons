# Exact average information cost of a near-hit in the bare Wilson route pool

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction for the deterministic route pool and its conditional Haar reference. It extends the [finite-alphabet budget](WILSON-ROUTE-INFORMATION-BUDGET.md) to mutual information, allowing randomized observation and selection with unrestricted alphabets. This is a finite one-shot optimization in the spirit of [Shannon's fidelity criterion](https://gwern.net/doc/cs/algorithm/information/1959-shannon.pdf), not a result about the nonlinear router, renormalized transport, or the mass gap. No new Lean verification.

Condition on a fixed exterior value in the [conditional Haar comparison](WILSON-NEARBY-ROUTE-TOTAL-VARIATION.md). Let X be the tuple of relative transports, A_i(X) the indicator that coordinate i is within radius t, and I in {1,...,M} the selected index. Write h=h(t) for the Haar probability, p for the true success probability, and delta for the conditional total variation error against M independent Haar transports. In the Haar reference S=sum A_i has Bin(M,h) distribution. Assume 0<h<1 and use natural logarithms for information. Put
```
G(lambda) = E_Bin log(1+(exp(lambda)-1) S/M),  lambda>=0.
```

## Robust lower bound and exact solution for independent Haar

For an arbitrary randomized selection channel with marginal index law q, its mutual information is the expectation of the relative entropy of I given X against q. Tilting q by exp(lambda A_i(X)) and using nonnegativity of relative entropy gives
```
I(X;I) >= lambda p - E_P log(1+(exp(lambda)-1) sum_i q_i A_i(X)).
```
The logarithmic term lies in [0,lambda], so replacing the actual law P of X by the reference costs at most delta lambda. Under the reference its expectation as a function of q is permutation-invariant and concave. Averaging q over all permutations and using concavity shows its maximum occurs at uniform q, where it equals G(lambda). Consequently
```
I(X;I) >= sup_(lambda>=0) {lambda (p-delta) - G(lambda)}.
```
In particular this is a conditional statement at each exterior value with the same delta upper bound. If only the average p over exterior values is known, first average the displayed bound for each fixed lambda, then take the supremum. If the router uses another observation Z of the interior with independent decoding randomness given Z and the exterior, conditional data processing also bounds I(X;I | exterior) by I(X;Z | exterior).

For the product reference the expression is exact as the minimum information subject to achieving success at least p in the interval [h,1-(1-h)^M]. For the uniform-output soft selection channel
```
W(i | X) = exp(lambda A_i(X)) / (M-S(X)+exp(lambda) S(X)),
```
the marginal index law is uniform by symmetry under the reference. Thus its success is G'(lambda), and its information is lambda G'(lambda)-G(lambda). For M>=2 the success runs continuously and strictly increasingly from h to the probability of at least one hit, because S is strictly interior with positive probability. The endpoint is obtained by the limiting channel which selects uniformly among hits if they exist and uniformly among all indices otherwise; the mutual information converges since the output is finite. For M=1 the interval has only one point and the cost is zero. Success targets below h cost zero and targets above the at-least-one-hit probability are impossible.

The same soft channel on the actual Wilson law has success within delta of its reference success. Its actual mutual information is at most the expected conditional divergence against the uniform index distribution (subtract the nonnegative divergence of the actual index marginal). The conditional divergence for this channel is lambda times its conditional success minus the logarithmic partition function, and lies in [0,lambda]. Therefore its actual mutual information is at most the reference cost plus delta lambda. This statement does not assume exchangeability of the actual law.

## A small-radius consequence for a sufficiently large pool

Jensen's inequality gives G(lambda)<=log(1+(exp(lambda)-1)h). Thus achieving fixed probability p>h in the reference costs at least the binary relative entropy D(Ber(p)||Ber(h)). In the regime h->0 and Mh->infinity this lower bound is sharp up to o(1) for every fixed 0<p<1. To check the upper bound let lambda=log(1/h)+s. The normalized S/(Mh) converges to 1 in L2 (variance at most 1/(Mh)). At fixed s, the functions for G(lambda) and G'(lambda) then converge in expectation to log(1+exp(s)) and exp(s)/(1+exp(s)), respectively: the logarithm is uniformly Lipschitz in S/(Mh) for bounded s, and the ratio is bounded and continuous. Bracketing s above and below the log odds of p shows that the exact multiplier giving success p has s tending to those log odds. The logarithmic partition convergence holds uniformly for s in a fixed compact interval by the same bounds. The exact cost is therefore
```
p log(1/h) + p log p + (1-p) log(1-p) + o(1).
```
Since h(t) is asymptotic to t^3/(3 pi sqrt(2)), the leading cost is 3p log(1/t), rather than a bound that counts every possible message. The regime Mh->infinity is distinct from fixed-scale extreme-value sampling with Mh bounded. For the actual Wilson comparison the robust lower bound and soft-channel upper bound have the additional success slack delta; one should retain those bounds unless the product of delta and the relevant log scale is controlled.

This separates the information a successful bare router needs from the much stronger claim that the published geometric or nonlinear statistic actually has that information. The latter and the physical-mass bridge remain open.
