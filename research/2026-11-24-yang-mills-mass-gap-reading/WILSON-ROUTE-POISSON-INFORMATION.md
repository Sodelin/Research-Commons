# Sparse Wilson route pools: the Poisson information curve including saturation

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof for the independent conditional-Haar reference of [the Wilson route information calculation](WILSON-ROUTE-MUTUAL-INFORMATION.md). The inputs are the bare routes, not the nonlinear router or renormalized transports. No Lean verification. Uses the familiar rate–distortion variational step and [Le Cam's Poisson approximation](https://msp.org/pjm/1960/10-4/pjm-v10-n4-p11-p.pdf); no claim of novelty for the abstract information-theory argument.

Let the pool size M tend to infinity, let each Haar hit have probability h, and assume M h -> a in (0,infinity). For S ~ Bin(M,h) set b_M=P(S=M), r_M=P(0<S<M). Set r=1-exp(-a) and let K be Poisson(a) conditioned on being positive. Let R_M(p) denote the minimum mutual information (nats) needed to hit with probability at least p. For p=b_M+r_M alpha, uniformly over alpha in [0,1] with p>=h,
```
R_M(p) = p log M + r J_a(alpha) + o(1),
J_a(alpha) = sup_(s real) [alpha s - E log(1+exp(s) K)].
```
In particular, at the maximal feasible success p_max=1-(1-h)^M, the correction is minus E[log Z; Z>0] for Z ~ Poisson(a). The no-hit event persists with probability tending to exp(-a). Thus the dense-pool approximation from the previous note does not describe this regime, even if the selector sees the entire pool.

## Exact finite reduction and a uniform limit

Permutation averaging of channels cannot increase mutual information (convexity for fixed input) and preserves success. Equivalently, one can use the exact soft selector from the preceding note. Given S=k, give total probability q to the hits uniformly and the rest to the misses uniformly; its output marginal is uniform. For 0<k<M its conditional divergence from that marginal is
```
q log M + q log q + (1-q) log(1-q)
    - q log(k/(1-k/M)) - log(1-k/M).
```
At S=0 or S=M the conditional divergence may be zero and success is forced to zero or one respectively. Thus the optimization at exact success p subtracts the forced success b_M before assigning conditional mean alpha on 0<S<M. Minimizing the displayed binary entropy expression at that mean gives the log-sum-exp dual, with equality for q=exp(s)k/(1-k/M+exp(s)k); limits s->+/-infinity give the endpoints. For p>=h the exact and at-least-p optima coincide by convexity of the achievable optimum as a function of exact success, and its minimum zero at h. Write W_M=S/(1-S/M) conditioned on 0<S<M, and use J_M for the same formula as J_a with K replaced by W_M. The resulting exact identity is
```
R_M(p) = (p-b_M) log M
         + E[-log(1-S/M); 0<S<M] + r_M J_M(alpha).
```

The added expectation tends to zero: for S<=M/2 it is at most 2 E S/M; above M/2 it is at most log(M) P(S>M/2), which is O(log(M)/M^2) by the bounded second moment. Also b_M log M -> 0. To pass through the supremum uniformly even when the multiplier diverges, subtract max(s,0) from each logarithm. For any w>=1 the centered function is between zero and log(1+w), is 1-Lipschitz in log w uniformly in s, and extends to s=+/-infinity. Replacing W_M by S in the conditional expectations changes them uniformly by at most E[-log(1-S/M) | 0<S<M]=o(1). For S on the positive integers, truncate at a fixed k and use convergence of the individual binomial probabilities, then let k tend to infinity; the tail of log(1+S) is uniformly small by the bounded second moment. This proves uniform convergence of the centered log partitions over all s. The deterministic term alpha*s-max(s,0) is unchanged, so the same sup-norm difference bounds the difference of their convex duals, for all alpha including 0 and 1. J_a is uniformly bounded: it is at most zero, and choosing s=0 bounds it from below by -E log(1+K). This proves the claimed result.

## Cost immediately below saturation

For Z ~ Poisson(a), put A=E[1/Z; Z>0] > 0 and B=E[log Z; Z>0]. Define L(p)=r J_a(p/r). For a small deficit d=r-p>0,
```
L(r-d) = -B - d log(A/d) - d + O_a(d^2).
```
Indeed the unconditioned log partition is r s + B + A exp(-s) + O_a(exp(-2s)) as s->infinity, and its derivative is r-A exp(-s)+O_a(exp(-2s)), by expansion on Z>=1. Solving the derivative equation gives exp(-s)=d/A+O_a(d^2), yielding the formula. This is an expansion of the limiting centered curve, not a uniform joint error estimate for shrinking d as M grows.

The actual Wilson-law comparison still needs its own error control. The previous total variation bound controls fixed interior targets with a multiplier of order log M, so the variation error times log M must tend to zero to distinguish an order-one correction via that bound. This calculation does not show that a nonlinear router reaches the curve or that a physical mass survives the continuum limit.
