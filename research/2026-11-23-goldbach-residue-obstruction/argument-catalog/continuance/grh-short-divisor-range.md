# Dirichlet GRH widens the short-divisor range in the direct Goldbach sum

Hand deduction from the [first-moment expansion](three-proof-attacks.md), with Dirichlet GRH as an external analytic input; not a Lean check or a proof of Goldbach.

Use H=√N, L=log N and the same strict support, with upper intermediate-prime boundary Z=exp(L^β), fixed β<1. For a fixed q let f(h)=μ(h) 1_(h,q)=1 z^k(h), |z|=1, and write f=μ*g as in the prefix estimate. Uniformly in q,z the reciprocal norm Σ|g(e)|e^(−1+η) is bounded by a fixed power of L at η=1/(2log Z).

By the [Baker–Harman theorem](https://doi.org/10.1112/jlms/s2-43.2.193), under Dirichlet GRH the bare additive Möbius sum up to x is O_ε(x^(3/4+ε)), uniformly in frequency. For the convolution over a prefix t≤H, split at e=√H. The short part is O_ε(H^(7/8+ε)L^C): bound (t/e)^(3/4+ε) by H^(3/4+ε)H^(1/8)/e and use the reciprocal norm (take ε<1/4). The long part is O(H L^C exp(−L^(1−β)/8)), using the trivial inner bound t/e and e^(−η)≤H^(−η/2). Constants are uniform in the prefix and frequency. Exact count extraction and logarithmic partial summation cost only powers of L.

Consequently the small-d part of the exact identity Λ(n)=Σ_{d|n} μ(d)log(n/d) is O_A(N/L^A) for every fixed A when d≤exp(L^(1−β)/32), since an individual h-progression indicator has Fourier coefficient absolute sum one. This expands the range relative to a fixed power of L but does not reach a fixed power of N. The tail d>exp(L^(1−β)/32) is not bounded by this argument. Likewise the block’s Fourier bound controls the actual prime convolution on any frequency set of measure at most exp(L^(1−β)/32)/N, but says nothing of the required sign on its complement.

GRH scope: [independent verification of the Dirichlet statements](https://math.mit.edu/~drew/grh/#what-was-verified). The final use of Baker–Harman and this extension are external hand arguments, not declarations in the checked RH package.
