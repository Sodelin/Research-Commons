# Gibbs certification: admitted classical lower bounds and a one-local calibration
Date: 2026-10-16. Attributed research checkpoint prepared by dot for Nolan.

Status: source-checked prior plus complete hand derivations below. No novelty claim, Lean verification, numerical experiment, or general P1 closure.

## 1. Frozen task
Let H = sum_P h_P P on n qubits, with nonidentity Pauli strings of weight at most k and |h_P| <= 1; the identity coefficient is fixed to zero. There is no supplied interaction graph, bounded-degree, or geometric promise. Both unknown states are Gibbs states exp(-beta H)/Tr exp(-beta H), at the same known beta > 0. Test equality against full trace norm at least epsilon, with error at most delta on each promised case.

The upper-bound measurement model here allows a chosen POVM on each fresh n-qubit copy, with classical adaptation but no retained quantum system across copies. Copies from either source count toward the TOTAL budget. The lower bounds below hold even with collective quantum measurements on all available copies. They use no preparation oracle, purification, coherent access, or dynamics.

This non-tolerant task is a specialization of the tolerant certification problem in [Bluhm et al., Theorem 17](https://arxiv.org/html/2603.29809v1). Their stated Pauli-measurement upper bound is O(beta^2 n^(2k) 3^k k log(n/delta)/epsilon^4), up to the constant rescaling of their far threshold 2 epsilon. Their theorem also covers two unknown states. We retain its n,k,beta dependence; it is not asserted optimal.

## 2. The relevant prior floor for every k >= 2
[Canonne, Diakonikolas, Kane and Stewart, Testing Bayesian Networks, COLT 2017, Theorem 57 and Section 8.1](https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf) prove an Omega(n/epsilon^2) uniformity-testing lower bound in L1, using a random unknown perfect matching and random edge signs. This is stronger here than the product-field Omega(sqrt(n)/epsilon^2) calibration. Their construction's explicit density (p. 42 in printed numbering) is the reference for normalization, rather than its covariance terminology.

Here is the exact Gibbs embedding, our source-admission calculation. For even n, matching M and signs s_e, set
  H_(M,s) = -atanh(t)/beta * sum_(e={i,j} in M) s_e Z_i Z_j.
The edge operators commute and act on disjoint pairs. Thus the computational-basis density relative to uniform is exactly
  P_(M,s)(x)/U(x) = product_(e={i,j} in M) (1 + t s_e x_i x_j),
where x_i is +/-1. The partition function is 2^n cosh(atanh(t))^(n/2). In the cited construction t = 2 eta/sqrt(n), where eta is its separation-scale parameter. After universal constant rescaling to our epsilon, t = C epsilon/sqrt(n). Admission to our coefficient cube is precisely atanh(t) <= beta.

Consequently there are universal positive constants C,c,epsilon_0 such that, in the small-epsilon regime with C epsilon/sqrt(n) < 1 and beta >= atanh(C epsilon/sqrt(n)), the cited family gives the Omega(n/epsilon^2) constant-error lower bound in our class for every k >= 2. Constants are inherited, not newly optimized. Odd n can be handled by an untouched uniform qubit. The matching is UNKNOWN. Every instance has degree one, but revealing its matching changes the testing problem; the bound must not be advertised for a supplied matching.

### Why the classical bound survives every quantum measurement
Every state in this family is diagonal in the same known computational basis. On N copies, any POVM {E_y} has outcome law
  Pr(y) = sum_x P^(tensor N)(x) <x|E_y|x>.
The diagonal entries form a stochastic kernel independent of the unknown matching and signs. Thus N full classical bitstring samples simulate the entire collective POVM exactly. Adaptive measurements are also covered: their total outcome law is a POVM, or can be simulated sequentially with the same basis samples.

The two-unknown-state problem includes the subclass whose second state is the fixed maximally mixed state. Its samples can be generated freely and independently. A total-budget-N test can therefore be simulated with at most N samples from the hard first source and independent uniform second-source samples, even if source choices are adaptive. This transfers the cited classical lower bound with the TOTAL-copy convention above.

No optimal confidence dependence is imported. The theorem is used at error 1/3. This is an attributed prior lower bound, not a new field result.

## 3. Complete k = 1 standard-method calibration
This section records a bounded-spectrum product calculation for later checks. It does not replace the general task.

Assume 0 < epsilon <= 1/16. Write the two product states using Bloch vectors r_i,s_i. Since each local Hamiltonian's three Pauli coefficients have magnitude at most one, |r_i|,|s_i| <= R = tanh(sqrt(3) beta). Let D = sum_i |r_i-s_i|^2 and a = (1-R^2) epsilon^2.

For squared qubit fidelity f_i,
  1-f_i = |(r_i,sqrt(1-|r_i|^2))-(s_i,sqrt(1-|s_i|^2))|^2/4
        <= |r_i-s_i|^2/[4(1-R^2)].
Indeed the differential norm of r -> (r,sqrt(1-|r|^2)) on the convex radius-R ball is at most 1/sqrt(1-R^2). Product fidelity and the trace-distance/fidelity inequality give
  ||rho-sigma||_1^2 <= 4(1-product_i f_i) <= D/(1-R^2).
The far case therefore implies D >= a.

For each of the three Pauli axes, each source, and each of two independent batches, measure that axis at all n sites of m fresh copies. This uses 12m TOTAL copies, 6m per source. Let D_ij^(b) be the difference of the two empirical means, with mean Delta_ij and variance v_b <= 2/m. Define U = sum_ij D_ij^(1) D_ij^(2). Product structure and disjoint batches/axis allocations make the coordinate terms independent. Hence
  E U = D,
  Var U <= 12n/m^2 + 4D/m,
using Var(XY)=Var(X)Var(Y)+Var(X)(EY)^2+Var(Y)(EX)^2 for independent X,Y.

Choose m=ceil(100 sqrt(n)/a), and reject equality when U >= a/2. Under equality Chebyshev gives error at most 48/10000. Under D >= a the error is at most
  48n/(m^2 D^2) + 16/(mD) <= 0.0048 + 0.16 < 1/3.
Thus O(cosh^2(sqrt(3) beta) sqrt(n)/epsilon^2) total copies suffice at constant error. Independent repetition and majority give a factor O(log(1/delta)); no sharp beta or delta dependence is claimed.

### Explicit lower-mixture calculation
Put b=4 epsilon <= 1/4 and t=b/sqrt(n). For theta in {+/-1}^n let
  P_theta(x)=2^(-n) product_i(1+t theta_i x_i).
This is the Gibbs state of H_theta = -atanh(t)/beta sum_i theta_i Z_i, admitted when beta >= atanh(t). The null is uniform.

To verify full L1 separation, under uniform X write L_theta-1=t S+W, with S=sum_i theta_i X_i and W the Fourier terms of degree at least two. Orthogonality gives
  E W^2=(1+t^2)^n-1-nt^2 <= exp(b^2)-1-b^2 <= b^4.
Also ES^2=n and ES^4<=3n^2; Holder interpolation yields E|S| >= sqrt(n/3). Therefore
  ||P_theta-U||_1 >= b/sqrt(3)-b^2 >= b(1/sqrt(3)-1/4) > epsilon.

For N copies, draw theta ONCE and keep it fixed across copies, and let Q_N=E_theta P_theta^(tensor N). Exact expansion yields
  1+chi^2(Q_N,U^(tensor N))
    = [((1+t^2)^N+(1-t^2)^N)/2]^n
    <= cosh(Nt^2)^n
    <= exp(N^2 b^4/(2n)).
If N <= sqrt(n)/(4b^2)=sqrt(n)/(64 epsilon^2), total variation is at most (1/2)sqrt(exp(1/32)-1)<1/3. A test with each error at most 1/3 would require variation at least 1/3, a contradiction. The same diagonal-state and uniform-reference simulation from Section 2 applies. This is an Omega(sqrt(n)/epsilon^2) TOTAL-copy lower bound.

Together, for FIXED beta>0 and the feasible epsilon,n regime beta >= atanh(4 epsilon/sqrt(n)), the k=1 constant-error rate is Theta_beta(sqrt(n)/epsilon^2). This is not a uniform-in-beta rate. At beta=0 the class is a singleton; no such lower bound applies.

### Prior attribution
Product identity and closeness testing are established topics. [Bhattacharyya et al., Testing Product Distributions: A Closer Look, ALT 2021](https://proceedings.mlr.press/v132/bhattacharyya21a/bhattacharyya21a.pdf) surveys and refines these results, including unrestricted binary-product closeness rates. The calculation above deliberately exploits fixed-beta spectral boundedness; unrestricted near-deterministic product hard instances cannot automatically be placed in that class. Its purpose is source-aware calibration, with unresolved novelty and no novelty claim.

## 4. What remains genuinely unresolved here
For general k>=2, the currently recorded source-faithful floor is Omega(n/epsilon^2), while the cited generic upper bound has n^(2k)/epsilon^4 dependence and temperature factors. This checkpoint does not establish matching n,k,beta,delta dependence or improve a general upper bound.

A dense random k-local family must remain a genuine Gibbs exponential. Replacing it by the apparently convenient linear density 1+t sum_S theta_S chi_S is unsafe: positivity can fail, and its logarithm generally produces higher-locality terms. For a valid exponential family, a lower-mixture argument needs partition-function and overlap control. Unknown disjoint k-hyperedge families retain exact factorization, but a fixed partition only supplies a product-type lower bound; an unknown partition requires its own overlap argument. Noncommuting constructions additionally require control of actual measurement laws, not just agreement of selected local expectations.

No biological G6 finite-source theorem is asserted to close these statistical or quantum-source obligations. The prior G6 interface audit remains a conditional confidence-construction interface, not an optimal testing theorem.
