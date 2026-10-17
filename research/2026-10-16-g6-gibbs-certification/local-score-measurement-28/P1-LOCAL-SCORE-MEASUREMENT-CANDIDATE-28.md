# P1: a fixed-temperature limitation of measuring the Gibbs logarithmic difference

17 October 2026, 21:52 UTC. Author: dot (OpenAI), working with Nolan.

Status: hand-proof candidate for review. No full P1 solution, historical-novelty claim, or Lean verification. This is a limitation of one proposed measurement, not a lower bound for unrestricted Gibbs-state testing.

## 1. Exact claim and why it matters

Fix any beta>0. For every sufficiently large N there are two N-qubit, three-local Gibbs states rho and sigma at this same beta, with every nonidentity Pauli coefficient of their Hamiltonians in [-1,1], such that

    ||rho-sigma||_1 >= 1/4,

but the total variation distance between the outcome laws of the spectral projectors of

    F = log(rho)-log(sigma)

is O_beta(1/N). Every measurement whose effects are functions of F has no larger outcome distance. In contrast, measuring one specified data qubit gives a constant probability gap for this pair.

Thus the true local logarithmic difference need not itself provide a dimension-independent, bounded measurement signal, even at fixed beta. Knowing its locality does not justify replacing a measured/weighted statistical witness by an arbitrary bounded function of this score. This does not exclude choosing other local observables, choosing a richer measurement algebra, or using arbitrary collective measurements. In particular this family is easy under the actual P1 access model.

The phrase "spectral projectors" matters: a measurement that resolves additional information inside a degenerate eigenspace of F is not constrained to be a function of F. Reading the data qubit in that eigenspace is exactly how this example can be distinguished easily.

## 2. Explicit coefficient-bounded family

Use R reservoir qubits, one mediator qubit m, and one data qubit d, so N=R+2. Write

    S = sum_{i=1}^R Z_i,
    n_m = (I-Z_m)/2,    n_d = (I-Z_d)/2,
    c = beta^(-1/2),    a in {1/2,1}.

Define

    H_a = -sum_{i<j} Z_i Z_j - sum_i Z_i
          + a S n_m + (c/sqrt(R)) S X_m n_d.             (1)

Choose the integer R >= max{1,1/(4beta)}. The complete nonzero Pauli coefficients, after combining collisions, are

* Z_i Z_j: -1;
* Z_i: a/2-1;
* Z_i Z_m: -a/2;
* Z_i X_m: c/(2sqrt(R));
* Z_i X_m Z_d: -c/(2sqrt(R)).

They are real, have magnitude at most one, and have weight at most three. There is no hidden coefficient on an uncounted auxiliary spin. All N qubits are part of the supplied state. The reservoir has growing degree and per-site interaction sum; this is allowed by the original coefficientwise class and would not be admitted under a separate bounded-degree promise.

Let rho_a=exp(-beta H_a)/Z_a. Both members use the same beta, R, reservoir Hamiltonian, and mediator/data coupling. They do not commute in general. Their logarithmic difference is exactly

    log(rho_(1/2))-log(rho_1)
      = (beta/2) S n_m + log(Z_1/Z_(1/2)) I.             (2)

Hence its spectral projectors are those of the single fixed observable G=S n_m. The scalar in (2) changes eigenvalues but not projectors.

## 3. Exact sector calculation

The reservoir Z_i and data n_d commute with H_a. In a reservoir configuration with j negative spins, put s=R-2j. Relative to the all-positive reservoir energy, the reservoir penalty is

    D_j = 2j(R-j)+2j.                                   (3)

The remaining mediator/data Hamiltonian is

    h_a(s)= a s n_m + (c s/sqrt(R)) X_m n_d.

For n_d=0 its mediator matrix is diag(0,a s). For n_d=1 it is

    [[0, c s/sqrt(R)], [c s/sqrt(R), a s]].              (4)

These are the exact full blocks; no effective-Hamiltonian approximation is used.

For the all-positive reservoir s=R, the n_d=1 eigenvalues are

    lambda_-(a,R)=(aR-sqrt(a^2 R^2+4c^2 R))/2
                 = -2c^2/(a+sqrt(a^2+4c^2/R)),
    lambda_+(a,R)=(aR+sqrt(a^2 R^2+4c^2 R))/2.

In particular lambda_- tends to -c^2/a and lambda_+ >= aR. The conditional probability of data value one is exactly

    p_a^+(R) = [exp(-beta lambda_-)+exp(-beta lambda_+)] /
               [1+exp(-beta aR)+exp(-beta lambda_-)+exp(-beta lambda_+)].  (5)

Therefore, since beta c^2=1,

    p_a^+(R) -> exp(1/a)/(1+exp(1/a)).                   (6)

The mediator-one weight in the lower eigenvector of (4) at s=R is

    w_- = (1-a/sqrt(a^2+4c^2/R))/2 <= c^2/(a^2 R).

The two upper thermal contributions have energies at least aR. The conditional mediator-one probability q_a^+(R) consequently satisfies

    q_a^+(R) <= c^2/(a^2 R) + 2 exp(-beta aR).           (7)

## 4. Full finite-temperature reservoir leakage

This step controls the actual Gibbs state, not only a selected sector. The eigenvalues of h_a(1) give, for s>=0,

    min eigenvalue h_a(s) >= -c^2/a,

and for s<0,

    min eigenvalue h_a(s) >= -a|s|-c^2/a.

For example, the maximum eigenvalue of h_a(1) is at most a+c^2/(aR), by sqrt(a^2+4c^2/R)<=a+2c^2/(aR). Multiplying by a negative s gives the second inequality. Thus the four-dimensional core partition function is at most

    4 exp(beta a max{-s,0}+1/a).

The all-positive core partition function is at least one. Let b_a(R) be the total Gibbs probability of a reservoir configuration other than all-positive. Using (3) and summing all binomial multiplicities gives the uniform bound

    b_a(R) <= B_R,
    B_R = 4 exp(2) [ (1+exp(-beta R))^R-1
                    + exp(-beta R)(1+exp(-beta(R-1)))^R ].              (8)

To verify (8), for 1<=j<=R/2 use D_j>=jR and s>=0. For j>R/2 set l=R-j<R/2. Then

    D_j-a(R-2l)
       = (2-a)R+2l(R-l)+(2a-2)l
       >= R+(R-1)l,

because 1/2<=a<=1. Extend both partial binomial sums to their complete nonnegative sums. This includes the all-negative phase rather than discarding it. In particular B_R=O_beta(R exp(-beta R)) and tends to zero. If R exp(-beta(R-1))<=1, the simpler bound

    B_R <= 4 exp(3)(R+1) exp(-beta R)

also follows from (1+u)^R<=exp(Ru).

The unconditional data-one probability differs from (5) by at most B_R. This follows directly from conditioning, since all probabilities lie in [0,1].

## 5. Separation of the states and failure of the score readout

From (6) and (8), the gap in data-one probabilities tends to

    delta_* = exp(2)/(1+exp(2)) - exp(1)/(1+exp(1))
            = approximately 0.1497384993.

The full trace norm is at least twice this binary probability gap. Its limit inferior is therefore at least 2delta_*>1/4. For an elementary strict comparison, 8/3<e<11/4 gives

    delta_* > 64/73 - 11/15 = 157/1095 > 1/8.

Consequently the claimed trace separation holds for every sufficiently large R at the fixed beta.

On the all-positive reservoir sector, G=S n_m takes values zero and R. Combining (7) and (8), its unconditional probability of a nonzero outcome is at most

    q_a^+(R)+B_R <= 4/(beta R)+2exp(-beta R/2)+B_R.

Let P_(1/2),P_1 be its two outcome laws. Each is close to the point mass at zero, so

    TV(P_(1/2),P_1)
       <= 8/(beta R)+4exp(-beta R/2)+2B_R
       = O_beta(1/R).                                  (9)

Every POVM all of whose effects are functions of G is a classical post-processing of this spectral experiment, and cannot increase total variation. The same statement holds for F by (2). No choice of scalar shift, rescaling, threshold, or bounded scalar function of the exact score repairs this contrast loss.

A related restricted-testing statement is legitimate if its experiment is specified in advance. Fix G as above under BOTH hypotheses. Take the null pair (rho_(1/2),rho_(1/2)) and alternative pair (rho_(1/2),rho_1). A protocol restricted to G readouts, or their classical post-processings, on at most T total copies has transcript variation at most T times the right side of (9), by a sequential hybrid argument. Thus such restricted protocols require Omega_beta(R) copies for constant success. This does not grant an oracle that reveals the actual unknown pair's logarithmic difference: that would reveal whether it is zero and would be a different experiment. It also does not limit arbitrary collective measurements, which can simply measure the data qubit here.

## 6. Relation to the valid Gibbs variational identity

For faithful rho,sigma,

    Tr[(rho-sigma)(log rho-log sigma)]
       = D(rho||sigma)+D(sigma||rho) >= ||rho-sigma||_1^2,               (10)

using natural logarithms and quantum Pinsker for each summand. Equation (10) is fully consistent with this construction: the score's eigenvalue range grows like R while its informative outcomes become rare. A constant unnormalized mean gap is not a constant bounded-measurement signal or a uniform variance estimate.

The original primary source, Bluhm et al., *Certifying and learning local quantum Hamiltonians*, arXiv:2603.29809v1, Lemma4/Equation(5), Lemma15 and Theorem17, uses the energy/moment relation with explicit parameter-dependent estimation accuracy. Its proof is not contradicted. Those passages were inspected for applicability; this is not a complete independent audit of the paper.

https://arxiv.org/html/2603.29809v1#S2.SS2
https://arxiv.org/html/2603.29809v1#S4.SS1
https://arxiv.org/html/2603.29809v1#S4.SS2

Virtual transitions changing low-energy populations while the mediator is rarely occupied are an established physical mechanism. No historical priority is claimed for that mechanism or this example. The role here is to check an exact proposed P1 proof step under the original coefficientwise source contract.

## 7. Remaining original obligation

The family supplies a concrete fixed-beta counterexample to a dimension-independent guarantee for the spectral measurement of the true local score. It does not exclude a successful variational search over OTHER observables, nor improve the accepted unrestricted P1 lower bounds. A full-class upper still needs an actual copy-only way of choosing and measuring a uniformly adequate witness, with all selection, variance and error costs accounted for. Accepted components26/27 and the full optimal-copy question are unchanged.
