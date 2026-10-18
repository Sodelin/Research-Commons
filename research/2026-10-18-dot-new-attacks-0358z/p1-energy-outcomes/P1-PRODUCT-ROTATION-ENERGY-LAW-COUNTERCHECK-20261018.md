# A whole-energy-outcome countercheck for P1

Written 2026-10-18 UTC. Producing-pass hand derivation; awaiting separate review.

## Scope and conclusion

This note tests a specific proposed measurement route for the original P1 problem: compare the complete classical energy outcome laws of the two unknown Gibbs states, even granting the two Hamiltonian eigenbases for free. For every fixed inverse temperature beta > 0, an admitted one-local product pair has a constant full trace-norm separation, but measuring a fresh copy in either of the two specified product eigenbases gives only O_beta(1/N) relative entropy. Adaptive repetition of these measurements therefore requires Omega_beta(N) total copies for constant-error discrimination of this pair against an equality null.

This is a restricted measurement-route countercheck, not an unrestricted P1 lower bound. A known transverse product measurement distinguishes the same displayed pair with one physical copy. Nothing here excludes a quantum-output pilot, coherent quantum reference, joint measurement on unmeasured copies, other bases, or an improved full-class tester. The mechanism is the familiar fact that a small rotation changes diagonal populations only to second order; no historical novelty is claimed.

## 1. Exact admitted family and constants

Let r = tanh(beta), so 0 < r < 1, and set

    a = 8/r,
    N >= ceil(a^2),
    theta = a/sqrt(N) in (0,1].

On exactly N qubits, with no auxiliary spins, define

    H_0 = -sum_{i=1}^N Z_i,
    H_theta = -sum_{i=1}^N (cos(theta) Z_i + sin(theta) X_i).

Every displayed nonidentity Pauli coefficient has magnitude at most 1. These are one-local Hamiltonians and hence belong to every original P1 class with k >= 1. Their Gibbs states at the same fixed beta are

    rho = tau_0^(tensor N),
    sigma = tau_theta^(tensor N),
    tau_0 = (I + r Z)/2,
    tau_theta = (I + r(cos(theta) Z + sin(theta) X))/2.

Both are faithful. Consider the simple two-source hypotheses

    null:        (rho, rho),
    alternative: (rho, sigma).

The parameters and both candidate bases may be supplied to the restricted tester. Granting this information strengthens the restricted tester, so the lower bound below is not an unknown-basis acquisition argument.

## 2. Constant full trace distance, with an explicit easy test

Measure X on every qubit of one copy from the second source. Let S be the sum of the N outcomes, each in {-1,+1}. Under the null E[S] = 0; under the alternative

    E[S] = N r sin(theta) >= N r theta/2 = 4 sqrt(N),

using sin(theta) >= theta/2 for 0 <= theta <= 1. The variables are independent under each hypothesis. Reject equality when S >= 2 sqrt(N). Hoeffding's inequality gives, under each respective hypothesis,

    Pr_null(reject) <= exp(-2),
    Pr_alternative(accept) <= exp(-2).

Consequently the total variation distance between these particular measurement outcome laws is at least 1 - 2 exp(-2). Measurement cannot increase full trace norm, so

    ||rho - sigma||_1 >= 2 - 4 exp(-2) > 1/4.                 (1)

Thus the pair is admissibly far for every original accuracy promise epsilon <= 1/4. The single-copy X measurement is only a test of this known displayed pair against its specified null. It is not asserted to test all unknown P1 states.

As a separate consistency identity, the squared single-qubit fidelity is

    F(tau_0,tau_theta) = 1 - r^2 sin^2(theta/2).

Multiplicativity gives root fidelity

    sqrt(F(rho,sigma)) = (1-r^2 sin^2(theta/2))^(N/2)
                       <= exp(-N r^2 sin^2(theta/2)/2).

The proof of (1) does not rely on this optional identity.

## 3. Complete product-eigenbasis outcome laws

Let B_0 be the tensor product Z eigenbasis, and B_theta the tensor product eigenbasis of cos(theta) Z + sin(theta) X. In B_0, the single-qubit plus probabilities under rho and sigma are, respectively,

    p = (1+r)/2,
    q = (1+r cos(theta))/2.

In B_theta the same two probabilities are interchanged. All N outcomes within a copy are independent. Both probabilities lie in [(1-r)/2,(1+r)/2], and

    |p-q| <= r theta^2/4,
    p(1-p), q(1-q) >= (1-r^2)/4.

For Bernoulli laws, log(u) <= u-1 yields the elementary bound

    D(Ber(p) || Ber(q)) <= (p-q)^2/[q(1-q)].

The same bound with the roles reversed holds. Hence in either of the two specified bases, in either relative-entropy direction, the complete N-bit laws obey

    D(P_N || Q_N) <= N r^2 theta^4/[4(1-r^2)]
                  = K_beta/N,
    K_beta := 1024/[r^2(1-r^2)].                            (2)

This is a bound on the entire recorded N-bit outcome, not merely its mean or total energy. Coarsening to the energy histogram can only decrease distinguishability.

Degeneracy boundary: the sum Hamiltonians have degenerate energy levels. B_0 and B_theta are the specified product refinements. The statement does not cover arbitrary coherent refinements inside degenerate energy subspaces, nor a measurement that retains the postmeasurement quantum state for later joint processing. It does cover the ordinary energy-value-only classical outcome measurement.

## 4. Adaptive source allocation and the total-copy budget

Consider any protocol using at most T physical copies in total. At each step, based on the previous classical outcomes and private randomness, it chooses a source and one of B_0 or B_theta, records its classical outcome, and discards that copy. It may postprocess all recorded data arbitrarily. The same decision rule is used under both hypotheses.

Condition on each realized classical history. A query to source one has identical laws under the two hypotheses. A query to source two has conditional relative entropy bounded by K_beta/N by (2), whichever allowed basis the history selected. The chain rule, also including the tester's random seed, therefore gives

    D(transcript_null || transcript_alternative) <= T K_beta/N.

A stopping rule with a hard cap T can be padded with deterministic empty observations. Pinsker's inequality gives

    TV(transcript_null, transcript_alternative)
        <= sqrt(T K_beta/(2N)).                            (3)

If each error probability is at most 1/3, the two final decision laws must have total variation at least 1/3. Thus

    T >= 2N/(9 K_beta).                                   (4)

The lower bound counts both sources and allows adaptive allocation. It concerns only the declared classical-outcome measurement restriction. It does not apply to unrestricted collective P1 measurements, and (1) exhibits the latter distinction concretely.

## 5. What this closes, and what remains

The proposed route needed a dimension-independent implication from a fixed full trace-norm gap to a fixed discrepancy in at least one source's energy outcome law. This family disproves that implication even for one-local Hamiltonians, at a fixed beta, with both specified product eigenbases known. It also shows that replacing scalar energy means by their full histograms does not repair this particular route uniformly.

It leaves open a decision-specific quantum reference or a measurement-selection procedure exploiting coherences across these bases. Such a procedure still requires a uniform performance and total-copy analysis for the full unknown noncommuting Gibbs class; knowing the useful transverse basis for this example is not that analysis. The original optimal-copy P1 target remains open.

## Sources and attribution

- W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables," JASA 58 (1963), 13-30, Theorem 2: https://doi.org/10.1080/01621459.1963.10500830 . The two displayed tail bounds are its direct independent bounded-variable application.
- Relative-entropy chain rule, classical Pinsker inequality, data processing, and the product-state/Bloch-vector formulas are standard ingredients. The elementary Bernoulli relative-entropy estimate used here is derived above. This note claims no new general information inequality.
- Original project contract and accepted full-local-linear-mean boundary: https://github.com/Sodelin/Research-Commons/blob/9148fcf7184ac9c7565e32ebb95b4fa002f932e1/research/2026-10-16-g6-gibbs-certification/full-local-mean-signal-boundary-34/README.md . The present countercheck concerns two source-energy outcome laws, not the all-Pauli linear-mean span in that different construction.
- The accepted classical learning-pilot boundary leaves quantum-output pilots open: https://github.com/Sodelin/Research-Commons/blob/635139c505ac8ba72261e2f468bbd51fac3fce82/research/2026-10-16-g6-gibbs-certification/trace-localization-pilot-boundary-33/README.md .

No numerical execution is needed for this finite-constant hand derivation. A later review receipt, if supplied, should identify its exact source hash and scope separately.
