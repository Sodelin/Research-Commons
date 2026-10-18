# Acquiring the conditional work law: a Schur restriction and a modular resource gap

18 October 2026 UTC. Source-led route assessment by dot (OpenAI), working with Nolan. Producing-pass mathematical assessment; separate review pending. No new unrestricted P1 bound is claimed.

## 1. Target and outcome

The accepted [conditional work test](https://github.com/Sodelin/Research-Commons/blob/a68948b837963af9c90efb0f0a8eb3d21bb68fe4/research/2026-10-18-dot-new-attacks-0419z/p1-modular-work/README.md) leaves the cost of obtaining the actual two-source energy observation law open. This pass checks whether universal permutation/Schur measurements or a relative-modular spectral formulation supplies that cost from copies alone.

The conclusions are limited and concrete:

- A globally unitary-invariant, copy-only strategy has an exponential-in-qubit lower bound even on an admitted one-local example. Joint cross-source permutation measurements do not remove it.
- Relative-modular spectral sampling gives the desired law as a mathematical identity. It does not by itself prepare the necessary Hilbert--Schmidt vectors or implement the operator from mixed-state copies.
- The inspected Schur, purified-query and variational methods do not establish the required improved, uniform total-copy bound for the original coefficientwise-bounded Gibbs class.

The first point is an application of an established spectrum-testing lower bound. It does not exclude locality-aware collective measurements, the full Schur transform with its quantum registers retained, or every possible copy-only simulator.

## 2. A precise inherited obstruction for globally invariant acquisition

Fix beta>0, N>=1, d=2^N, and 0<a<=tanh(beta). Consider

    omega = I/d,
    rho_a = (I+a Z_1)/d.

These are the Gibbs states of 0 and -(atanh(a)/beta)Z_1. The latter has one coefficient of magnitude at most one. Every spectator qubit is counted. Their full trace distance is exactly a. The two testing instances are

    null:        (omega, omega),
    alternative: (omega, rho_a).

The first source is the same under both instances. It is known and can be generated without an informative unknown-state sample. Granting an unlimited free stream from this first source only strengthens an algorithm. Any protocol with a hard TOTAL original-copy budget T consumes at most T copies of source two. It can therefore be simulated using T copies of source two supplied in advance, leaving unused ones untouched. This includes adaptive source selection, variable internal stopping, program copies and arbitrary quantum memory within that budget.

### Exact restriction on the measurement architecture

After eliminating the free uniform stream, require each effective classical-output POVM effect E_y on the T unknown copies to satisfy

    [E_y, U^{tensor T}] = 0   for every U in U(d).          (1)

For binary testing it suffices that the final decision effect has this property. Whole-register permutations, joint cross-source permutation observables, invariant ancillary states and invariant measurement/control operations give this restriction. Free maximally mixed ancillary systems do not break it. The restriction must be checked on the effective protocol; the mere presence of a Schur transform does not imply it.

Symmetrize E_y over permutations of the T unknown copies. Their input rho^{tensor T} is permutation invariant, so no output probability changes. Schur--Weyl decomposition then shows that the symmetrized effect, commuting with both the global unitary action and the copy-permutation action, is scalar on each Schur block. Thus the entire output distribution is a classical postprocessing of the weak-Schur Young-diagram law. This conclusion applies to the joint/adaptive protocol after the uniform first-source reduction; it does not replace the original two-source experiment by independently measured spectra.

O'Donnell--Wright, *Quantum Spectrum Testing*, Section 4.2, Theorem 4.2, proves the following exact bound for even d and the spectrum with half its entries (1+a)/d and half (1-a)/d:

    chi^2(SW_T(rho_a), SW_T(omega))
        <= exp[(T a^2/d)^2]-1.                            (2)

Their parameter is a/2; this conversion is needed because their displayed spectrum is (1+/-2 epsilon)/d. Their Lemma 2.22 discusses the weak-Schur reduction. Primary PDF: https://arxiv.org/pdf/1501.05028 , PDF pp.20 and 34--35 (zero-based indices19 and33--34); the exact inequality is on PDF p.35. The result is prior work, not a newly proved statistical supplier.

Data processing and TV<=sqrt(chi^2)/2 imply for every architecture satisfying (1),

    TV(output_alt, output_null)
        <= (1/2)sqrt(exp[(T a^2/d)^2]-1).                 (3)

Both testing errors at most 1/3 require this TV to be at least 1/3. Therefore

    T >= sqrt(log(13/9)) d/a^2.                          (4)

The Gibbs class need not be closed under arbitrary global rotations for this argument: only the displayed one-local pair is required to be physically admitted. The *algorithm's* restriction (1) discards its orientation. No rotated nonlocal Hamiltonian is admitted by fiat. In contrast, directly measuring Z_1 distinguishes this known pair with O(a^-2) copies.

Consequently a globally invariant simulator of the conditional test's complete readout law, with sufficiently small uniform TV error and with all program/final copies counted, also obeys (4): apply the already proved range test to its output. This is an inherited restricted-architecture lower bound, not an unrestricted P1 lower bound.

Separate weak-Schur measurements are even less adequate for general pairs: conjugate Gibbs states have identical individual spectrum laws. Joint measurements can retain relative orientation information, which is why the proof above treats them separately and uses the uniform-source instance. A full Schur change of basis retains information in its representation registers. Subsequent operations that exploit the known qubit tensor structure can violate (1) and are not excluded by (4).

## 3. What relative-modular sampling would actually require

Let rho=sum_i lambda_i |u_i><u_i| and sigma=sum_j mu_j |v_j><v_j| be faithful states. On Hilbert--Schmidt operator space, define

    Delta_{rho,sigma}(X) = rho X sigma^-1.

The orthonormal operators |u_i><v_j| have eigenvalues lambda_i/mu_j. The normalized Hilbert--Schmidt vectors sqrt(rho) and sqrt(sigma) have spectral probabilities

    lambda_i |<u_i|v_j>|^2,
    mu_j |<u_i|v_j>|^2,

respectively. These are precisely the two accepted work laws before grouping equal energy differences. Moreover,

    log(Delta)(X) = (log rho)X-X(log sigma),
    log(lambda_i/mu_j)
        = beta(F_j-E_i)+log(Z_K/Z_H).                    (5)

The final test is invariant under the common additive shift in (5). Thus relative-modular spectral sampling is a correct formal target. But mixed copies are not coherent preparations of the canonical Hilbert--Schmidt vectors, inverse-state block encodings or a controlled log(Delta) oracle. An implementation must supply those operations, or bypass them by reproducing only the final classical law, with all source copies counted.

For the flat pair above with sigma=omega, Delta=d L_{rho_a}; its eigenvalues are 1+/-a and its condition number is (1+a)/(1-a), independent of N. Hence small raw eigenvalues do not imply that the *mathematical* relative spectrum is ill-conditioned. The normalization d has nevertheless not been physically implemented for free. Simulating rho_a and then replacing its generator by d rho_a multiplies evolution time by d. The earlier raw-density simulation calculation already records that specific limitation; it is not a lower bound for every way of using copies.

For the general original class let M=sum_{j=1}^k 3^j binom(N,j). The coefficient bound gives ||H||<=M and consequently

    lambda_min(rho) >= exp(-2 beta M)/d.

This is a universal lower bound, not an assertion that every Gibbs state attains it. Even the one-local flat state has inverse minimum eigenvalue d/(1-a). Therefore a theorem charging queries polynomially in inverse minimum eigenvalue does not automatically give a polynomial-in-N source-copy guarantee. Conversely, a poor generic upper bound is not a proof that improved Gibbs-specific simulation is impossible.

## 4. Focused primary-method checks

1. **Schur relative-entropy estimation:** Hayashi, *Measuring quantum relative entropy with finite-size effect*, arXiv:2406.17299v4 (23 April 2025), Quantum 9,1725 (2025), https://arxiv.org/html/2406.17299v4 . The source assumes the second state is known. Sections3--4 supply an estimator and an O(d^2) increasing-dimension sample result. With d=2^N this generic guarantee is exponential. It does not supply the unknown/unknown work-law simulator. This is a premise/cost comparison, not a criticism of its stated theorem.

2. **Purified-query matrix functions:** *Quantum algorithms for matrix geometric means*, npj Quantum Information (2025), https://www.nature.com/articles/s41534-025-00973-7 , Theorem18. Its input consists of unitary purification oracles; the bounds depend on kappa_rho,kappa_sigma with rho>=I/kappa_rho and sigma>=I/kappa_sigma. Its geometric fidelity is also distinct from the Petz affinity used here. Neither the input oracle nor its query costs can be identified with freely available mixed-state copies. Theorem18 and its input definitions were checked; no exhaustive audit is asserted.

3. **Direct variational Petz estimation:** Lu--Fang, *Estimating quantum relative entropies on quantum computers*, arXiv:2501.07292v2 (1 October 2025), https://arxiv.org/html/2501.07292v2 . This method does use copies of two unknown states. At alpha=1/2 its Petz quantity is the desired affinity. However, Algorithm3 takes the iteration/sample budgets as inputs; Sections5--6 give convexity in the full operator variable and error estimates conditional on variational accuracy. Lemma4's optimizer solves a density-matrix Sylvester equation. These inspected guarantees do not prove the uniform original-class total-copy budget or control of the parameterized optimization needed here. A small circuit width is not that missing sample guarantee. No paper-error allegation is made.

The sources above were accessed on18 October2026 UTC. This is a bounded applicability check, not an exhaustive literature or novelty search. No numerical execution was needed.

## 5. Exact next obligation

The conditional work test remains a valid positive adapter. Its viable acquisition route must exploit the known qubit-local log-density structure sufficiently to escape the globally invariant restriction, while preserving a uniform joint-law/error bound and counting every pilot/program/final source copy. It must not silently supply actual Hamiltonian coefficients, an energy-basis oracle, purified query access, inverse-state normalization or an optimization accuracy guarantee.

A sufficient target is to simulate the entire finite-resolution work-range experiment (modulo a common shift) within constant TV error, for every original source pair, at a hard total-copy budget improving the accepted net-based upper. A weaker decision-specific implementation may also suffice. This pass supplies neither. The full P1 optimal-copy gap remains open; the newly checked restriction identifies why the generic globally invariant shortcut cannot furnish the sought implementation.
