# Independent review: invariant acquisition and modular-resource boundary

18 October 2026 UTC. Reviewer: dot (OpenAI), independent reviewing lane.

## Identity and verdict

Reviewed unchanged candidate `P1-MODULAR-WORK-ACQUISITION-CHECK-20261018.md`, SHA256 `50d87ee28214a86627f975f0713cd05f0e6869eb0c897a267111c4929d3a33bd`.

**Scoped hand/source PASS.** Section 2 correctly imports an established weak-Schur testing bound into the explicitly globally invariant measurement architecture, including joint adaptive access to both sources. Section 3's finite-dimensional modular identities and resource qualifications check. No new unrestricted P1 lower bound or copy-only implementation is established. No numerical execution, formal verification, or exhaustive literature audit is part of this review.

## 1. Primary statistical supplier

I directly read O'Donnell and Wright, *Quantum Spectrum Testing*, [primary PDF](https://arxiv.org/pdf/1501.05028), Section 4.2, Theorem 4.2 on PDF page 35, its alternating spectrum on page 34, and Lemma 2.22 on page 20. Their spectrum uses entries `(1 +/- 2 epsilon)/d`. Substitution `epsilon=a/2`, `n=T` gives exactly

    chi-square <= exp((T a^2/d)^2)-1.

The direction of chi-square is the perturbed weak-Schur law relative to the uniform law. The source's even-dimension requirement holds for d=2^N, N>=1. The stated a range is inside its admitted parameter interval. This review imports that theorem; it does not independently re-prove its representation-theoretic proof.

## 2. Actual admitted source and measurement restriction

The physical state `(I+a Z_1)/d` is generated at the specified beta by `-(atanh(a)/beta) Z_1`. The coefficient is at most one and the N-1 maximally mixed spectator qubits are counted. Its full trace-norm distance to I/d is a. No arbitrary rotation of this Hamiltonian is asserted to remain local.

For a protocol with a hard total budget T, supply T second-source systems in advance. Simulate each requested first-source system by the known maximally mixed state, and reveal the next second-source system whenever requested. This represents arbitrary adaptive source choices, quantum memory, and early termination by a fixed effective POVM on T second-source copies. Unused systems can be ignored. The restriction to effects commuting with every U^(tensor T) is an explicit additional assumption on that effective POVM, rather than a property of all P1 protocols.

Average those effects over permutations of the T input copies. The tensor-power input makes this averaging probability-preserving. Schur--Weyl decomposition is multiplicity-free as a representation of the paired unitary and permutation actions; an effect commuting with both acts as a scalar on each summand. Positivity and POVM normalization make those scalars a classical output channel from the Young-diagram distribution. This proves the data-processing step even for the joint/adaptive protocol, without replacing the experiment by separately measured spectra.

In particular, globally invariant operations and invariant ancillas retain the restriction after the maximally mixed first stream is eliminated. A circuit merely containing a Schur transform need not retain it. The candidate correctly exempts locality-aware subsequent operations and retained representation registers that permit noninvariant measurements.

## 3. Constants and simulator consequence

Cauchy--Schwarz gives total variation at most one half the square root of the imported chi-square. A decision with each error at most 1/3 has output total variation at least 1/3. Consequently

    exp((T a^2/d)^2) >= 13/9,
    T >= sqrt(log(13/9)) d/a^2.

These constants and the hard total-copy convention check. An invariant acquisition procedure followed only by classical work-range processing stays invariant. If its simulation error and the conditional range-test error together are at most 1/3 under each hypothesis, the same necessary budget follows. All program, pilot and final unknown-source copies must remain within T. This does not exclude an orientation-sensitive simulator; the displayed pair itself has an inexpensive Z_1 test.

## 4. Modular identity and resource boundary

For faithful rho and sigma, the Hilbert--Schmidt operators `|u_i><v_j|` form an orthonormal eigenbasis of left-rho/right-sigma-inverse multiplication, with eigenvalues lambda_i/mu_j. The squared overlaps of sqrt(rho) and sqrt(sigma) with that basis are respectively lambda_i and mu_j times `|<u_i|v_j>|^2`. Their sums are one. Thus the claimed two work laws and logarithmic common-shift relation are exact, including spectral degeneracy after summing equivalent entries.

For sigma=I/d, the relative operator is d times left multiplication by rho, so the flat example's relative condition number is `(1+a)/(1-a)`. This checks the distinction between mathematical conditioning and the physical cost of implementing that normalization. Also, `||H||<=M` implies `lambda_min(rho)>=exp(-2 beta M)/d` by bounding its smallest Boltzmann weight and partition function separately. The candidate does not mistake this universal lower bound for a typical eigenvalue estimate or a general implementation lower bound.

I read the complete candidate, but did not independently re-audit all the external methods in Section 4. Those remain the contributor's bounded applicability checks, rather than a blanket independent review of the cited papers. This scoped acceptance covers the explicit inherited Schur restriction and the directly checked algebra/resource distinctions. The original two-unknown copy-only P1 problem remains open.
