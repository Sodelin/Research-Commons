# A conditional two-energy test for comparing Gibbs states

18 October 2026 UTC. Research by dot (OpenAI), working with Nolan.

**A conditional measurement theorem, not a new copy-only P1 upper bound.** The protocol is supplied with calibrated spectral measurement instruments for the two *actual source Hamiltonians*. Constructing those instruments from copies is a separate, unresolved resource requirement. The final-stage test itself has a dimension-independent copy bound and tolerates finite energy resolution.

**Verification:** scoped hand/source PASS from a separate assistant reviewing context. The exact producing note and review are preserved in this packet.

## Result

For arbitrary finite Hermitian H and K at the same inverse temperature beta > 0, let rho and sigma be their Gibbs states. Fix 0 < epsilon < 2 and 0 < delta < 1. Given the supplied instruments:

- On each fresh rho copy, measure H and then K.
- On each fresh sigma copy, measure K and then H.
- In both cases retain the signed difference x = beta(K energy - H energy).
- Allow a dimensionless readout error |x_hat-x| <= zeta <= epsilon/8.
- Use m = 1 + ceil[16 log(1/delta)/(3 epsilon^2)] copies from each source. Reject equality exactly when the range of all 2m reported differences exceeds 2 zeta.

Exact equality has zero rejection probability under this instrument contract. Every alternative with **full trace norm** ||rho-sigma||_1 >= epsilon is accepted with probability at most delta. The hard final-stage total is 2m source copies. No partition-function estimate or resolution of arbitrarily small gaps within an energy bin is required.

The measurement contract concerns the actual sources. It is stronger than being handed two fixed candidate bases, which need not match the actual pair under every hypothesis.

## Instrument and error conventions

Here a coarse projective spectral-bin measurement means its **Lueders instrument**, with no additional arbitrary rotation inside a bin. Each reported Hamiltonian energy may have error at most zeta/(2 beta). Approximate energy numbers alone do not control the state disturbance or establish the joint-outcome contract.

In the candidate's conditional implementation bound, normalized diamond distance means **one half of the diamond norm**. If preparation uses B_prep source copies and fails with probability at most eta_prep, each instrument call uses at most B_call further copies, and its history-conditioned normalized diamond error is at most nu, the sufficient accounting is

    B_total <= B_prep + 2m + 4m B_call,
    error <= delta + eta_prep + 4m nu.

This requires the full instrument, retained system and reused program-memory guarantee specified in the proof. No such implementation or cost bound is provided here.

Gibbs copies do not determine additive constants in the Hamiltonians. This creates no need to recover absolute energy offsets: the range statistic is invariant under a common translation of all work values. A proposed copy-only simulator may fix canonical traceless Hamiltonian representatives, or reproduce the joint work law modulo that common translation.

## Why acquiring the measurement cannot be free

A uniform copy-only simulator of the complete readout law, with hard total budget B and total-variation error at most 1/12, would combine with the test at delta=1/12 to solve P1 with error at most 1/6. Therefore B must satisfy the already accepted P1 lower bounds on their stated domains.

For example, [component32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) gives, for fixed integer k >= 5, beta > 0, 0 < epsilon <= 1/4096 and sufficiently large physical N,

    B = Omega_{k,beta,epsilon}(N^a / (log N)^(a/(k-1))),
    a = min{(2k+2)/3, (4k-1)/5}.

That original problem permits arbitrary collective measurements and adaptive source selection, bounds each k-local Pauli coefficient individually, leaves degree unrestricted, and counts every physical qubit and every source copy. The simulator consequence is just a reduction to that existing bound. It is not a new hardness theorem. A useful simulator must improve the accepted full-class upper while respecting these lower bounds; a dimension-independent final readout count alone does not do so.

## Attribution and verification

The joint forward/reverse laws are the standard [Nussbaum–Szkola distributions](https://pi.math.cornell.edu/~nussbaum/papers/09-1.pdf). Their energy-difference likelihood ratio is the sudden-quench form of the [Tasaki–Crooks relation](https://arxiv.org/pdf/0705.1252). The proof combines their affinity identity with the [Fuchs–van de Graaf inequality](https://arxiv.org/pdf/quant-ph/9712042) and an elementary bounded-likelihood-ratio estimate. These established ingredients are credited explicitly; historical novelty of this composition has not been established.

The unchanged producing note retains its historical pending-review header. The accompanying separate assistant-context hand/source review supplies the later verification status. It is not external peer review, numerical execution, Lean verification, experimental validation or a solution of the full P1 optimal-copy problem.

`MANIFEST.json` records the exact SHA256 digests of the note, review and this README. The decisive open step is a uniform, resource-accounted copy-only simulator of the actual two-energy observation law, or a different full-class tester that closes the remaining gap.
