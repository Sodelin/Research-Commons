# All-channel extension: directed prior-work addendum

17 October 2026 UTC. dot (OpenAI), working with Nolan. Local review draft. The all-N proof is being reviewed separately; this is a source/overlap assessment, not mathematical acceptance of that manuscript or a novelty certificate.

Target: canonical PHS contractive 2N×2N reflection, g=N−||A||F²+||B||F², Q=det r, and proposed inequalities Q≥1−g and (−1)^N Q≥g−(2N−1). Physical conductance interpretation remains zero energy/zero temperature/zero bias with admitted channels, contacts and normalization.

## Exact antecedents

**Bravyi, “Lagrangian representation for fermionic linear optics,” quant-ph/0404180v2, Sec.IV Eqs.17–19, PDF p4.** Eq.17 is the Wick/Pfaffian formula for even Majorana correlations. Eq.19 gives the canonical product density operator; its following paragraph states that real antisymmetric M is a Gaussian-state covariance exactly when M^T M≤I, with pure states at equality. This is the direct standard supplier for a normalized positive auxiliary state with covariance built from a contraction. Singular/mixed cases are included. Conventions matter: Bravyi's Majoranas and covariance signs should be translated explicitly rather than copied without matching the vacuum. https://arxiv.org/pdf/quant-ph/0404180

**Wimmer, Akhmerov, Dahlhaus, Beenakker, “Quantum point contact as a probe of a topological superconductor,” arXiv:1101.5795v2, Sec.II Eq.3, PDF p2; Appendix B.** They write g=1−Q+4 sum' R_n using Béri degeneracy for the unitary-reflection setting. The nonnegative remainder immediately gives Q≥1−g there. Hence the lower inequality's unitary all-N special case is explicitly implied by prior work. Their zero-temperature/zero-voltage scope is stated in Sec.IV. This source does not establish the replacement of the ±1 topological invariant by an arbitrary contractive reflection determinant. https://arxiv.org/pdf/1101.5795

**Diez et al., arXiv:1206.3079, Sec.II Eqs.9–10.** The previously checked conductance lower and parity-dependent upper bounds are for unitary reflection; their G0=2e²/h differs from our normalization. The text extends the bounds to class D through Béri degeneracy. The proposed general formula should be presented as consistent with these restricted antecedents, not as the first relation between conductance and topology. https://arxiv.org/pdf/1206.3079

**Grabsch, Cheipesh, Beenakker, “Pfaffian formula for fermion parity fluctuations in a superconductor and application to Majorana fusion detection,” arXiv:1903.11498, Sec.2 (global parity Eq.7; open-subsystem Pfaffian formula), and Sec.4 Eq.23.** This explicitly treats nonquantized parity expectation for an open subsystem, computed by Pfaffians. Its covariance/subsystem construction and physical parity observable are established prior. This is not itself the claimed reflection-determinant versus local-charge-conductance inequality. Their Majorana normalization differs from Bravyi's. https://arxiv.org/pdf/1903.11498

## Elementary ingredient: do not claim novelty

For occupation number k≥0, (-1)^k≥1−2k. Therefore for every density operator, including non-Gaussian states,

    expectation(parity) >= 1 - 2 expectation(total occupation).

Equivalently, probability(odd occupation)≤expectation(total occupation). This is an elementary occupation-basis inequality (or Markov/union bound), not a special Gaussian theorem. I did not locate a particular primary source printing exactly this inequality in the directed search; that does not make it novel. The substantive proof obligation is the exact auxiliary-state dictionary: its parity expectation must equal det r, and twice its mean occupation must equal the specified g, including signs, factors and singular contractions. Applying particle/hole exchange then requires determinant multiplier (-1)^N and g↦2N−g.

## Search disposition and limits

Directed queries covered nonunitary visibility/conductance bounds, det r versus 1−g, Gaussian parity/occupation inequalities and Pfaffian covariance results. The 2016 visibility paper remains a model-sweep/correlation comparison rather than an inspected universal all-N inequality. No exact arbitrary-contractive all-N statement was located in these inspected sources; this is a bounded-search result only. Neither new-theorem priority nor independent physical interpretation of the auxiliary density operator follows.

Recommended attribution: an exact contractive-scattering application of classical Gaussian covariance/Pfaffian machinery and the elementary parity–occupation inequality, with explicit unitary antecedents and historical novelty unresolved. Do not imply a new fermion-parity principle or that the auxiliary state is an experimentally prepared state of the device.
