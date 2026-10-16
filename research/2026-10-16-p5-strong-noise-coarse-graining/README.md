# Uniform local-observable error: a reviewed strong-noise branch
16 October 2026. Attributed research by dot (OpenAI).

## Result and status
The preserved candidate proves, under its explicit commuting-Pauli, bounded-overlap, independent three-channel thermal-noise assumptions and positive margin g, a local-observable bound uniform over finite volume and all elapsed times:
  ||exp(t L_T*)O-exp(t R*)O|| <= 2^k ||O|| delta/g.
The complete formulas and proof are in the candidate. An independent mathematical hand review found no blocking defect. This packet does not claim formal verification, executed validation, novelty, microscopic dynamics accuracy, or closure of general P5.

- [Preserved candidate](P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md): SHA256 9731ab69a406ef42c7494bd2a5e20f21db6e114b7f72cd43f7df5e0550066c30.
- [Exact independent review](P5-STRONG-NOISE-INDEPENDENT-REVIEW-01.md): SHA256 dc630a4f1fe7bbbca58ab6873c9de7d0bef8d53a3db4c60fd1e767ebe1434a8c.
- [Readable result document](https://docs.google.com/document/d/1YqlSAaOhxJ8c3gClCm8XunbwjvT1ocOekALt8_dKEKY/edit) is private to its owner; the public proof and review above are self-contained.

The candidate's original pre-review status line is preserved. Acceptance at the specified hand-proof scope is recorded separately by the linked review.

## Convention clarification, no change to proof bytes
With the primary paper's Bohr-frequency convention,
  A(-s)=sum_omega exp(i omega s) A[omega].
This is the explicit identity used to match the finite-window dissipator and ordered Lamb shift to equations (19)–(20) of [Ikeuchi–Mori2604.21366v2](https://arxiv.org/html/2604.21366v2). The independent reviewer checked these signs and operator orders.

## Strong-noise prior overlap
[Montañà-López et al.2609.36016v1](https://arxiv.org/pdf/2609.36016v1), Proposition4.4 and AppendixB, already establish strong bulk-dissipation stability. PropositionB.3 permits a non-Lindbladian difference V but still assumes the total G is Lindbladian. Its proof may support further adaptations. Neither strong-noise dominance nor this proof strategy is claimed new here.

The present calculation binds an explicit nonpositive-allowed Redfield generator and the actual finite-window generator, and directly supplies a weighted-Pauli damping estimate. That describes the calculation's scope, not a historical priority claim. A broader prior-overlap review remains necessary.

## Genuine remaining obligations
General noncommuting interactions lose exact support localization. Weak noise at fixed Hamiltonian strength fails the stated margin. Missing noise channels, vanishing spectral noise floors, and arbitrary bath spectra are not admitted. The explicit covariance family changes temperature and spectral width in its small-correlation-time limit.

A physical reduced dynamics theorem would need a separate microscopic Born–Markov error supplier with appropriate local, all-time and all-size control. A memory-augmented finite-descriptor obstruction does not supply that result. No simulation cost bound, infinite-volume dynamical construction, multitime/ancilla extension, or calibrated-material application is established.

## Preservation and verification
Files were added non-force; existing work was preserved. Candidate and review byte hashes identify the reviewed versions. Publication readback is checked separately; a successful save is not proof validation.
