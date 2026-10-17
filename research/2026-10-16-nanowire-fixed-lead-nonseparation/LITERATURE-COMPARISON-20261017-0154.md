# Three 2026 nanowire inference studies: scope and relation to the all-channel bound

Prepared by dot for Nolan. Source check: October 16, 2026, Pacific time / October 17, 2026, UTC (approximately 01:54 UTC).

This is a bounded primary-source comparison, not a novelty certificate, reproduction of experiments, or endorsement of every interpretation in the cited papers. It preserves the distinction between a statistical prediction, a reflection determinant, and a bulk topological invariant.

## 1. Learning from the lowest-energy curve

Jacob R. Taylor, Haining Pan and Sankar Das Sarma, *Machine learning Majorana topology using unsupervised and supervised learning*.

- Status: Physical Review B 114, 165418, published September 21, 2026. The inspected arXiv v2 was posted October 6, 2026; v1 was December 15, 2025.
- Inputs and target: simulated lowest-excitation-energy curves across Zeeman field, with a zero-energy reflection determinant (topological visibility) used in the learning analysis.
- Demonstrated contribution: supervised/unsupervised analysis of the simulated distribution, including intermediate behavior in short or disordered wires.
- Relation to our result: the reflection determinant is the same mathematical type of target, but the all-channel conductance theorem needs the corresponding conductance. It does not make energy-only inference universally identifiable. Admission of our separate energy-nonseparation construction to the authors' exact implementation remains unverified.

Sources: [APS publication record](https://journals.aps.org/prb/abstract/10.1103/ywsw-29xc); [arXiv version record](https://arxiv.org/abs/2512.13825); [full v2 model, data and appendices](https://arxiv.org/html/2512.13825v2).

## 2. Predicting low-temperature behavior before dilution refrigeration

Jacob R. Taylor, Haining Pan, Jay D. Sau and Sankar Das Sarma, *Avoiding Dilution: Using Diffusion and Vision Transformers to resolve Majorana Features in Nanowires at High Temperature*.

- Status: arXiv v1, July 16, 2026. The APS accepted-paper record lists acceptance to Physical Review B on October 1, 2026. The detailed methods inspected here are the arXiv version, not a verified final typeset successor.
- Inputs and target: paired simulations of local/nonlocal conductance maps at 300 mK and 50 mK, over bias, chemical potential and field; a second network predicts low-temperature visibility.
- Reported evidence: test-set R² approximately 0.95 for local-conductance reconstruction, 0.91 for nonlocal reconstruction and 0.80 for visibility. These are predictive metrics, not worst-case error guarantees.
- Potential use: preliminary device screening. This source does not establish experimental replacement of low-temperature characterization.
- Missing theorem connection: Eq. (3) thermally averages conductance; the model also changes the parent superconducting gap with temperature. A certified bound on the appropriate zero-energy conductance is needed before applying our inequality to a warm measurement.

Sources: [APS acceptance record](https://journals.aps.org/prb/accepted/10.1103/12cp-xlkb); [arXiv version record](https://arxiv.org/abs/2607.14949); [full methods, especially Section II and Eq. (3)](https://arxiv.org/html/2607.14949v1).

## 3. Sparse measurements for a different topology target

Nathan Jones, Binayyak Roy, Valentine Mohaugen, Ian Lewis, Toby Cox, Sumanta Tewari and Rong Ge, *MEDA: Measurement-Efficient Disorder-Aware Majorana Zero Mode Detection in Realistic Devices*.

- Status: arXiv v1 July 28, 2026; v2 August 16. The author-maintained arXiv record reports acceptance to the 2026 IEEE International Conference on Quantum Computing and Engineering. This check did not independently establish a proceedings-publication date.
- Inputs and target: sparse chemical-potential slices of four local/nonlocal conductance maps predict a dense periodic-disorder-invariant (PDI) map.
- Demonstrated contribution: reduced input requirements in simulations, reporting a tenfold reduction; the paper also reports difficulty with highly fragmented phase maps.
- Target boundary: PDI is computed by embedding the device into an infinite repeated superlattice. It is not the finite-device reflection determinant. Our determinant inequalities therefore do not certify its PDI labels.
- The model includes positive dissipation in some cases. Its presence is not, by itself, an algebraic refutation of the all-channel theorem; the actual scattering and measurement assumptions still require checking.

Sources: [arXiv status/version record](https://arxiv.org/abs/2607.26208); [full v2 methods, Sections II–V](https://arxiv.org/html/2607.26208v2).

## Exact boundary for using the all-channel theorem

The [reviewed all-channel packet](https://github.com/Sodelin/Research-Commons/blob/f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1/research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel/README.md) concerns every finite number N of electron channels and a zero-energy reflection matrix

r = [[A, B], [conj(B), conj(A)]]

that is a contraction. For the same matrix and channel convention, define

g = G/(e²/h) = N − ||A||F² + ||B||F², and Q = det(r).

Its bounds include Q ≥ 1 − g and (−1)^N Q ≥ g − (2N − 1). Particle-hole symmetry, contractivity and this exact conductance identification are substantive admission conditions. Passive broadening or loss need not violate them automatically; an effective implementation must be checked. Conversely, a finite-temperature average or a differently normalized measurement is not automatically the g in these formulas.

A justified interval for the underlying g can support a determinant bound or an abstention decision. Average prediction scores do not supply such a per-device interval. A positive determinant is not a proof of protected Majorana modes. The particular previously certified finite-pair construction retains its zero-internal-dissipation assumption; the broader algebraic theorem does not silently remove that assumption from the construction.

A useful application is checking consistency of simulated zero-energy conductance/determinant pairs, followed by calibrated, error-aware measurement inference. Neither this checkpoint nor the cited predictive studies establishes universal energy-spectrum or Hamiltonian reconstruction.

## Search and verification boundary

The bounded search checked the three exact arXiv identities, current primary publication/acceptance metadata, and their accessible full arXiv methods, plus focused 2026 searches for conductance, inverse inference and determinant bounds. APS search-indexed primary records supplied the publication/acceptance dates; the full-method comparisons use the linked arXiv versions. No source code was executed and no device data were reanalyzed. These are three closely relevant works, not an exhaustive 2026 bibliography. No historical novelty of our all-channel result is established by this search.

This checkpoint adds literature/status clarification. It changes neither the accepted mathematical statements nor their verification level: reviewed hand proofs and separate interval certificates are not a completed Lean formalization.
