# Fixed-lead nanowire nonseparation at a positive visibility margin

**2026-10-16. Authors:** Nolan and dot. **Verification:** scoped independent hand-proof review plus an independently replayed exact-rational finite-matrix certificate. This is not a Lean proof. The historical candidate is preserved unchanged; the independent review records its accepted scope.

## What is established

For one explicitly declared 60-site Rashba nanowire model with fixed normal leads, zero internal dissipation and unrestricted finite scalar onsite potentials, the two classes with zero-energy reflection visibility at field 2 meV at most −0.1 and at least +0.1 have **zero separation in their entire closed-wire lowest-energy curves** over fields 0–2 meV.

- Both devices have the same length, lattice, hopping, pairing, spin-orbit coupling and physical leads.
- Each device uses one fixed potential vector throughout the field sweep.
- The visibility margin stays at 0.1 while the energy-curve distance tends to zero.
- The proof therefore covers any fixed 512-field menu within that interval. It establishes a uniform bounded-error identification obstruction for the declared model.
- A finite threshold for the barrier parameter exists by the proved strict limits. A certified numerical threshold has not been extracted.

[Read the preserved proof](FIXED-LEAD-POSITIVE-MARGIN-CANDIDATE-01.md) and [independent review](INDEPENDENT-REVIEW-01.md).

## Why this matters

A margin on the desired visibility label alone does not guarantee robust identification from energy measurements. In this construction, large but finite end potentials reduce the effective contact width while the microscopic leads themselves remain fixed. The two visibility signs retain a substantial margin although the closed-wire spectra become arbitrarily close.

This is a worst-case conditioning result. It is not a claim of exactly identical noiseless observations, a typical-device or average-case error rate, fabrication feasibility, or a correction to a published experiment. No historical novelty claim is made.

## Source admission remains separate

[Taylor, Pan and Das Sarma, arXiv:2512.13825v2](https://arxiv.org/html/2512.13825v2) motivate the energy-to-visibility target and specify the underlying Rashba Hamiltonian and zero-dissipation table. The declared 0.6 μm device is at the Table 1 length boundary. However:

- Their exact lead Hamiltonian/contact implementation has not been authenticated from source code.
- Their Gaussian-disorder description does not by itself authenticate clipping, realized-RMS normalization or other dataset-generation restrictions. The theorem needs unrestricted finite scalar potentials. An untruncated nondegenerate Gaussian would supply full support; a bounded or normalized realization class may exclude this sequence.
- The exact finite field list has not been recovered. The theorem controls the complete interval, but a claim about an archived label must still bind its actual target field.
- **The modified energy-plus-length unsupervised variant in Appendix II excludes lengths below 1 μm. The present 0.6 μm construction is not admitted to that variant.** Do not transfer the Table 1/supervised length range to this variant.
- Positive internal broadening changes this singular limit. The result is for zero dissipation.

Accordingly, this packet is not an authenticated counterexample to Taylor's exact implementation. [MEDA, arXiv:2607.26208v2](https://arxiv.org/html/2607.26208v2) has a different conductance observation and periodic-disorder target; no MEDA impossibility follows.

## Attribution

The dependence of reflection visibility on energy splitting and lead coupling is prior physics. [Araya Day et al., *SciPost Physics Core* 8, 047 (2025), §3.1](https://arxiv.org/html/2504.01069v1) give explicit effective-model formulas and discuss lead bias. This packet supplies a scoped microscopic construction and exact finite-matrix certificate, without claiming that underlying mechanism is new.

Additional held-out conductance settings were already used to validate inferred disorder in [Taylor, Sau and Das Sarma, *Physical Review Letters* 132, 206602 (2024)](https://arxiv.org/html/2307.11068v2). Those simulated truncated-model tests are useful prior, and are not a uniform identification theorem.

## Verification and reproduction

The certificate pins a rational approximate inverse for a 115 × 115 minor of the central chiral block. The checker proves the minor remains invertible, encloses the transverse scalar crossing and endpoint weights, and verifies strict visibility-limit bounds using exact rational comparisons. Its hopping interval contains the standard conversion of the stated 0.01519 electron-mass parameter at 10 nm spacing.

With Python and NumPy already available, run:

```sh
OPENBLAS_NUM_THREADS=1 python verify_crossing_certificate.py
```

The checker does not use an eigensolver or floating-point acceptance tests. `certify_crossing.py` records proposal-generation provenance; it uses floating point to propose data before exact checks. `finite_barrier_smoke.py` and `FINITE-BARRIER-SMOKE.json` are **diagnostics only**, not certificates. The Schur-complement scattering limit and identification consequence are independently reviewed hand arguments beyond the script's acceptance scope.

`MANIFEST.json` is the preserved pre-review manifest. `PUBLICATION-MANIFEST.json` gives the publication packet's file sizes and SHA-256 hashes. `independent-review/` preserves the independent checker replay and supplemental symbolic checks; the review states their actual scope.
