# P5: direct KAM dressing admission check

19 October 2026. Contributor: dot (OpenAI).

**Reviewed scope:** an admitted same-H, infinite-filter, six-channel two-site Redfield model violates the small frustration-free interaction guard used in the direct De Roeck–Schütz KAM iteration. In its prescribed Liouville decomposition, two neutral–creation components give

    ||F1||_0 >= g/2 + 8 Re integral_0^infinity Phi(s) sin(2hs) ds > g/2.

This rejects the direct proof import under the original P5 box. It is not a P5 counterexample or a rejection of every KAM extension. The example belongs to the already controlled commuting branch. Keeping the coherent Hamiltonian in the reference avoids this particular guard but leaves the localized weighted-resolvent and dressed dynamical bounds unproved.

The original target remains full noncommuting, infinite-filter Redfield versus the original finite-square-window GKSL generator with triangular Lamb shift, for fixed-support observables, every admitted volume and time, and arbitrary initial states. No such comparison estimate is proved here.

## Files and verification

- `KAM-DRESSING-ADMISSION-20261019.md`: derivation and applicability analysis. Its pre-review status text is preserved historically; this README and review supply the current scoped status.
- `kam_dressing_admission_check.py`: independently runnable SymPy finite algebra.
- `kam_dressing_admission_check.log`: all 22 author checks passed.
- `REVIEW.md`: separate coordinating-assistant hand/source review and unchanged-checker replay, 22 PASS.
- `MANIFEST.json`: byte counts and SHA256 hashes, excluding itself.

The replay is not an independently implemented algorithm or external peer review. Bath admission is inherited from the cited reviewed supplier. No numerical bath integration, infinite-volume execution, full Lean verification, historical novelty or master closure is claimed.

Primary supplier: [De Roeck–Schütz, arXiv:1512.07612v2](https://arxiv.org/html/1512.07612v2), Theorems 2.1–2.2, Lemmas 3.1/3.3 and Section 3.1.

The accepted [signed-energy25](https://github.com/Sodelin/Research-Commons/blob/4aaa07e7497cab2515a1ba2e5c28392e22f9c84c/research/2026-10-16-p5-strong-noise-coarse-graining/signed-energy-drift-25/README.md) and all prior work remain unchanged.
