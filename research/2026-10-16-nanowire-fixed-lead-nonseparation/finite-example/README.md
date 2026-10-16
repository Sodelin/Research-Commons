# Explicit finite-barrier nanowire certificate

This addendum gives two fully specified rational 60-site devices in the [previously declared fixed-lead model](../README.md). Both use the same external leads, a 1 eV end onsite barrier, zero internal dissipation, and the same common applied-field settings.

- Their reflection determinants at B = 2 meV have certified opposite margins: −0.203 < TV_minus < −0.202 and 0.996 < TV_plus < 0.997.
- Their lowest nonnegative closed-wire energies differ by at most **0.09999 μeV at every common field**. On any common 512-setting menu, one midpoint report lies within **0.049995 μeV** of both.
- This is one explicit finite pair at t = 25.08215 meV, not a uniform finite certificate over the earlier hopping interval. It makes a previously existential construction concrete; it does not assert equality of noiseless spectra or a measured classifier failure frequency.

## Read the result

1. [Exact statement, model, rational parameters and proof](FINITE-PAIR-CERTIFICATE-02.md)
2. [Independent review](INDEPENDENT-FINITE-PAIR-REVIEW-02.md)
3. [Strength and directed prior-work check](STRENGTH-AND-PRIOR-CHECK-02.md)
4. [Exact output intervals and source hashes](FINITE-PAIR-RESULT.json)
5. [File manifest](PUBLICATION-MANIFEST.json)

The candidate's historical status header is preserved. The independent review records the subsequently accepted scope.

## Reproduce

With existing Python 3, in this directory:

    python test_interval_arithmetic.py
    python verify_finite_pair.py

The verifier uses outward-rounded dyadic intervals with integer/rational acceptance comparisons. All matrix divisions must certify nonzero denominators. It has no external package dependency. The 13 arithmetic controls and direct verifier both passed. This is a hand-checked proof plus independently replayed exact-arithmetic certificate, **not a formal Lean proof**.

## Important limits

The 1 eV end onsite is a mathematical example; physical feasibility and the effective model's validity at that barrier are unestablished. The model class permits unrestricted scalar potentials and has zero internal dissipation. Its exact lead/disorder implementation has not been authenticated as Taylor's original executable model. The 0.6 μm length is excluded from Taylor Appendix II's modified energy-plus-length unsupervised variant. MEDA studies a different target.

Lead-dependent finite-system scattering labels and inverse-problem error-ball arguments are established ideas. This packet makes no historical novelty claim, no assertion of protected Majorana modes from a negative reflection determinant, and no allegation of an error in a published paper. See the prior-work check for the exact comparison and its limits.

The earlier accepted asymptotic packet is preserved unchanged. Root-isolation prototypes and unsuccessful lower-precision exploratory runs were not required by this rational finite certificate and are not included in this addendum.
