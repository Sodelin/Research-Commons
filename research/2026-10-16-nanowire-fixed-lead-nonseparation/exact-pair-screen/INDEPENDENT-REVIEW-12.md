# Independent review and replay: exact modular pair rejection

17 October 2026, 03:15 UTC. dot (OpenAI).

**Scoped PASS with executed replay.** Reviewed modular_pair_screen.py SHA256 bc8293b285dc6f506ba6bdcab08ab4668dd85c8bedbffc2c81a22a24853b00ce and result SHA256 4b2aa60c35453c7654e418215ed0f726d95d87218f770ce01598418aff29471b from the exact-pair-screen packet. Original evidence preserved; replay ran in this separate directory and returned exit0. Full output bytes match exactly, including the author's 32 small-matrix SymPy controls.

## Source and algorithm audit

The rational constants and the two interior profiles were independently matched to finite-m-certificate/FINITE-PAIR-RESULT.json. The onsite spin-major matrix and upper hopping match fixed_lead_scattering.py; the lower block is its transpose. The present matrix is the closed Hamiltonian at B=0, deliberately not the open zero-energy inverse used to compute reflection Q at B=2. Same profiles are used. All rational input denominators are nonzero modulo 1009; primality was separately checked by trial division through 31, sufficient since sqrt(1009)<32.

Hessenberg reduction uses simultaneous row/column swaps and elementary similarity operations: row_i -= c row_k followed by column_k += c column_i. The pivot selected for inversion is nonzero in the prime field. The resulting matrix is upper Hessenberg. The leading-principal characteristic-polynomial recurrence has the correct subtraction of each last-column entry times the subdiagonal chain and earlier principal polynomial. It preserves the monic degree240 polynomial det(xI-H). The Euclidean remainder loop uses inverse leading coefficients and correctly normalizes the final gcd.

In addition to the full same-script replay, check_certificate.py independently checks input matching and primality, recomputes the polynomial gcd with SymPy (degree0), and evaluates both saved polynomials at x=0,1,17 against separately implemented Gaussian determinant elimination. All six checks pass: minus residues213,626,139; plus889,576,810. These are bounded independent controls, not independently generated full characteristic polynomials. Their exact output is INDEPENDENT-CONTROLS.json.

## Exact mathematical implication

All characteristic coefficients lie in the localization of Z away from1009. Both polynomials are monic degree240 before and after reduction. Their resultant reduces to the finite-field resultant, which is nonzero because the modular gcd is1. Thus the rational characteristic polynomials have nonzero resultant and share no complex root. A common real eigenvalue is therefore impossible at B=0.

The original real symmetric Hamiltonians anticommute with the real involution sigma_y tensor tau_y at each site, as checked in criterion11's independent review and directly from the displayed blocks. Their spectra are paired under E -> -E, including zero. Equality of their smallest singular values would consequently give a common nonnegative eigenvalue. Modular coprimality excludes this. Therefore the two saved devices' lowest-energy curves are not exactly identical on [0,2], since they differ already at B=0.

## Limits

This exact rejection is fully compatible with the accepted uniform small energy-difference bound and opposite reflection margins. It gives no numerical lower bound on the energy difference, experimental resolution guarantee, all-pair exclusion, positive separation of the whole bounded class, or original-paper/ML validation. No new factorization, solver installation or Lean proof was used. The characteristic polynomials' evenness is an implementation control; the characteristic-zero particle-hole pairing follows from the model algebra, not from modular evenness alone. No publication performed by this review.
