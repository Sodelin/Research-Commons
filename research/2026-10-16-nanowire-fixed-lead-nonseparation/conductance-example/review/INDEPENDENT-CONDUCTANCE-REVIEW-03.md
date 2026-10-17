# Independent review of the finite-pair conductance certificate

**Date:** October 17, 2026, 00:23 UTC. **Reviewer:** dot, working with Nolan, in a separate review pass from the candidate's construction. **Verdict:** scoped hand/source review and exact replay PASS, with one citation-locator correction below. No mandatory mathematical correction was found.

## Exact object and execution evidence

Reviewed candidate `CONDUCTANCE-SEPARATION-CANDIDATE-03.md`, SHA256 `123dab191b5e37e2704c6b3471ee2545e1507c6556afd29990e6e752b37ce78a`.

The ten files listed in its manifest were checked against their recorded sizes and hashes. All five Python files were read before execution. Unchanged source copies were placed in a separate review directory. With ordinary Python 3, assertions enabled:

- `python test_interval_arithmetic.py`: 13 tests passed, exit 0.
- `python verify_conductance.py`: all rational-range, separation, decision-threshold, block-residual and incoming-column unitarity guards passed, exit 0.
- The resulting `CONDUCTANCE-RESULT.json` matched the candidate result byte for byte: SHA256 `9e1eb9198562c8696d005819c6ffb8aa40d236c5afa4d3ff80d8ce3b96906647`.

`REPLAY-RECEIPT.json` records the exact interpreter, times, source hashes and log hashes. These are independent executions of the same inspected checker, not a second implementation of the numerical calculation. Decimal output is presentation only; the acceptance comparisons use exact rational endpoints.

## Source and convention check

The accessible final primary article, [Rosdahl, Vuik, Kjaergaard and Akhmerov, PRB 97, 045421 (2018)](https://pure.tudelft.nl/ws/portalfiles/portal/46877558/PhysRevB.97.045421.pdf), Eqs. (3)–(5), defines outgoing sector/lead first and incoming sector/lead second. Its current direction is from the scattering region into a terminal. Reversing that direction gives the candidate's local expression `2 − R_ee + R_he` and nonlocal expression `T_he − T_ee`. The source's electron-mode count is two in the declared spin-degenerate normal lead; an additional spin or Nambu factor would be incorrect.

**Citation correction:** these equations are on article page **045421-3**, which is **PDF page 4** when the TU Delft cover sheet is counted (zero-based page index 3). The candidate says 045421-2 / PDF page 3. Its formula and polarity mapping are correct; the locator should be corrected in the accompanying README or a dated erratum without silently changing the reviewed bytes. The equation text and article footer were read; a separate screenshot request was unavailable, so no visual-PDF verification is claimed.

The source supplies the transport formula, not a validation of this particular device or its experimental feasibility.

## Mathematical and implementation checks

1. **Same finite devices.** The source uses exactly the previously reviewed rational hopping `501643/20000`, end onsite `1000`, central base `1234318662378001/25000000000000`, and offsets `1/100000000` and `1/10000`. The onsite and hopping blocks match the finite-pair model. No new tuning or per-field refitting enters the calculation.

2. **Channel indexing.** In the actual spin-first matrix ordering, τz has diagonal `(1,−1,1,−1)`. Electron indices `(0,2)` and hole indices `(1,3)` are therefore correct. The Frobenius sums use outgoing rows and incoming-electron columns. Basis changes confined within electron and hole sectors leave these sums invariant.

3. **Lead normalization.** At E = 0 the stated unit-hopping normal half-chain has retarded surface Green value −i. Contact hopping −τz gives self-energy −iI and broadening 2I. Thus the stated normalized formulas `r = I − 2i G_LL` and `s = −2i G_RL` agree with the pinned scattering convention, up to sector-preserving contact phases. No finite-energy wide-band approximation is assumed.

4. **Block solve.** The right-to-left Schur recurrence uses `U = −T`, `L = Uᵀ`, and diagonal blocks of `−H + iΠL + iΠR`. The reconstructed first inverse block column obeys `G_jL = −S_j⁻¹ L G_(j−1)L`. Guarded pivots justify each inverse. All 60 block equations are checked. Enclosing zero in a residual is a diagnostic consistency check; correctness comes from the interval enclosure and the algebraic elimination identities.

5. **Conservation.** The reflection block alone is not assumed unitary. The identity `G − G† = −2i G†ΠG` implies `r†r + s†s = I₄` for the entire incoming left-lead column of the two-lead scattering matrix. All sixteen entries are checked. The separate probability sum yields `g_LL = 2 R_he + T_ee + T_he`, also checked. This is appropriate only for the declared loss-free, fixed-condensate-potential model.

6. **Interval kernel.** Integer scaling, endpoint multiplication, reciprocal guards, complex division and square enclosures were inspected. They preserve containment with outward rounding. Every inverse requires a certified nonzero pivot; optimized Python is explicitly rejected by the verifier. The kernel and inherited controls are unchanged from finite-pair packet 02. The controls exercise arithmetic and basis conventions, not physical model admission.

7. **Decision claims.** The certified open rational ranges imply local separation greater than `1205/1000` and nonlocal separation greater than `787/1000`, in units e²/h. Consequently the stated strict half-gap error radii suffice. The alternative explicit thresholds also check: local threshold `3/5` with absolute error at most `1/2`, and nonlocal threshold `−2/5` with absolute error at most `3/10`. These statements concern the two fixed devices only.

## Accepted scope and remaining limits

The result supplies a concrete ideal readout that separates the finite pair whose energy curves share a bounded-error report. It is a useful paired measurement benchmark. It does not establish uniform identification over the entire source class, the asymptotic sequence's conductance behavior, original Taylor implementation admission, protected Majorana modes, or historical novelty.

The acceptance requires grounded superconducting condensate, zero temperature, zero bias, no internal dissipation, the fixed rational parameters and the declared lead convention. It does not cover a floating island, calibration error, parameter drift, finite-temperature averaging, fabrication feasibility, or validity of a 1 eV onsite barrier in an actual material. The gap is in conductance units, not an experimentally demonstrated accuracy budget.

No Lean kernel proof or external domain-expert review is claimed. The original candidate status remains historical; this review supplies the subsequent scoped acceptance.
