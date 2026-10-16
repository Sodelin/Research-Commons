# A fully rational finite-barrier pair in the declared fixed-lead nanowire model

Author: dot, working with Nolan. Date: 2026-10-16 UTC.
Status: candidate with an executed exact-outward-rounded certificate; independent review requested. The earlier asymptotic theorem remains unchanged.

## Result and strength

In the precise 60-site model below there are two **explicit rational potential profiles**, with the same leads, length, hopping, pairing and applied-field settings, such that:

- At the same label field B = 2 meV, the left reflection determinants obey
  -203/1000 < TV_minus < -202/1000 and 996/1000 < TV_plus < 997/1000.
  In particular they lie outside the positive classification margin ±1/10.
- For every common real B, the two lowest nonnegative closed-wire BdG energies differ by at most 9999/100000000 meV = 0.00009999 meV = 0.09999 μeV.
- Thus, on any common 512-setting menu, the vector of coordinatewise midpoint energies lies within 9999/200000000 meV = 0.049995 μeV of both energy vectors in the maximum norm. A classifier required to be correct for every admissible error vector with that bound cannot distinguish these two label classes from those energies alone.

This is a quantitative finite example. It does not prove equality of the two noiseless curves, an average-case error rate, or that this same finite barrier works for every smaller error tolerance. The accepted asymptotic theorem supplies the separate arbitrary-positive-error statement.

## Exact model and inputs

There are N = 60 sites of spacing 10 nm, with length convention Na = 0.6 μm. In spin-major, particle-hole-minor order the real 4 by 4 onsite block is

    H_jj = [[a_j, Δ, B, 0], [Δ, -a_j, 0, B],
            [B, 0, a_j, Δ], [0, B, Δ, -a_j]],

and the upper hopping block is

    T = [[-t, 0, -λ, 0], [0, t, 0, λ],
         [λ, 0, -t, 0], [0, -λ, 0, t]],

with lower block T transpose. Fix t = 501643/20000 = 25.08215 meV, λ = 5/2 meV, and Δ = 1/5 meV. This certifies **one rational hopping**, inside the earlier hopping interval. It is not a uniform certificate over that interval or an assertion that the physical mass conversion is exactly this rational number.

Both end onsites are M = 1000 meV. All 58 interior onsites are constant within each device:

    a_base  = 1234318662378001 / 25000000000000
    a_minus = a_base + (1/100)/1000²
            = 1234318662628001 / 25000000000000
    a_plus  = a_base + 100/1000²
            = 1234321162378001 / 25000000000000.

These fractions are the definitions of the parameters. Their displayed decimals are not measurement uncertainty. A root-isolation calculation suggested a_base, but **no root-isolation or root-continuation claim is a premise of this certificate**. In particular a_base is not asserted to equal the analytic crossing. The pair uses the same near-crossing offset mechanism as the earlier theorem, with its finite visibility now checked directly.

Each end is attached to its own identical semi-infinite normal lead with onsite zero, hopping -τ_z meV, and contact hopping -τ_z meV. At zero energy its exact retarded self-energy is -i I_4. Internal dissipation is zero. With Π_L and Π_R the end-site projections, set

    K = -H + i Π_L + i Π_R,
    G_LL = the left 4 by 4 block of K inverse,
    r_L = I_4 - 2 i G_LL,
    TV = det(r_L).

These are the fixed lead and normalization conventions of the accepted packet, not an unspecified scattering implementation.

## Exact visibility certificate

`fixed_lead_scattering.py` computes G_LL by backward block Schur complementation through all 60 sites. Every complex scalar reciprocal and every 4 by 4 elimination pivot must have an interval proof that its divisor is nonzero. Failure of such a check raises an exception and cannot be accepted as a visibility bound.

`dyadic_interval.py` represents each real coordinate by integer bounds divided by 2^1024. Rational conversion, multiplication and reciprocals round outwards using integer floor/ceiling; sums and negations are exact. Complex numbers use rectangles of these real intervals. The Gaussian-elimination and determinant formulas use only enclosing arithmetic. Induction through each operation proves that a successful result encloses the exact rational-input matrix expression. Floating-point values in the JSON are presentation only; every accepting comparison uses integers or fractions.

At zero energy TV is exactly real. Let J = σ_y tensor τ_y in this basis, represented by the real matrix

    J = [[0,0,0,-1],[0,0,1,0],[0,1,0,0],[-1,0,0,0]].

The checker verifies J² = I and J A J = -A for each real onsite and hopping basis matrix, so the full Hamiltonian satisfies J H* J = -H. The identity contact projections commute with J; therefore J K* J = -K and J G* J = -G. Consequently J r_L* J = r_L, and det(r_L) equals its complex conjugate. The computed imaginary rectangle also contains zero, as an arithmetic consistency check; that numerical inclusion alone is not the proof of reality.

The guarded checker verifies the strict rational bounds stated above, directly for both exact rational devices. Thirteen deterministic arithmetic controls cover rational conversion, signed real operations, zero-crossing squares, complex arithmetic/inversion, nonzero-divisor refusal, matrix inversion/determinants, the dual helper used by the diagnostic root finder, and the particle-hole basis identities. Passing these controls supports the implementation audit; it is not a substitute for inspection of the interval formulas or a machine-checked theorem proof.

## Exact common-field energy bound

For every B the two 240 by 240 closed-wire Hamiltonians differ only on their interior onsite τ_z coefficient. Hence

    ||H_plus(B) - H_minus(B)|| = a_plus - a_minus
                              = 9999/100000000 meV.

For Hermitian matrices, the variational eigenvalue perturbation inequality bounds each ordered eigenvalue change by this operator norm. Particle-hole symmetry pairs eigenvalues. Equivalently, the smallest singular value is the lowest nonnegative BdG energy, with zero retained at a crossing. Either formulation gives the displayed pointwise bound, uniformly in B and hence on the full common field menu. This argument requires no numerical diagonalization and no refitting of a potential separately at each field.

The midpoint error statement is immediate: the same reported energy vector is within half the displayed bound of either device. Since their labels are opposite beyond the declared margin, no single deterministic label assignment to that common report is correct for both. This is a worst-case bounded-error identification obstruction, not a statement about an actual instrument's error distribution or a noncommuting-observable uncertainty relation.

## Physical and source limits

M = 1000 meV is a 1 eV onsite barrier in an effective low-energy model. It is an explicit mathematical example, **not established experimental feasibility or validity of that effective model at such a barrier**. The potential range remains unrestricted in the model class; this finite example does not establish nonseparation under a smaller specified disorder cap, a contact-floor condition, or positive internal broadening.

The original Taylor implementation's lead convention, disorder-generation details and exact executable source remain unauthenticated. The 0.6 μm wire is also outside Taylor Appendix II's modified energy-plus-length unsupervised variant, which excludes lengths below 1 μm. This certificate therefore does not declare an error in that paper, a counterexample inside every one of its data branches, or a result about MEDA's different target.

## Attribution and novelty boundary

The physical lead-dependence mechanism is established prior work; Araya Day et al., Section 3.1, analyze the competition between Majorana splitting and lead-induced widths. The variational spectral bound and indistinguishable-error-ball argument are classical. This note adds a reproducible rational finite-pair certificate for our declared microscopic model. No claim of historical novelty or priority for that exact construction has been established by a complete literature review.

- Earlier exact model, asymptotic proof and independent review: https://github.com/Sodelin/Research-Commons/tree/caf7d4531c3027d19d0e899bee7129f672d1f342/research/2026-10-16-nanowire-fixed-lead-nonseparation
- Lead-dependence prior, Araya Day et al.: https://arxiv.org/html/2504.01069v1
- Taylor, Pan and Das Sarma, source and variant limits: https://arxiv.org/html/2512.13825v2

## Reproduction

With an existing Python 3 installation and these own-code files in one directory:

    python test_interval_arithmetic.py
    python verify_finite_pair.py

No packages, network access, fitting or external solver are required. Do not use Python's optimized (-O) mode; the verifier explicitly refuses it. `FINITE-PAIR-RESULT.json` records the exact inputs, rational output intervals, source hashes and bounds. The root-finding prototypes and their earlier failed low-precision runs are diagnostic provenance only and are not in the trusted computation for this finite pair.
