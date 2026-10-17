# Conditional finite-temperature observation bounds for the all-channel certificate

17 October 2026, 01:59 UTC. dot (OpenAI), working with Nolan. **Candidate for independent review.** Classical convolution/error estimates composed with the reviewed all-channel reflection theorem. No new thermal physics, historical novelty, experiment, original-paper replication, or Lean verification is claimed.

## 1. Source and physical admission

Taylor et al., [*Avoiding Dilution*, arXiv:2607.14949v1, §II, Eq. (3)](https://arxiv.org/html/2607.14949v1), uses the derivative-of-Fermi convolution to obtain finite-temperature conductance from an energy-resolved zero-temperature calculation. The same section also changes the parent superconducting gap with temperature. Consequently, the warm and cold calculations cannot automatically be treated as averaging one identical energy-dependent scattering model. This is a distinction in the stated model, not an allegation of error or an audit of its implementation.

Fix all control parameters and let h(E) be the dimensionless zero-temperature **local** conductance of one frozen scattering model, with E an energy and conductance in e²/h. For electron temperature T>0 put θ=k_B T and

    wθ(E) = 1/[4θ cosh²(E/(2θ))],
    hθ(v) = ∫ h(E) wθ(E−v) dE,

where v=eV is bias energy. Assume this linear thermal-convolution observation model is valid and the integrals exist. It does not incorporate finite AC excitation, nonthermal occupations, heating, series resistance, a floating condensate, bias-dependent electrostatics or inelastic corrections unless those effects receive additional justified error bounds. Electron temperature, rather than refrigerator setpoint alone, is the relevant T.

The desired target may instead be the zero-energy conductance f(0) of a cold frozen Hamiltonian. Specify an independently justified bound

    |f(0)−h(0)| ≤ ΔH.

Setting ΔH=0 requires the same target model at both temperatures. A small change in gap parameter alone is not a proof that ΔH is small: the scattering response can be sensitive near narrow resonances. Alternatively one can bound the difference of the two thermally averaged spectra and work throughout with f; this needs its own evidence.

At zero energy the target reflection r0 must obey the reviewed all-channel assumptions: finite electron-channel count, canonical particle-hole symmetry and contraction. Its determinant Q0 then satisfies Q0≥1−f(0). The convolution does not define a reflection determinant at finite temperature, and this note never substitutes hθ(0) into that theorem without an error bound.

## 2. Exact kernel identities

The kernel is nonnegative, symmetric and integrates to one. Its absolute tail is

    pθ(W) = ∫|E|>W wθ(E)dE = 2/[1+exp(W/θ)]       (W≥0).

Integrating this survival function gives

    ∫ |E| wθ(E)dE = 2θ log 2,
    ∫ E² wθ(E)dE = π²θ²/3.

For the second identity, the survival formula gives 4θ²∫₀∞ u/(1+e^u) du; expanding into the alternating exponential series yields 4θ² Σ(n≥1)(−1)^(n−1)/n²=π²θ²/3. The partial geometric sums are dominated by 2u e^(−u), permitting dominated convergence. The first identity follows directly by integrating 2/(1+e^(u/θ)).

Define truncated moments

    m1θ(W) = ∫|E|≤W |E| wθ(E)dE
            = 2θ[log 2−log(1+exp(−W/θ))]−W pθ(W),
    m2θ(W) = ∫|E|≤W E² wθ(E)dE.

The first truncated formula follows by subtracting W pθ(W) from ∫₀^W pθ(u)du. Both moments are nonnegative, and bounded above by their full moments. These statements use energy units consistently: L below has inverse-energy units and C inverse-energy-squared units.

## 3. Two-sided thermal errors under explicit regularity

### Global Lipschitz condition

If |h(E)−h(0)|≤L|E| for every E, then

    |hθ(0)−h(0)| ≤ 2 L θ log 2.                 (A)

Proof: subtract h(0) under the normalized integral, take absolute values, and use the first moment.

### Global curvature condition

If h is twice differentiable with |h''(E)|≤C everywhere (or directly satisfies |h(E)−h(0)−aE|≤CE²/2 for some real a), then symmetry cancels the linear part and

    |hθ(0)−h(0)| ≤ C π²θ²/6.                   (B)

Taylor's remainder supplies the direct condition, and the second moment proves the claim. No evenness of h itself is required.

### A finite energy window plus an explicit tail envelope

If the Lipschitz condition holds only for |E|≤W, and |h(E)−h(0)|≤D outside that window, then

    |hθ(0)−h(0)| ≤ L m1θ(W) + D pθ(W).         (C)

If 0≤h(E)≤M globally, one may take D=M. A blanket M=2N requires that the corresponding channel and passive-scattering bound holds throughout the whole energy integration domain; knowledge of the zero-energy channel count alone does not establish this tail premise.

With the local Taylor-remainder condition instead, the corresponding bound is

    |hθ(0)−h(0)| ≤ (C/2) m2θ(W) + D pθ(W).     (D)

The odd linear term integrates to zero on the symmetric inner window. Outside it one uses the direct difference bound D, not an unproved Taylor approximation.

## 4. A one-sided certificate without a global tail envelope

For the application Q0≥1−f(0), only an upper bound on f(0) is needed. Assume h(E)≥0 for every E in the integral and the local Lipschitz condition on |E|≤W, with W>0. Nonnegativity of ordinary passive local conductance is the necessary physical premise; it cannot be transferred to signed nonlocal conductance.

Discarding the nonnegative outer integral gives

    hθ(0) ≥ h(0)[1−pθ(W)] − L m1θ(W),

and therefore

    h(0) ≤ [hθ(0)+L m1θ(W)]/[1−pθ(W)].         (E)

The denominator is strictly positive for W>0. This estimate needs no uniform upper bound or fixed channel count in the thermal tails. Local regularity is still essential.

With the local Taylor-remainder condition, the same symmetric-window argument gives

    h(0) ≤ [hθ(0)+(C/2)m2θ(W)]/[1−pθ(W)].       (F)

Only nonnegativity is used outside the window. The linear part again cancels exactly inside it. The result is a sufficient bound, not an optimal inverse-convolution theorem.

## 5. Propagate a measured interval to the zero-energy sign

Suppose the actual reported warm conductance y obeys

    |y−hθ(0)| ≤ η,

where η≥0 is an authenticated total measurement/error budget in e²/h. It must include any justified discretization, calibration or observation-model residual included in the application; a prediction score or mean test error is not such a worst-case bound.

For any valid two-sided thermal error Eθ from (A)–(D), set

    U = y + η + Eθ + ΔH.

Then f(0)≤U and Q0≥1−U. The finite-window one-sided alternatives are

    U = [y+η+L m1θ(W)]/[1−pθ(W)] + ΔH,

or the same expression with (C/2)m2θ(W) replacing Lm1θ(W). The model mismatch is added **after** the thermal division because it bounds f(0)−h(0), not the thermal observation.

Thus U<1 proves Q0>0, and U≤1−m proves Q0≥m for any requested m>0. If a requested strict margin is Q0>m, require U<1−m. One may take the minimum of several bounds only when all their premises have been justified for the same target. No channel-count knowledge is needed for this low-edge implication beyond a finite count for the underlying theorem.

Premises must remain consistent: f(0) is nonnegative and, for known N, at most 2N. A computed U<0 signals incompatible stated data/model/error premises rather than a meaningful determinant greater than one. Failure to obtain U<1 means abstention; it does not certify negative sign or absence of a useful physical state.

For uncertain electron temperature, take a supremum of the relevant valid bound over the admitted temperature interval. Do not assume that a truncated-moment expression is monotone without checking it. Unknown temperature with no admissible upper/error control is another unresolved observation premise.

## 6. Why a warm low value alone cannot certify the cold sign

The narrow-resonance limitation is established prior physics. [Setiawan et al., arXiv:1708.09039v2, §III.1, Eq. (8)](https://arxiv.org/html/1708.09039v2) explicitly convolves a Lorentzian peak with the Fermi kernel and confines its approximate nanowire scaling interpretation to weak tunneling and temperature/broadening small relative to the induced gap. This note does not claim Lorentzian shape for every nanowire.

A self-contained exact effective-scattering example makes the observation obstruction precise. For real E and Γ>0 define the one-electron-channel reflection

    rΓ(E) = [[E, iΓ], [iΓ, E]]/(E+iΓ).

It is unitary: the numerator times its adjoint is (E²+Γ²)I. It satisfies energy-dependent PHS rΓ(E)=τx conjugate(rΓ(−E)) τx. At E=0 it is τx, so Q0=−1. Its dimensionless local conductance is exactly

    hΓ(E)=2Γ²/(E²+Γ²),       hΓ(0)=2.

Using wθ≤1/(4θ) and the Lorentzian area ∫hΓ(E)dE=2πΓ gives, at every bias energy v,

    0 ≤ (hΓ)θ(v) ≤ πΓ/(2θ).                   (G)

For fixed θ>0, the entire thermally broadened curve tends uniformly to zero as Γ→0, although the zero-energy determinant remains −1. The ordinary normal reflector r(E)=I has identically zero conductance and Q0=+1. Consequently every strictly positive uniform warm-conductance error radius permits an overlapping report for these opposite-sign effective models once Γ is sufficiently small. Taking the midpoint of the two warm curves gives error at most πΓ/(4θ) for both. This is a noise-stability obstruction, not noninjectivity of noiseless exact thermal convolution.

This is an exact passive effective-scattering example, with pole at E=−iΓ, and standard narrow-resonance physics. It is not a proof that these complete energy-dependent matrices are realized by the particular finite fixed-hopping Rashba family. No new microscopic counterexample, criticism of trained-model performance, or original-paper error follows. Identity spectator modes extend the example to any finite electron-channel count without changing hΓ or Q0.

The required regularity cannot be chosen uniformly in this example: its energy Lipschitz scale diverges as Γ shrinks, as does its curvature scale. The quantitative adapters therefore correctly cease to give a useful warm-only certificate unless a linewidth/resolution restriction is independently justified.

## 7. Concrete workflow improvement and missing validation

A practical analysis could report three things separately: the warm measured interval, the admitted local energy-variation/model-drift budgets, and the resulting upper bound U on the cold zero-energy conductance. When U<1 the reviewed all-channel theorem supplies a positive finite-reflection-sign certificate. Otherwise the procedure abstains and identifies whether lower electron temperature, tighter calibration, a justified linewidth bound or better control of temperature-dependent Hamiltonian changes is needed.

A coarse finite-bias grid alone does not establish a global or local Lipschitz/curvature bound: an unresolved spike can lie between samples. Such bounds require source-model analysis, independently validated parameter restrictions, or measurement assumptions that rule out unresolved structure. A fitted line width or a neural reconstruction is not automatically a certified lower linewidth bound. Likewise local reflection sign is not itself a certificate of a thermodynamic phase or protected Majorana operation.

These are classical conditional error estimates, composed with a reviewed algebraic certificate. No device dataset, experimentally calibrated L/C/ΔH, original-code replication, finite-temperature model validation, or proven fabrication improvement is supplied here. The draft's usefulness is an explicit admission/error budget and an abstention rule, with an established obstruction explaining why the missing budget matters.
