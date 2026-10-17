# Independent review of the conditional thermal observation adapter

17 October 2026, approximately 02:02 UTC. dot (OpenAI), independent mathematical review for Nolan.

**Verdict: scoped hand-proof PASS. No mandatory mathematical correction found.**

Reviewed source: `THERMAL-OBSERVATION-ADAPTER-CANDIDATE-08.md`.

Reviewed SHA-256: `4deeec93e55184c4c254ace14c3623453b2ad5ae07d34e2fdfb848819dcf92a8`.

The file digest and complete text were read before review. The candidate was not edited. This receipt accepts the conditional inequalities and the exact effective-scattering example as stated. It does not supply experimentally validated constants, a microscopic realization in the fixed Rashba family, novelty, or Lean verification. No numerical experiment or code-based proof check was performed for this review.

## 1. Kernel, moments and window terms

For positive theta, the kernel is nonnegative and even. Integrating its hyperbolic-secant-squared expression gives total mass one and

`p(W) = 2/(1 + exp(W/theta))`.

The survival-function identities give the full first moment `2 theta log 2` and second moment `pi^2 theta^2/3`. The draft's alternating-series argument for the second moment is valid: the finite geometric sums are bounded in absolute value by `2 exp(-u)`, and multiplication by `u` provides an integrable dominating function.

Integration by parts gives

`m1(W) = integral_0^W p(u) du - W p(W)`

and hence precisely the displayed truncated first-moment formula. In particular `m1(0)=0`, `p(0)=1`, and both truncated moments are nonnegative and bounded by their full counterparts. There is no missing factor of two.

## 2. Two-sided and one-sided errors

Bounds (A) and (B) follow from the first and second kernel moments. The curvature argument only needs the stated quadratic remainder; its odd linear term integrates to zero. Evenness of the conductance itself is unnecessary.

Bounds (C) and (D) correctly separate the symmetric inner window from the outer direct-difference envelope. The local linear term cancels only inside the window; the draft does not incorrectly extend a local Taylor estimate into the tails. Taking `D=M` is valid when both conductance values lie in `[0,M]`. A zero-energy channel count alone does not justify that envelope at every energy, as the candidate explicitly states.

For (E), nonnegativity outside the window permits discarding the outer contribution, while the inner integral is at least

`h(0)(1-p(W)) - L m1(W)`.

The denominator is positive exactly when `W>0`. The identical argument with the quadratic remainder proves (F). These one-sided estimates genuinely avoid a global upper tail envelope; they still require nonnegative local conductance and a justified inner-window variation bound. They do not apply automatically to signed nonlocal conductance.

## 3. Measurement and Hamiltonian mismatch

The inequality `h_theta(0) <= y + eta` is the correct direction for obtaining an upper bound on `h(0)`. The independent target mismatch `|f(0)-h(0)| <= DeltaH` is correctly added after the division by `1-p(W)` in the one-sided formula. Putting it into the numerator would describe a different premise.

The resulting `f(0) <= U`, followed by `Q0 >= 1-f(0)`, proves `Q0 >= 1-U`. The strict and closed threshold statements are correct. An inconsistent negative upper bound cannot be interpreted as a determinant exceeding one. Failure of the sufficient positive-sign test only requires abstention.

The target reflection must still have canonical particle-hole symmetry, be contractive, and produce the conductance used in the formula, with the same electron-channel convention. Finite-temperature averaging is not a new reflection matrix. The temperature-uncertainty supremum is valid when each constituent bound, including its model-mismatch budget, is justified for the corresponding admitted temperature; no unproved monotonicity is used.

## 4. Exact effective-scattering obstruction

For `r_Gamma(E) = (E I + i Gamma tau_x)/(E+i Gamma)`, direct multiplication gives unitarity for every real energy. Conjugation at `-E` and exchange by `tau_x` reproduce `r_Gamma(E)`, so the energy-dependent particle-hole relation is exact.

Its eigenvalues in the `tau_x` basis are `1` and `(E-i Gamma)/(E+i Gamma)`. At zero energy, `r_Gamma(0)=tau_x` and the determinant is `-1`. The continuation has no upper-half-plane pole; the nonconstant eigenvalue has modulus at most one there. This supports the candidate's passive effective-scattering description, without proving a particular microscopic implementation.

The one-channel local conductance is exactly

`1 - |r_ee|^2 + |r_he|^2 = 2 Gamma^2/(E^2+Gamma^2)`.

Its area is `2 pi Gamma`. Combining this with `sup w_theta = 1/(4 theta)` gives the uniform-in-bias upper bound `pi Gamma/(2 theta)`. The identity reflector has zero conductance and determinant `+1`, so the midpoint of the two thermal curves lies within `pi Gamma/(4 theta)` of each. For every fixed positive temperature and positive uniform error radius, a sufficiently small positive Gamma therefore gives overlapping possible reports with opposite zero-energy determinant signs. Identity spectator channels preserve this conclusion for every finite positive channel count.

This is a stability obstruction over the stated effective class. It is not exact noninjectivity of noiseless convolution and does not establish admission to the fixed-hopping Rashba model. The draft preserves both boundaries. Its missing regularity is real: at `E=Gamma`, the anchored difference quotient `|h(E)-h(0)|/|E|` equals `1/Gamma`, and `|h''(0)|=4/Gamma^2`. No fixed positive window admits uniform such constants as Gamma tends to zero.

## 5. Primary-source and physical scope check

- [Taylor et al., arXiv:2607.14949v1, Section II, Eq. (3)](https://arxiv.org/html/2607.14949v1) was inspected directly. It uses the derivative-of-Fermi convolution. The same section changes the parent superconducting gap between temperatures. The candidate correctly retains a separate frozen-Hamiltonian mismatch rather than treating every warm/cold comparison as one unchanged spectrum.
- [Setiawan et al., arXiv:1708.09039v2, Section III.1, Eq. (8)](https://arxiv.org/html/1708.09039v2) was inspected directly. It gives the Lorentzian/Fermi-kernel expression and limits its nanowire scaling interpretation to temperature and tunnel broadening small relative to the induced gap. The exact effective matrix in the candidate is proved independently; it is not asserted to be an exact microscopic nanowire formula at all energies.

The source treatment is appropriate: established thermal physics is credited; no trained-model performance is refuted; and no historical novelty or paper error is inferred. A coarse bias grid, fitted width, or average prediction score does not furnish the necessary worst-case regularity or model-drift budget. The remaining practical obligation is to establish those budgets for an admitted device and measurement protocol.
