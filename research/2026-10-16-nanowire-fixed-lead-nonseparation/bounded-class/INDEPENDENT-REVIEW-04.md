# Bounded-class boundary: independent hand-review receipt

2026-10-17 UTC. dot (OpenAI), working with Nolan.

Reviewed `BOUNDED-CLASS-IDENTIFICATION-BOUNDARY-04.md` after the Section 6 wording correction, SHA256 `7479c30f82f9fe63aed562e752c745483eb1fe7740572259693525981a3bf0c1`. This differs from the originally supplied hash because the author corrected whole-box equivalence to membership of the two particular profiles.

## Verdict: PASS within declared finite-model assumptions

No defect found in the inverse estimate, compact classification characterization, grid approximation or real-algebraic decision reduction. This is a hand-proof review, not execution of a numerical solver, SMT decision, quantifier elimination, or formal build. No novelty or experimental-admission acceptance is given.

Specific checks:

1. The hopping obeys TT†=τ²I, because the scalar hopping and iσ_y terms have cancelling cross terms. Both propagation directions therefore have inverse hopping norm 1/τ. The imaginary quadratic form bounds each endpoint by sqrt(ε/γ). The recurrence with R=2+(C0+γ)/τ absorbs the forcing ε/τ through u. Applying it independently from both ends yields exponent min(j−1,N−j), at most d=floor((N−1)/2)=29 for N=60. Summing site squares yields sqrt(N)R^d u. Splitting at ε=τ²/γ gives exactly the stated minimum ρ, including equality cases.
2. For A=1000, fixed t=25.08215 and γ=1, τ>25, C0+γ=1003.2, hence R<2+1003.2/25=42.128<43. Also τ²>625. Thus both entries in the minimum exceed or equal 1/(240·43^58), so the rational weakening is valid.
3. The resolvent and contraction determinant perturbation bounds give 8γρ^-2 times the potential maximum-norm change. Opposite margins differ by at least 2m, producing mρ²/(4γ). This is only a parameter-separation estimate, as the source states.
4. F is jointly Lipschitz with the displayed constants. Compactness of C and continuity of Q make both closed-margin classes compact. Their curve-image distance is attained. With nonempty classes, equality of opposite curves is equivalent to zero distance. Closed radius-ε balls meet exactly at curve distance <=2ε; the midpoint argument includes ε=0. Consequently the strict condition δ_full>2ε is correct, including the zero-error case.
5. For each fixed pair the absolute curve difference is 2-Lipschitz. Endpoint-inclusive maximum gap h gives covering radius h/2. The pointwise bound max_grid<=sup<=max_grid+h survives minimization over the SAME opposite pair domain, proving δ_grid<=δ_full<=δ_grid+h. Finite-grid extraction therefore uses a genuine positive strict margin, not an assumed injectivity theorem.
6. H is real symmetric in the specified basis. For e>=0, PSD(H²−e²I) plus its zero determinant uniquely selects sqrt(min spectrum(H²))=s_min(H), including zero crossings. All principal minors, rather than just leading ones, give the finite PSD encoding. KG=I has a unique solution by the inverse estimate. Algebraic constants and finite semialgebraic C make the resulting formulas first-order real algebraic.
7. The two potential vectors and their label constraints stay outside the universal field quantifier; only their uniquely determined energies vary inside it. Finite and full-menu overlap formulas are therefore faithful. Empty classes are explicitly separated before the minimum is defined and can be tested by the same real-algebraic framework. No decidability claim for arbitrary closed non-semialgebraic C is made.
8. The prior rational-pair certificate states end onsites 1000 and interior onsites near 49.37275, with common offset 2t−1=49.1643. Thus both particular profiles lie in A=1000 and Vmax=950.8357. The corrected text no longer equates the two whole boxes. The existing energy difference 9999/100000000 and midpoint half thereof justify the bounded-box obstruction at and above the stated closed error radius; this review did not rerun that prior arithmetic certificate.

Keep the stated limitations: bounded-class restriction; no determination of exact equal-curve collisions in a substantial class; no feasible QE runtime assertion; no original Taylor implementation admission; no evidence of physical feasibility for the high barrier.
