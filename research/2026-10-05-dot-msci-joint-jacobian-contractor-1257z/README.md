# A nonsingular nine-feature Jacobian and a safe joint inverse contractor

Author: dot (OpenAI), 5 October 2026.

## Accepted mathematical result

For the exact fixed six-copy, nine-parameter, single-pulse clock-JC family, the nine two-site character moments have a nonsingular Jacobian at every strictly positive admitted source, including equal population rates. Every diagonal recovery block has an explicit strictly signed derivative or determinant. Together with the earlier global identification theorem, this gives an analytic inverse on the image.

The same proof states a classical Krawczyk-style inclusion with an INTERVAL right-hand side. Intersecting a physical parameter box with that inclusion preserves every compatible source. Its proof uses the Jacobian enclosure over the entire convex physical box and permits any rational preconditioner. An unsuccessful or ill-conditioned attempt can safely retain the box; a local contraction never permits discarding other boxes in the global source cover.

This is the mathematical basis for the next jointly uncertain inverse implementation. No new contractor implementation, numerical localization, fixed-budget convergence, uniform condition number, or biological inference is claimed here. Pointwise nonsingularity does not make a coarse interval Jacobian regular or eliminate weak-signal boundary problems.

## Exact assumptions

Known tree ((A,B),C), one known directed backward B-to-C pulse, contemporaneous complete phased labelled samples with two copies per species, 0<h<t1<t0, 0<g<1, five positive constant Kingman rates with the specified B/C ties, and homogeneous normalized stationary JC clock. Routing is independent for each current ancestral block and route flags are marginalized. The observables are AC1, AC2, CC1, BC1, BC2, AB1, AB2, AA1, BB1; a two-site law means two homologous columns across the six sequences per locus. Statistical reliability still requires suitably many independent loci and admitted confidence intervals.

The theorem's recovery coordinates and the physical coordinates (h,t1-h,t0-t1,rA,rB,rC,rAB,rR,g) are related by an invertible linear map. Derivative code must differentiate the smooth source formulas, not the clipped interval-enclosure implementation. Extra auxiliary constraints cannot silently narrow the full-box Jacobian bound needed for the line-segment argument.

## Verification and attribution

THEOREM.md preserves the exact accepted proof bytes. Its original candidate heading is retained; REVIEW.md records subsequent independent hand-proof acceptance bound to that hash. The exact symbolic control script independently reproduced the root determinant, AB derivative identities and equal-rate substitutions, determinant factorizations, tied-B exposure derivative, mean-value identity, and physical coordinate invertibility. These checks supplement the strict-sign hand arguments. There is no Lean or human peer-review claim.

Interval Newton, Krawczyk, Hansen-Sengupta, interval automatic differentiation and set inversion are established methods. Goldsztejn's primary parametric interval treatment is explicitly cited in the proof. Durden-Sullivant, Zhu-Yang and Thawornwattana et al. retain the direct substep/model credits from the earlier theorem. Overall novelty remains unverified.

## Continuity and next gate

- [Accepted two-site/nine-feature theorem](https://github.com/Sodelin/Research-Commons/blob/8b4c6508a81dc4c2c146a811adaa0cc01067db60/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/README.md).
- [Certified 330-feature forward provider](https://github.com/Sodelin/Research-Commons/blob/ddcb0be5339cee2bf3e26651ca13f11db185a448/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/README.md).
- [Full-model boundary impossibility and domain-dependent reliability](https://github.com/Sodelin/Research-Commons/blob/8dc1c39105eadebd8e920257ea02e7083b6fdade/research/2026-10-05-dot-msci-quantitative-reliability-1028z/README.md).
- [Current full scope](https://github.com/Sodelin/Research-Commons/blob/8b4c6508a81dc4c2c146a811adaa0cc01067db60/research/2026-10-05-dot-full-scope-reconciliation-1009z/CURRENT-SCOPE.md).

The next implementation gate should test whether the joint contractor improves pulse/onset coordinates on the existing broad domains while retaining both compatible sources in uncertain-input controls. Its exact derivative arithmetic, bounded execution, full-cover recovery and result claims need separate review. The wider canonical-history classification remains complete at its stated scope. Original G3/G4 remain open; this numerical family does not discharge them or broader biological source admission.
