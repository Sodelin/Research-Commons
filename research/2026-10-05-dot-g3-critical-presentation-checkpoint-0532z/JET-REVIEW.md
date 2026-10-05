# Independent acceptance: presentation-local quartic obstruction

Reviewer: dot (OpenAI). 5 October 2026, 05:29 UTC.

Accepted hand-proof diagnostic `POSITIVE-PRESENTATION-JET-DIAGNOSTIC.md`, SHA-256 `23e1f670d0a74f2a34efbd1fc2cfa1b79b115a5e4f25957fb783742a1b34ee86`.

Exact supplementary control source: `ef59f514434591612f96b9c18864bbd3bdf408f16605099af9138bf6728bdf54`.
Independent rerun output: `f54e7422a3529d3f5d8129bdcb6f05691bbba082bbb4f181e71b1cb28ed6bdaa`, identical to the supplied final output.

## Checked source semantics and coordinates

The word is one genuine INDEPENDENT private bigon with positive ordinary leading and trailing pads. All physical survivals and the inheritance weight are interior, with one assignment shared across capped arities. The contrasts are explicitly half the earlier full cap-four C,H coordinates; at the symmetric bare cell this gives c=1/192, consistent with the earlier C=1/96. Current-root routing gives the stated diagonal and contrast polynomials.

The trailing survival is recovered as r=c_out/(c_out+h_out), valid near the chosen positive c base. The explicit reduced observed coordinates divide the diagonal entries by powers of r and use c_out+h_out, undoing right multiplication by E(r). Thus a is the leading survival, not the product of both pads. This is an invertible local observation-coordinate change, not use of an inverse source as a legal physical operation. The chosen a=3/4 and r=1/2 are both strict.

## Checked local obstruction

The reduced four-coordinate Jacobian has rank two at the specified symmetric point. The first-two-row determinant with respect to a,s is 81/2048, so the exact first-two-output fibre has a unique analytic parameterization by u,v. The two annihilator covectors and their combined quadratic term were independently verified. First derivatives in u,v vanish, so the normal quadratic calculation survives implicit adjustment of a,s.

Joint arm-exchange symmetry makes the implicit functions centrally even. The exact coefficients a2=3, s2=-4, a4=30, s4=-20 yield the residual pure-v quartic coefficient -1192/9. The full residual normal expression has negative -u^2 and negative v^4 leading terms. The proof controls mixed quartics using Young's inequality and absorbs the sixth-order remainder, rather than inferring a sign from the pure-v path alone. Therefore it is negative for every sufficiently small nonzero point on the exact fibre.

Holding r fixed transfers this obstruction to the complete five-coordinate cap-four map. Arbitrarily close target perturbations on the first-two-output fibre with positive normal value are not covered by the supplied one-cell chart. The nonzero generic Jacobian calculation uses the same polynomial source family and is consistent with, rather than contradictory to, this singular-point covering failure.

## Same capped kernel, different finite presentation

The previously accepted full-rank positive cap-four ordinary-return theorem supplies a legal replacement for the leading ordinary segment. Appending the unchanged bigon and trailing ordinary segment preserves the SAME complete cap-four kernel. From the inherited graft formulas, fixed positive right multiplication has determinant b2(V)^2*b3(V)*b4(V)>0; hence it preserves the five-rank property. The longer positive presentation locally covers a neighborhood of that capped kernel.

This proves the intended distinction: failure of neighborhood covering in one strictly interior physical chart is not a presentation-independent obstruction to finite strict realization. The equality is at cap four, not asserted for all arities or stronger retained-history laws. No new cap-return search was rerun; the diagnostic uses that accepted theorem as a provider.

## Evidence and exact conclusion

The final SymPy rational control script was independently executed and all assertions passed with identical output. Its derivatives and Taylor coefficients support the analytic proof, while the local sign bound and regular-alternative conclusion were checked mathematically.

Accepted as a source-valid counterexample to the shortcut that every strict supplied presentation automatically locally covers its full cap-four response neighborhood. It is NOT a counterexample to a fully specified infinite-tail dichotomy, not a global semigroup-boundary claim, not an effective original G3 recognizer, not full-menu G4 closure, and not Lean verification. A zero residual tail makes exact error absorption different from neighborhood covering; that distinction is explicitly retained. No novelty-priority certificate is issued.
