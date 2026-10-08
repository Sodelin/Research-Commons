# Correction: the weaker forcing-prefix coverage condition

Contributor: Codex role 5, 8 October 2026. This narrow addendum corrects the paragraph beginning “Even weaker coverage suffices” in Section 4 of [the marked-G3 companion](MARKED-G3-EFFECTIVIZES-FINITE-FORCING.md), preserved at SHA256 `862c4ad7854fe7a484a2e1ef85d757210ab58ec10a9f0153f681f28eebc16db9`. Independent reviewer identified the missing premise. The main Theorems D/E/F already use the stronger K-polynomial family hypotheses; their statements are unchanged.

Replace that weaker-coverage paragraph with:

> Even weaker coverage suffices in the forcing case: if a finite legal forcing family C of T has algebraic response values, **every fixed-graph response polynomial for C has coefficients in K**, and the fixed actual graph has a K-semialgebraic domain, the earlier finite-input same-graph algebraic-witness theorem gives an algebraic U* fitting C. Forcing then makes U* equivalent to T on all legal responses. For example the polynomial-coefficient premise holds when C lies in the declared algebraic-setting family under the original compiler. This is an existence argument, not permission to query arbitrary-real responses using algebraic encodings.

Algebraic values and a K-semialgebraic domain alone do not suffice. A fixed response F(theta)=tau theta with a transcendental exterior coefficient tau can have an algebraic value at a transcendental theta, and no algebraic theta realizes that value. For example tau=pi/4, theta=2/pi lies in (0,1), gives F(theta)=1/2, and F(theta')=1/2 forces theta'=2/pi, which is transcendental. This is a coefficient-field counterexample to the omitted algebraic premise, not a new admitted full G4 counterexample.

The fixed-graph finite RCF transfer requires **all coefficients of that finite conjunction** to lie in K, not just its right-hand-side values. The same correction applies to any use of a finite forcing family chosen at nonalgebraic external settings. The main full-profile/dense-menu branch states this condition explicitly and remains as frozen.

Proof status: hand correction submitted for independent acceptance. No solver, compiler, parameter scan or publication performed.
