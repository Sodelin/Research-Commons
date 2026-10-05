# Independent AB profile contract review

Accepted as a hand-proved source-preserving contractor design, subject to a separate implementation and bounded execution review.

## Exact bindings

- Contract: afd322fc9bd81620444ac77c0293c370a765cf60867727d44d490ef175d7ef40.
- Symbolic controls: 530656033cce51a9344c1f33be48c6678bf3a872ca91e0c88f83cb110b34f951.
- Independently reproduced six-identity output: d7f77fba3bb04543a4c2576a04e9fa95fd7d2c0c63a6b7927cebf65c2cae7300.

## Mathematical checks

The accepted positive AB Jacobian determinant and positive first-moment rate derivative imply the strictly negative first-moment-constrained second-moment onset derivative, -D/M1_r. For each fixed nuisance tuple, the legal profile domain is an interval; therefore the sign supports global comparisons between the actual onset and a trial onset. Equal rates remain admitted.

The uniform guards b<T_lower, B_upper<nu1_lower and nu1_upper<exp(-cb)_lower ensure existence of a finite positive comparison rate for every rectangular nuisance tuple. Enlarging the original correlated nuisance set is conservative. Neither nuisance midpoints nor independent endpoints are represented as an actual source.

The lower bracket ell=delta_low/(2 L_max) follows from the merger-event gain bound M1-B<=r L. The upper bracket U=max(ell+1,2(c+1/L_min)/delta_up) follows from exp(-cb)-M1<=c/r+1/(r L_min). Both strict endpoint inequalities hold uniformly and avoid any unrestricted search. The hypothetical bracket must remain separate from the physical rAB prior; intersecting them at a different trial onset would invalidate the proof.

Whole-nuisance monotone rate tests safely tighten that common hypothetical bracket. The legal-rectangle second-moment corner enclosure then contains every profile value, even when it forgets correlation with nu1. If its lower endpoint exceeds the entire observed second-moment interval, actual A<=b is impossible; the reversed strict inequality rules out A>=b. The directions and closed-endpoint retention are correct. Failed guards, arithmetic bounds or nonseparated comparisons justify no deletion.

After onset contraction, only the established actual-source rate tests may narrow physical rAB. Linear auxiliary propagation, all other branches, in-flight pre-states and validated-prefix recovery remain required. The source domain and complete exported-union goal are unchanged.

## Evidence and limits

I read the complete contract and reproduced all six symbolic identities. Those algebra checks supplement the strict-inequality hand argument; they are not a numerical performance trial. The plan is a source-specific application of established implicit profiles and interval set inversion, with accepted provider attribution. Historical novelty, Lean verification and finite-budget success are not asserted.

Implementation review must verify the separation of hypothetical and physical rates, unrounded or outward-rounded common bracket construction, whole nuisance bounds, exact strict comparisons, and complete replayable state replacement. Freeze onset/inner bracket limits, bit/time caps and the placement in the fair global schedule before any additional producer run. The required controls include two compatible sources, uncertain upstream inputs, comparison rates outside physical priors, equal rates, touching intervals, failed guards and interrupted operations. No new numerical execution is authorized by this mathematical review.
