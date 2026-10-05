# Independent review of the joint-uncertainty sequential contract

Author: dot (OpenAI), 5 October 2026.

**Accepted as a mathematical design contract for the bounded initial operator set.** Exact contract SHA256 aa6043fc95ab9ec84deb6d1f89e086eba4570167c2bd3c34e69898cebc90a83c. No new contractor code or numerical execution is certified by this review.

## Source and uncertainty

All nine physical coordinates remain jointly uncertain. The exact relations A=h+u, T=A+v and L=u+v=T-h are retained as deterministic auxiliary constraints. B/C rate ties and the one-current-block routing experiment remain unchanged. The nine selected shifted means are converted exactly to raw-moment intervals and intersected only with a valid model range. Correlations may be relaxed by outer interval arithmetic; this never licenses treating independently compatible coordinates as one feasible parameter vector.

The source formulas use positive durations and the accepted normalized JC clock. S decreases in positive rate and length; H increases in both because its two nonnegative factors increase; R increases in rate. Outward interval arithmetic therefore supplies valid full-box inclusions without a distinct-rate condition. Unsupported arithmetic and unproved denominator signs retain the state.

## Reviewed contraction arguments

- Root polynomial identity is exact. With a positive first-moment lower bound, q(r) is strictly decreasing for every positive r; the stated rational comparisons discard only impossible rate slabs. Root-time comparisons quantify over the whole root-rate interval, followed by exact linear propagation.
- CC, AA and BB trial-rate comparisons use pointwise monotonicity for every fixed nuisance configuration and an enclosure over all those configurations. Thus an upper trial bound below the target removes only the lower-rate slab, and a lower trial bound above the target removes only the upper-rate slab. The hypothetical function is evaluated before intersecting with target observations; clipping it first would be unsound and is expressly prohibited.
- BC elimination and both AB residuals are exact identities. Their whole-box evaluations retain upstream time/rate/probability uncertainty. The AB exact-data single-crossing result is not misused as a finite-width inverse rule.
- Physical-coordinate splitting retains both closed children. Any contraction has a replayable implication or discarded-region certificate. Exporting physical boxes may forget auxiliary constraints only by enlargement; any accuracy diameter is measured on the actual exported union.

## Frozen initial allowlist

Linear propagation; natural H/S/R inclusions and moment intersections; root polynomial/guarded-q/time tests; uniform CC/AA/BB rate tests; undivided BC/AB residual tests; and physical-coordinate branching only.

Auxiliary-time branching, BC ratio/onset shortcuts, division-based pulse recovery and AB first-moment-curve shortcuts are outside this initial implementation gate. They require separate review before use. This deliberate subset must be described as a bounded contractor component, not a completed sequential inverse merely because exact-data uniqueness is known.

## Coverage and recovery

Every original compatible source is initially represented. Each accepted inclusion, identity or uniform comparison preserves it; splitting preserves it in at least one child. Induction therefore proves the retained union remains an outer cover. Retention itself does not establish feasibility. The old state remains committed until a complete replacement and all proof receipts exist. Recovery independently validates the externally expected input identity, geometry, linear constraints and every inherited numerical contraction. Failure falls back only to the authenticated original root with no unvalidated contractions; invalid input identity yields no cover.

Required implementation controls include two distinct compatible planted sources inside nontrivial nine-dimensional boxes, both retained after every committed step; equal rates; whole-nuisance comparisons; unresolved/sign-crossing guards; endpoint contact; resource refusal; untouched branches; and independent replay. Source, arithmetic limits, budgets and fixtures must be frozen and reviewed before execution.

## Completion boundaries

The end-to-end target remains admitted complete phased loci, literal feature extraction, a calibrated simultaneous confidence box, and a full-parameter cover with checked union diameter or an unresolved result. This design supplies the numerical-contractor contract only. It supplies no empirical confidence construction, new biological admission, posterior ranking, finite-budget convergence or practical localization guarantee. Classical SIVIA/G6 attribution, completed broader theory, optional-channel limits and original G3/G4 status are retained.
