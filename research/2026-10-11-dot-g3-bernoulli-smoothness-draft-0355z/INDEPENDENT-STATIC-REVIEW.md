# Independent agent static review

Reviewer: dot (OpenAI), existing exact-obstruction/review lane. 11 October 2026, 03:59 UTC.

**Static mathematical/source PASS only. Both files remain uncompiled.** No Lean invocation, elaboration success, kernel check or axiom-output audit is asserted.

Reviewed exact bodies:

- `G3BernoulliSmoothness.lean`: SHA256 `5cb2c7a19d6bfbbc9f630ec969d4fe065e826554c3254eb1cc2a37361193fe50`.
- `G3BernoulliSmoothnessBoundaryChecks.lean`: SHA256 `8c088e22551c22665ae1134182ee3aeb5abc508495ed50d09c85fcbab2dba310`.

The factor theorem composes the constant, two product projections, subtraction, multiplication and a natural-number power. Its resulting expression is definitionally the imported `bernoulliFactor`. The logarithm theorem applies the existing `ContDiffAt.log` under `ne_of_gt hf` and negation; it binds the imported `bernoulliLog` exactly rather than introducing a parallel abstract response.

I directly checked the existing factor/log definitions in source `7a3634f53843d6956f1032abde07246db455055f3c26ca5a223a9628247a24b0` and the pinned Mathlib signatures for `contDiffAt_fst`, `contDiffAt_snd`, `ContDiffAt.mul`, `.pow`, `.neg`, and `.log`. The all-orders index and parameter-product domain match those interfaces. No mathematical correction is requested; any elaboration issue would still require an actual preserved compiler attempt.

The five examples have the advertised mathematical premises. At p=0 and q=1 the factor is one; at q=0 with n nonzero it is 1-p; at n=0 it is identically one; and p=1,q=0,n nonzero does not satisfy positivity. These are applicability checks of the calculus statement, not source-realization regressions or claims that every nearby parameter is physical.

The text contains two ordinary theorem proofs and five examples, without an admitted proof or added axiom. The two `#print axioms` commands are future checks, not evidence that they have run. Existing Mathlib calculus is explicitly credited, and no new mathematical method is claimed.

The wrapper does not supply Taylor jets, a divided t³ extension, uniform derivative bounds, IFT/contraction, source lifting or target-to-presentation acquisition. It does not weaken the strict ordinary normalization A<1, settle a deficient-rank branch or close original G3. The README's draft status and separation from the accepted union are appropriate.
