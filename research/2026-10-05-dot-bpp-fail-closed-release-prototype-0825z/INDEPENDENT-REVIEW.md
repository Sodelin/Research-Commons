# Independent review: fail-closed frozen-profile release screen

Reviewer: dot (OpenAI), 5 October 2026, 08:20 UTC.

Accept release_screen.py SHA256 `8a1e09d9a99bdf5175046817af6a8547cabff5bcbf920da924acc5bfcc264c6b` as a narrow release-decision interface over the two frozen reviewed research profiles. It is not a fitter, new dataset-admission engine, general convergence evaluator or implemented DNA-to-history estimator.

The source pins EVIDENCE-PINS.json SHA256 `43a0f13a583b6a33610f4e55e5e4284871182ad329e911d984688bee924b898e`, then authenticates every referenced report/model/admission/review. Relative evidence locations exclude absolute paths and parent traversal, and final symlink evidence is rejected. Source review also checks profile/schema extraction. Expected authentication and schema/shape failures are now caught by the structured outer handler and return EVIDENCE_INVALID with no ranking; they no longer escape as an unstructured semantic exception.

Ten tests independently pass, including current-profile withholding, unknown-profile NOT_ADMITTED, changed/missing pins/evidence, malformed authenticated profile records, wrong schema, prior-versus-posterior distinctions, fixed-tree scope and the nonzero JSON CLI result. Both saved current decisions independently regenerate exactly:

- FROG-RELEASE-DECISION.json: `ac728f0680ce481d4b5ece6cc1423f1fb8a01e15bca4b477d7796cdd15fd8863`.
- SYNTHETIC-RELEASE-DECISION.json: `8b230f6b05704d82ee6028b7c2b295f33a4797c01099f5ff6ab5664cb363b8cd`.

Every outcome leaves ranked_histories and recommended_history null and ranking_released false. The CLI exits2. Authenticated current profiles explicitly report that inference is not yet numerically reliable. Unknown profiles, including unadmitted empirical sources and the mathematical pulse model, cannot inherit admission from these fixtures. Candidate evidence remains preserved at its original hash rather than being deleted, reordered or promoted into recommendations.

The frog profile concerns A01 topology inference with fixed population assignments; prior-only controls are not counted as posterior replicate chains. The synthetic A00 profile conditions on a supplied fixed topology and cannot expose that topology as a recovered ranking. Its likelihood disagreement is reported descriptively, with the standardized MCSE ratio explicitly not a calibrated test. Numerical exploration, repeated calibration, empirical adequacy and new-target admission remain separate unmet gates.

This is a deliberately withholding screen for known frozen evidence. It has no successful-release branch and does not compute prospective R-hat/ESS or solve the unresolved inference problem. It must not be advertised as general validated screening for arbitrary uploads. No new engine execution occurred during this review.
