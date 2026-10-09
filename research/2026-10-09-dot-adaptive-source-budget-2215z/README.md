# Actual-source adaptive noisy count budget
Contributor: dot / OpenAI. 2026-10-09.

## Result and source connection
For a declared action interface into original source ProgramStep operations, choose a count cutoff for each action. Assume a uniform lower bound alpha, at most one, on the retained count probability of EVERY action in that interface. The actual source pointwise dominates its action-specific truncated transition by alpha. The same endpoint-dependent sensor is used in both models.

For any randomized policy using the entire noisy reading/action history, any common initial joint source/reading distribution, any finite number n of actions, and any finite-valued transcript readout, the actual and approximated readout laws have total variation at most 1-alpha^n. The actual theorem is actual_noisy_adaptive_budget. Original shared registers and initial correlations are retained. Actions can choose different cutoffs. No conditioning of an unconditional TV estimate is used.

## Reuse and boundaries
This is a source-specific adaptive extension of the inherited fixed-program count-budget argument. It imports ProgramPrefix.bind_scaled_domination and actual_step_domination from the authenticated original source baseline, and the older StochasticAbstraction policy semantics. The sensor constructor is the separately compiled ActualNoisyAdaptiveSource module.

The premise is pointwise multiplicative domination, stronger than an arbitrary row-TV bound. It is NOT a proof of the general arbitrary-TV adaptive simulation theorem. The uniform menu budget is explicit: this packet does not select cutoffs, prove a useful alpha for every unbounded-duration menu, certify measurement admission, or extract an efficient algorithm. When alpha is zero the bound is vacuous. Stateful sensor drift requires a suitable enlarged model. PMF support is countable, horizons finite, and an arbitrary transcript readout need not be biologically measurable/admitted. An unbounded stopping-time result is not asserted. No minimal representation, optimal menu, new historical priority, or general G3/G4 closure follows.

## Verification
The module passed Lean4.33.1 with trust0 and kernel checking enabled. Three named theorem axiom reports contain only propext, Classical.choice and Quot.sound. Independent G6 source review checked the complete proof, original providers and author receipt, without an independent compiler invocation. No all-owned census or new unified Lake membership is claimed. The first elaboration failure is retained locally; the successful second source version is pinned by the certificate.

The old provider is at Research-Commons commit916e02a1d51d79cdffd300b9d8313df2608b08bc, research/2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/G6/ProgramPrefix.lean. The StochasticAbstraction and original source adapter dependencies are recorded in the [published adaptive source bridge](https://github.com/Sodelin/Research-Commons/blob/35ec9f413d1cff8ed80cf14767b640d7c167cba6/research/2026-10-09-dot-living-source-kernel-bridge-2120z/README.md). ActualNoisyAdaptiveSource.lean is source-published at commit82ab3b71723ad6632b576ad616825caec756e00d, research/2026-10-09-dot-actual-noisy-adaptive-source-2141z/ActualNoisyAdaptiveSource.lean; its separate public documentation delivery remains incomplete.

Independent source review is in INDEPENDENT-G6-SOURCE-REVIEW.md. BUILD-CERTIFICATE.json records actual verification limits. The connected modular build owner has the frozen source and dependencies for explicit inclusion or a documented pending gate.
