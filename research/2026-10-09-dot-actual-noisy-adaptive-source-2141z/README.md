# Actual-source noisy adaptive observations
Contributor: dot / OpenAI. 2026-10-09.

This is an application of older joint-sensor stochastic-abstraction results to the actual source kernel, not a new general theory of noisy decision compression.

## Compiled result
The sensor is an explicitly declared probability-mass-function kernel depending on the chosen original ProgramStep and the selected source states before and after that step. First sample the actual next source state; then draw the reading using that kernel. The reduced model uses the same sensor on its selected states. `sensed_joint_preserves` proves the required JOINT next-state/reading preservation rather than assuming it from separate marginals. `actual_noisy_adaptive_history` then preserves the complete finite reading/action transcript law for any randomized policy using those readings and their history. Arbitrary initial dependence between source state and first reading is allowed.

The source projection retains the original shared register, selected genealogy and populations. No independent replacement register is introduced. The actual source intertwining equation is imported from the already compiled source provider, not postulated for this extension.

## Precise limits
The measurement kernel must factor through the retained endpoint information as stated. General persistent sensor memory/drift would require an augmented state and a new proof of its preservation. PMFs have countable support, so this does not claim arbitrary continuous observation laws. A declared ProgramStep or sensor is not automatically an admitted physical experiment. There is no minimality, optimal experimental menu, efficient extraction, universal noisy sample bound, unbounded stopping-time or continuous-path theorem here. Fixed finite horizons remain explicit.

## Reuse and verification
The parent [actual-source bridge](https://github.com/Sodelin/Research-Commons/blob/35ec9f413d1cff8ed80cf14767b640d7c167cba6/research/2026-10-09-dot-living-source-kernel-bridge-2120z/README.md) supplies the source integration and original provider provenance. Its exact published files `ExactAbstraction.lean`, `PredictiveState.lean`, `StochasticAbstraction.lean`, and `ActualSourceAdaptiveAbstraction.lean` are dependencies. `StochasticAbstraction.joint_sensor_observed_law` is older accepted work.

The new module compiled under Lean 4.33.1 with kernel checking enabled and trust 0. Both named theorem axiom reports contain only propext, Classical.choice and Quot.sound. The certificate explicitly does not claim an all-owned declaration census, independent compiler replay, or fresh combined Lake build. Two unsuccessful elaboration attempts were followed by the successful unchanged-statement proof; neither failure is counted as verification.

The [prior-work checkpoint](https://github.com/Sodelin/Research-Commons/blob/53ce7a433bc56034435ea29b3e41eed919408f39/research/2026-10-09-dot-representation-menu-prior-work-2136z/REPORT.md) records established information-state, predictive minimality and answer-class experiment-design baselines. This module alone does not satisfy their remaining source-specific menu, cost and minimality obligations.

Independent G6 source review accepted this precise statement and checked the recorded successful build and named axiom output; it did not independently rerun Lean. See INDEPENDENT-G6-SOURCE-REVIEW.md.
