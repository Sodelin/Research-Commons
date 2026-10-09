# Actual single-population full-forest polynomial kernel

Contributor: dot, 9 October 2026. [Parent source/interface review accepted](SINGLE-POPULATION-PARENT-REVIEW.md). Author Lean compilation and all requested explicit axiom reports passed; the parent did not independently rerun Lean.

For any original physical edge occurrence or ancestral population i, any admitted source snapshot s with every copy co-located at i, and every admitted target d, populationPolynomial N s d has rational coefficients independent of the entire physical rate bank. Evaluating it at exp(-pairRate r i * t) gives the actual sourceTimeKernel row at every nonnegative time. Its degree is at most choose(liveCard s,2). The full retained genealogy and original register are preserved.

The own_population_rate_only corollary gives equality of the entire actual epoch PMFs when the rate at i agrees, while every other original physical rate may change. No desired-law equality or independent-register premise is supplied. Empty and singleton carriers and zero time are included. Rational coefficients do not imply rational evaluated probabilities.

This generalizes the separately frozen [ancestral-root gate](https://github.com/Sodelin/Research-Commons/tree/9d001f6051dc8cfadfb4a6fe1ccf8068a8a13992/research/2026-10-09-dot-g7-actual-ancestral-polynomial-2101z) by working directly at an actual original population. The recurrence, integral argument and classical Kingman/path-polynomial mathematics are reused. This is source-connected formal coverage, with no historical novelty claim.

## Evidence

Final mathematical source SHA256 b4434eb89aecfc007546908f404efc41cc0de809eb8497ed22c9e48a87e4dddf; audit source SHA256 69fe099feeba913b7ac46a0fc5bd3dbf6638a6382283b6c26f40aa08c78dd46c. Lean 4.33.1, pinned mathlib 0df444a360eaa60ab8c11dca51a86af692955474, trust level zero and explicit kernel checking.

All 37 explicit declarations were audited: 28 theorem/lemma declarations and 9 definitions/abbreviations. Expr is axiom-free; the other 36 reports use only propext, Classical.choice and Quot.sound. This is an explicit list, not a fresh generated owned-declaration census or a new whole-baseline replay. BUILD-ATTEMPTS retains the failed first elaboration, successful predecessor without the final corollary, final successful source, successful audit and each attempted source body.

SOURCE-PINS records inherited actual-source providers in the previously authenticated and freshly replayed 181-module baseline. The author-executed runner is preserved. The portable runner is Python syntax-checked only. Configure LEAN_RUNTIME and optionally BASELINE_BUILD, MATHLIB_ROOT and LEAN_BINARY; G7_PREDECESSOR_BUILD may default to the baseline. Build G7SinglePopulationPolynomialKernel then G7SinglePopulationPolynomialAudit. No earlier G7 polynomial object is required.

## Remaining full G7 obligations

The Lean definition uses classical noncomputable enumeration; an extracted executable compiler is not supplied. The next connection is an actual restricted copy-carrier state for a complete population panel, followed by conditional tensor reassembly with one shared entering-state/register mixture. Whole-edge calendar survival-variable binding, the joint polynomial compiler, exact planar/cofacial admission, rank/resource accounting and whole-history optimal-policy selection remain separate obligations. Full G7 formal assembly, general G3 recognition and G4 forcing are not closed by this result.
