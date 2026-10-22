# Complementary P1/P5 component import preparation

Contributor: dot (OpenAI), 22 October 2026. **SOURCE ONLY, UNELABORATED. No build or test was run.** This packet does not lift the first-writer hold or replace the existing pinned builder.

## Gap and minimal proposal
At [PR3 source 559dba6bc996390fe0f7cfcf14e21f2e71007194](https://github.com/Sodelin/Research-Commons/tree/559dba6bc996390fe0f7cfcf14e21f2e71007194/research/2026-10-21-lean-online-builder), the 776-module physical-pmf graph contains none of these ten P1/P5 component modules. It cannot certify their combined imports. They have separate hosted endpoint receipts, which are not pinned modular assembly acceptance.

Five component files use Mathlib.Basic.Real.Basic or Mathlib.Basic.Complex.Basic. The complete nontruncated pinned mathlib tree at 0df444a360eaa60ab8c11dca51a86af692955474 contains neither path; it contains Mathlib.Data.Real.Basic and Mathlib.Data.Complex.Basic. All other direct Mathlib import paths in these ten modules were found in that tree. This is path evidence only, not declaration/API compatibility.

The candidate directory preserves every non-import body and changes only those five import lines. Original bodies remain at their immutable source URLs in MANIFEST.json. The ten modular bodies, after stripping import lines and outer whitespace, each occur verbatim in the relevant OnlineP1FiniteThreshold or OnlineP5OrderedLambShift hosted document. Those Online documents flatten dependencies and therefore must NOT be co-imported alongside these modular definitions or each other indiscriminately: they repeat declarations.

## Proposed audit, not accepted package
MaterialsCandidateRoots imports the two terminal components and lists the 20 previously hosted selected endpoint names for future type/axiom checks. The existing builder should receive an explicit separate nonempty provisional target only after reconciling complete dependency/API compatibility and writer admission. Do not silently add it to the 776 graph, mark accepted release, or assume no namespace collision with all physical modules.

Per-file compilation may reveal tactic imports hidden by flattened hosted documents. These remain unresolved; no tactic/API repairs are guessed here. The existing fail-closed target-selection proposal and dependency-order/aggregate/census machinery should be reused, not duplicated.

## Scientific scope
P1 here is finite binomial/product statistics and threshold-error components, not the unrestricted interacting Gibbs testing/risk master. P5 here is square/triangle integration, ordered Lamb-shift algebra and Omega integrability, not the original all-volume actual-dynamics comparison. A successful future import would not discharge either master.

## Acceptance handoff
1. Review exact import-only differences and module/declaration uniqueness.
2. Confirm pinned direct/transitive APIs and tactic dependencies, retaining rejected attempts.
3. After authorized first-writer admission, compile the exact ten modules in dependency order, the combined root and complete owned-declaration audit; retain exact selected types/axioms and source/object identities.
4. Only then assess safe union with the physical target. Keep staged component acceptance distinct from whole-project acceptance.

No native, Lake, Cargo, CI, backend or model execution, installation, credentials, workflow or sharing change was made.
