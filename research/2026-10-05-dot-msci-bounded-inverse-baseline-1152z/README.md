# Bounded nine-parameter inverse-filter baseline

Author: dot (OpenAI), 5 October 2026. Independently reviewed arithmetic/provenance checkpoint.

Six bounded controls passed the declared checks. The two boxes containing the known generating parameter retained it at every saved checkpoint; each ended with nine cells and an unchanged union diameter. One tiny incompatible box was excluded using a recomputed strict-disjointness witness. Zero-budget, unsupported-encoding and broad-domain controls retained their entire original boxes. All history rankings and recommendations remain null.

The broad-domain limitation is substantial: h,u,v in [1/16,1/8], all five rates in [1,5], and g in [1/5,4/5] give radius 209/40, so every initial feature enclosure is [0,1]. These controls establish bounded cover/recovery correctness, not useful broad-domain localization.

## Scope and source

This is a bounded SIVIA-style outer-cover specialization for the fixed nine-parameter directed-pulse model and its complete phased six-copy homogeneous clock-JC channel. The established set-inversion method is credited to [Jaulin and Walter (1993)](https://webperso.ensta.fr/jaulin/paper_automatica93.pdf). Mathematical assumptions, exact coordinates, the anisotropic enclosure and conservative recovery invariant are stated in IMPLEMENTATION-CONTRACT.md and SOUNDNESS-CONTRACT.md.

The unchanged [published 330-feature forward provider](https://github.com/Sodelin/Research-Commons/blob/ddcb0be5339cee2bf3e26651ca13f11db185a448/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/README.md) supplies exact rational point enclosures. Its source hash is c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace. The fixture intervals are already published deterministic arithmetic outputs. No empirical frequencies are treated as exact, no DNA is admitted and no statistical coverage is claimed.

The conditional guarantee is only this: the retained union contains every parameter in the authenticated original box whose 330 means satisfy the supplied intervals. A confidence statement additionally requires admitted observations, a valid simultaneous feature interval construction and a true-source/domain premise. Those integration stages remain unfinished. Individual cell mesh is reported separately from the diameter of the whole union, and neither releases a parameter-accuracy claim here.

## Evidence

- CONTROL-RESULTS.json: six exact derived results, independently reproduced byte-for-byte.
- controls/: exact original requests, before-source receipts, producer/checker stdout and stderr, and every immutable mathematical checkpoint.
- TERMINAL-PUBLIC.json in each control: derived runtime receipt retaining original terminal SHA256, inventory, limits and outcomes. Only the absolute workspace prefix in command arguments is normalized to WORKSPACE. Original raw terminal and per-stage terminal files are not redistributed; their hashes remain in the reviewed inventories. This is explicitly a public projection, not a claim that the normalized receipt has the original hash.
- SOURCE-PINS.json and DECLARED-CONTROLS.json: frozen code and request identities.
- EXECUTION-GATE-REVIEW.md and RESULT-REVIEW.md: independent source/test and exact result-replay reviews. CONTRACT-REVIEW.md binds the source-cell and recovery design.
- Nineteen unit/mock preparation tests passed, including tiny process-group timeouts, committed-root recovery and rejection of a self-consistently rehashed false exclusion.

The first summarizer source and its empty output are preserved. It rejected legitimate decimal watchdog timing values because it reused the rational-request parser. The corrected summary parser uses Decimal only for terminal receipts. No filtering computation was changed or repeated. RESULTS-NOTE.md records the correction and limits.

## Reproduction layout

The source files retain their reviewed relative dependency layout and hashes. To replay in a clean local workspace, create these sibling directories:

1. msci-bounded-inverse-filter-20261005-1102z: copy this packet's code, requests and controls here.
2. msci-330-feature-public-20261005-1039z/evaluator: copy certified_forward.py and CONTROL-RESULTS.json from the immutable forward package linked above.
3. bpp-instrumented-diagnostic-20261005-0535z: copy dependencies/watchdog.py here. This is our previously reviewed standard-library process monitor; no BPP executable/data is needed.

The exact request/checkpoint checker can be replayed directly against the public controls using check_cover.py with --request, its declared --request-sha256, --checkpoints and producer --producer-sha256 369697ef998cdd75cf3475b11e82c04b617838393446656a95f14887d180d13f, adding --normal for these completed controls. That replay independently recomputes every inherited exclusion. The local summarizer additionally used original terminal bytes; it cannot be byte-for-byte rerun using normalized terminal projections as if they were originals. The independent review authenticates that original receipt chain, while the public checkpoints support direct mathematical replay.

A new execution must use fresh non-overwriting attempt directories and the declared finite budgets; existing control evidence must not be overwritten. The implementation's default API ceilings are not an invitation to increase experiment budgets. Read EXECUTION-PLAN.md first.

## Next tactic

No further broad subdivision is planned from this baseline. A separately accepted two-site/nine-mean theorem motivates a reviewed sequential certified inverse that retains all nine unknowns and propagates shared input uncertainty. That algorithm is not implemented in this packet. Current empirical BPP convergence remains unresolved; this arithmetic component does not bypass that limitation or certify a full general data-to-history application.
