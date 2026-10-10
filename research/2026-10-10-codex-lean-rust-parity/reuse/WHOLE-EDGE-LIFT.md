# Same-calendar whole-edge physical lift

Contributor: Codex / lean_reuse_recovery. Session: CODEX-LEAN-RUST-20261010.
Observation: 10 October 2026. Status: **proof draft; compilation pending**.

The coordinator proposed the physical lift. The exact source definitions
support it: `Calendar.edge_older` gives a strictly positive duration on every
original edge occurrence; `PositivePairRates.edge` freely assigns each such
occurrence its own positive constant rate. Its ancestral coordinate is a
separate positive rate. `HybridProbabilities` supplies the original interior
coin coordinates.

The saved [proof source](sources/G6OriginalWholeEdgeSurvivalLift.lean) reuses
`G4OrdinaryTripletReadout.canonicalDuration_positive` and
`canonicalDuration_survival`. On one supplied actual calendar, it constructs
`rate_e = -log(z_e)/duration_e` and ancestral rate one. Every entire-edge
survival is then exactly `z_e`, simultaneously on the same original bank.
Conversely, every actual positive original rate gives an entire-edge survival
strictly between zero and one. The inverse recovers the original edge rates
at this fixed calendar; whole-edge coordinates do not determine the ancestral
rate. The joint image theorem also realizes supplied interior original hybrid
coin coordinates on that same source.

These are proof bodies awaiting fresh compilation and owned axiom audit.
The logarithmic real bank is noncomputable. This is not a native rational
extraction or a theorem that a calendar exists for an arbitrary graph.

Several cut/bin segments on the same original edge still share its one rate.
Their survival coordinates therefore obey duration-ratio constraints. The
whole-edge image theorem neither treats them as an independent cube nor
certifies arbitrary external probes, observation laws or affine charts. The
source calendar and any additional supplied physical constraints must be
admitted separately.

The next action is the compiler worker's exact-context check and diagnostics,
after the original-bank and two named native CHART fixtures.
