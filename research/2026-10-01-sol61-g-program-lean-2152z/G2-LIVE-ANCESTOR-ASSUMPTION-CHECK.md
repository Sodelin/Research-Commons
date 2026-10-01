# G2/G7 live-ancestor routing assumption check

Dedicated Sol6.1 Lean lane, 2026-10-01. This is a check of the declared correct
compiler primitive, not a report that the existing compiler is wrong.

The pulse explicitly names an actual original hybrid in `RootedBinary` and its
two distinct actual incoming parent-edge IDs. A current forest state's original
copy labels map onto its live ancestral tokens; every token has an original
member. A routing coin is indexed by the live token. Copies whose ancestors have
already coalesced therefore use the same original parent edge, for every coin
realization.

Lean proves that an opposite-bit assignment to two original copies sharing one
live ancestor cannot factor through that ancestor. The incorrectly weakened
per-original-copy pulse is an exactly normalized four-outcome distribution. At
fair bits it splits a merged ancestor with probability 1/2. The correct lifted
single-live-ancestor pulse has split probability 0. The generic wrong split mass
is `2p(1-p)`.

This makes a high-risk implementation hypothesis explicit: independent
inheritance means independent coins per LIVE lineage, rather than a new coin for
each original sampled copy. Shared inheritance and retained shared registers are
different contracts. Original hybrid IDs and incoming labels are kept intact;
no compressed core actuator is substituted.

The accepted source/hand compiler already uses the correct live-lineage rule.
The finite countercontrol refutes a weaker candidate primitive; it does not
discover a gap in that accepted contract. Whole source forest construction,
stochastic transition semantics, all-copy projectivity, and one fixed original
parameter/control assignment across all response rows remain formal obligations.

Code: `program/G2LiveLineageRouting.lean`. Actual Lean 4.33.1 compilation,
source/compiler/dependency hashes and standard-axiom log: `receipts/`.
