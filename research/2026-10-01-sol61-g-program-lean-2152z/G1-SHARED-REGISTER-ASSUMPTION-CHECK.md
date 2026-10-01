# G1 shared-register assumption check

Dedicated Sol6.1 Lean lane, 2026-10-01. This is a machine-checked context stress
test, not a new failure of the accepted G1 theorem or a full G1 formalization.

## Positive-time biological component

Two live labelled lineages have one exponential pair-merger holding clock. The
output unranked forest is either the two separate original tokens or their one
merger. The Lean proof uses Mathlib's actual exponential probability measure,
proves its survival probability is `exp(-rate*duration)`, and verifies that
positive rates `log 2` and `log 4`, both over duration 1, have survival
probabilities 1/2 and 1/4. Both edge parameters are strictly positive. This is
the two-lineage common-bigon conditional kernel component; general original
graph admission/extraction and whole-source semantics remain separate.

The four-entry joint register/forest kernel is normalized and nonnegative for
interior coin weights and positive pair rates. The counterexample is a genuine
finite stochastic-kernel difference, not an arbitrary unsupported probability
matrix.

## Exact exterior context contract

A fair original parent register selects the component branch, AND the same
register is retained and can be read/reused by an exterior. Its event is
“register 0 and two surviving lineages.” The correct joint mass is 1/4.

Marginalizing the component's register gives two-survivor probability 3/8.
Drawing independently from that marginal against the exterior's retained
register gives joint mass 3/16. Lean verifies every value exactly and proves
that the two whole register/forest laws differ.

The general difference is `p(1-p)(x0-x1)`. For an interior binary register,
marginal resampling preserves that exposed-register survival event exactly when
the two conditional survival probabilities agree.

## Scope and lesson

This exterior explicitly has access to the shared register. It is not ordinary
passive gene-tree or DNA observation. With genuinely private component coins
independent of the exterior, marginal replacement can remain sound. The accepted
conditional-register G1 proof already preserves and reuses the register; this
formal check confirms why that hypothesis is necessary. It does not discover a
new gap in that accepted contract.

The safe interface must retain conditional kernels indexed by the shared
register and actual input forest. This component does not prove that a general
original graph supplies those kernels, that all subtrees are correctly grafted,
that the root blob is preserved, or that a decorated core is an ordinary
source-realizable bounded network.

## Machine verification

`program/G1SharedRegisterStress.lean` compiled with Lean 4.33.1, single-thread,
against pinned mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Exact
source/compiler/dependency hashes and successful log are in `receipts/`.
Every printed theorem depends only on standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`. No placeholder or custom unproved axiom is
used.
