# Finite union of original path budgets

G7FinitePathBudgetBridge is a semantic adapter over the EXISTING usedRows,
usedSites, WithinBudget and trajectory_budget_deletion_closed. It adds no
programme/source/QE engine or native resource-state implementation.

A region consists of the original site/row/call ceiling and optional permitted
original row/site sets. None means the complete finite carrier. A finite union
means there is ONE currently satisfied region. All costs use positive-support
original rows and their touched sites along the EXECUTED path; repeated rows
are counted once in the union. Actual positive support/programme semantics
remain the supplier's premise, not a Boolean flag added by this adapter.

Four complete selected declarations ACTUALLY passed hosted4.35/mathlib56a005:
Astra.G7FinitePathBudgetBridge.finite_union_deletion_closed,
next_action_legal_deletion, extension_call_bound and
zero_remaining_no_legal_action. All selected axioms are exactly the standard3;
no errors/sorry/unsafe warnings, seven benign unused/style warnings retained.
There was no rejected source revision for this component.

The first two prove the deletion-closed physical-legality premise used by the
retained rank theorem. The extension bound uses the maximum, over currently
fitting regions, of region.calls minus the already executed path length.
Every legal extension fits a region that already fitted the smaller path, so
its total length is at most current length plus this maximum. A zero maximum
therefore leaves no legal additional action. Empty unions are also covered;
nonempty-region admission remains explicit in the native frontend.

Standalone5073B/SHA256
901ed36d65848fe0d1ac88a6b4bc70931273c7b043094fa9dc66b29fa422f5d2;
virtual25140B/SHA256
1b52d64139d9fc7d33558e36c96fd355dcb1ed434ae76a8cc16b7d77d7db1a6d;
actual appended-audit submission SHA256
f10e364bba4df89051ac4b58582bbd324e809e7a4062e894eee8baab0992ee27.
The exact previously checked complete G7 game/rank projection is retained.
Full printed types/axioms and source map are in the public evidence packet.

These statements do not prove the Rust BTreeSet loops, AST construction or
parser correct. The rank-to-game coefficient/totality premises, original source
admission, legal programmes and effective history-relative selection remain
separate. No resource-cap UNKNOWN becomes budget NO or original-source NO.
The hosted proof-only game repair is not silently substituted into native pins.
