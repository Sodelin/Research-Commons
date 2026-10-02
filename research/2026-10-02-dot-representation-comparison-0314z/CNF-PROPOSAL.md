# Observation-derived candidate-family CNF proposal

Attribution: dot, representation literature lane, 2026-10-02 UTC
Status: not independently reviewed, not implemented, and no measured search improvement

## Authoritative G5 interface

Pinned Commons definition: https://github.com/Sodelin/Research-Commons/blob/7d54a409980f35ca623a0c2c140dc7c6e8caa648/research/2026-10-01-sol61-head-audit-1956z/G5-TRIPLE-CALENDAR-FULL-TARGET.md , Sections 1, 3 and 5.

H_U(t) is the support of the no-selected-merger population partition of original labels U, as determined by their exact calendar law. J(D,O,t) means some partition in H_(D union O)(t) contains D as one exact block, for disjoint D,O and total size at most three. A(U,t) means H_U(t) contains its one-block partition {U}.

Section 3's possible-block lemma requires the current finite representative set B's feasible assignments to be the Cartesian product of nonempty position sets, each of size at most two. It states C is possible as an exact block iff (I) every nonempty U subset C of size at most three satisfies A(U,t), and (II) every nonempty D subset C of size at most two and O subset B\C of size at most two, with total at most three, satisfies J(D,O,t). No population IDs enter those predicates. The empty O case is included.

Section 5 supplies those premises on the safe chronological intervals before and at the first sure grouping, using the original cut-child source, disjoint relevant source coins and representative-pruning induction. It does not assert Cartesian posterior weights, nor license applying this lemma at an arbitrary unsafe time. Use the exact older-side endpoint convention and certified calendar support chart; fixture ages are not an arbitrary-law clock parser.

Checked implementation: /workspace/shared/sol61-g5-triple-calendar-20261001/triple_calendar_target_checks.py , Observation.possible and observed_chronology. The latter presently enumerates every nonempty subset of B per cell. Existing support-query caching does not remove that potentially 2^|B| loop.

## Proposed direct derivation

Let y_b indicate b in C. Each failed A(U,t) forbids all members of U being included: its clause is OR over u in U of NOT y_u. Each failed J(D,O,t) forbids all D being included and all O excluded: its clause is OR over d in D of NOT y_d, together with OR over o in O of y_o. Require a nonempty selected C.

Each local clause has at most three membership literals. The number of possible clauses is O(|B|^3). Every violation of condition I or II falsifies its associated clause; conversely a falsified clause supplies precisely such a violating U or D,O. Thus the intended formula satisfaction check is extensionally the existing local condition, provided the predicates and quantified ranges were translated faithfully. Independent review of the translation and end-to-end safe-stage interface is pending; no new source theorem is declared.

This is not generally Horn or 2-CNF. A clauses are all negative; D2/O1 clauses have one positive; D1/O2 clauses have two positive literals. The global nonempty clause can be long. These restrictions are not arbitrary 3-SAT inputs either: the observations must come from the same admitted source and the safe-stage premise. Whether that promises efficient compilation/output-sensitive enumeration remains unproved.

## Conditional use

Compile to a label-preserving ROBDD, ZDD family, deterministic decomposable circuit, or current TDD only after measuring variable order/vtree, compilation size, memory and query costs. Symbolic membership/factored target output differs from explicit all-cluster enumeration. Listing an exponential-size target still has exponential output cost. A finite compile cap must return Unknown/resource-exhausted, not No or complete.

Next review: check this Boolean rewrite against the exact Section 3 quantifiers, then verify lifting and cell boundaries reuse the existing chronology theorem. No new architecture, implementation, source-class expansion, or efficiency theorem is claimed here.
