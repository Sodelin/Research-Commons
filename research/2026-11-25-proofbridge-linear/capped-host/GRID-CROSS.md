# Grid width step and proof-reuse speed

[Alexander's Section 6](https://arxiv.org/html/1212.0186#S6) asks the broad universality question for populations avoiding a word. The [fixed-child-cap single-host theorem](https://github.com/Sodelin/Research-Commons/blob/7206e66a8de0b04725924e32df822eca530b1143/research/2026-10-09-dot-alexander-capped-universality-2055z/CAPPED-UNIVERSAL-HOST.md) is a scoped response with an existing written proof, not the literal open question as posed. This pass does not claim historical novelty.

## New Lean evidence

- [Grid cross lower bound](CappedGridCross.lean): fewer than n listed points leave both a row and a column empty, hence miss their cross. This does not require distinct points; duplicate entries cannot make the bound stronger than warranted.
- [Finite contradiction](CappedGridInterface.lean): import the common-index interval lemma and the cross lower bound. An interval assignment satisfying its exact overlap and incidence obligations cannot be represented by bags of size strictly less than the grid side. It does not construct the actual incidence assignment.
- [Control](CrossSmoke.lean): one point fails on a 2-by-2 grid; two explicit points suffice. The [receipt](grid-cross.receipt.json) records standard core axioms only.

Remaining for a whole-claim package binding: chronological normalization from real dates, graph-to-bag construction/width and cross incidence, construction of the eligible finite grid and preservation of the infinite-word language, then the exact edge-labelled and source-gender theorem assembly. The new portion covers the abstract finite contradiction only.

A scoped **hand consequence**, not separately formalized: a single enlarged-grid rival rules out any family of hosts with a common upper bound R on their number of roots, at fixed child cap k. Take side n > kR+1 and use the written proof's disjoint addition once. This does not assume the candidate sources have that same fixed root budget. It does not answer the unrestricted countable-family question when host root counts can grow.

## Measured speed

Three trials on the same warmed Linux machine, each rebuilding the same four local provider modules in a fresh directory and checking the consumer, then timing just the same consumer with those modules already built: median 4.364 s versus 0.791 s (5.52× for this fixed check). No setup, download, drafting, scheduler wait, or whole mathematical proof search is measured. The two ready typed jobs previously took 2.63 s in total for the narrow batch. [Detailed timings](reuse-speed.receipt.json).
