# How Lean, Python and Rust fit together

Codex coordinator, 10 October 2026, 07:30 PDT. Explanation and dated status;
the linked receipts define the precise verification scope.

**Rust is a good choice for the practical engine.** Lean supplies mathematical
definitions and proofs; Python supplies research experiments and independent
reference calculations. Rust implements the same operations as a bounded,
standalone executable. This is a port with explicit correspondence checks;
Lean proofs do not automatically become proofs about the Rust binary.

## Epochs and Lake are different concepts

An **epoch** is an interval in the biological model between boundary events.
Lineages remain in their assigned populations and may merge during the interval.
A boundary operation moves them through an original node or edge occurrence.
A sequence of intervals and boundaries forms an operation word. Ancestral
completion finishes the remaining genealogy in the root population.

A Lean epoch module defines and proves properties of those operations. Its Rust
counterpart calculates the full probability table while retaining the same
genealogies, population locations and hybrid register.

**Lake** is Lean's build tool. A package is a project managed by Lake, modules
are `.lean` files, dependencies are other packages/modules, and the Lean
compiler/kernel checks the definitions and proofs. Epochs are model operations,
not collections of packages or compilers.

## Why this language combination

| Language | Role and tradeoff here |
|---|---|
| Lean | States the exact model and checks proofs. Mathematical completion and executable implementation are distinct obligations. |
| Python | Fast to change, useful for experiments, reference solvers and evidence processing. It remains valuable even when the production engine is Rust. |
| Rust | Typed interfaces, explicit error/resource outcomes, memory safety and a fast standalone runtime. Useful for composing many stateful solver components; development takes more effort while the model is changing. |
| C | Fast and widely portable, with more manual memory/ownership discipline. There is no specific C integration requirement driving this project. |
| C++ | Fast, with a large scientific library ecosystem. A substantial existing C++ engine or required library could make it preferable; we currently have a growing checked Rust implementation. |

All four implementation languages can use exact rational arithmetic. Rust's
memory safety does not prove a probability formula or source-model assumption.
The principal scaling limits include symbolic term growth and the number of
states; language speed does not remove those limits. No comparative benchmark
of these languages is claimed.

## What is checked so far

| Component | Current evidence |
|---|---|
| Connected Lean baseline | Latest 1,433-module union has authenticated prior component checks and a fresh aggregate/full ownership audit: 98,330 declarations, 90,253 theorem declarations, no owned/nonstandard axioms or missing modules. The earlier 1,340-component build was all fresh. [Union review](../quality/LATEST-UNION-REVIEW.json). |
| Original population recurrence | Eight actual original Lean/Rust/independent-generator comparisons pass. [Receipt](evidence/population-lean-rust-review-1/RECEIPT.json). |
| Mixed-population epochs | Eight ordinary and one parallel-edge original Lean/Rust/reference comparisons pass. [Ordinary execution](../lean/ORIGINAL-EPOCH-NATIVE-EXECUTION-RESULT.json), [parallel execution](../lean/ORIGINAL-PARALLEL-EPOCH-NATIVE-EXECUTION-RESULT.json). |
| Boundaries | Generic sparse source-boundary theorem passes a 133-module audit; all twelve actual original Lean/Rust/reference full-table comparisons pass separately. [Proof review](../quality/EFFECTIVE-BOUNDARY-REVIEW.json), [actual execution](../lean/ORIGINAL-BOUNDARY-NATIVE-EXECUTION-RESULT.json). |
| Finite operation words | Eight original cases plus two natural hybrid controls pass full-table/reference comparisons. Root independently checked all 42 captured full rows, exact work, literal witnesses and frozen build identities. [Review](../quality/WORD-CANDIDATE-REVIEW.json). |
| Actual finite-word source and execution | Concrete source bridges pass135/139/138/141/150 overlapping module audits. Original fixture/main pass171/172 audits and actual Lean/Rust execution agrees on9 cases/39 full rows. [Bridge review](../quality/WORD-BRIDGES-REVIEW.json), [fixture review](../quality/WORD-FIXTURE-REVIEW.json). |
| Supplied rational calendars | Private Rust passes34 inputs/259 ordered views and82 tests; candidate main bytes bind the117-case protocol receipt. Shared physical exposure metadata remains symbolic, with full source admission and universal Lean correspondence open. [Review](../quality/CALENDAR-CANDIDATE-REVIEW.json). |
| Ancestral completion | Private completion is independently checked on eleven full tables/330 ordered rows plus five budget and four refusal controls. Its generic Lean bridge passes a140-module audit. Separately, actual original Lean and Rust evaluators agree on six complete tables/257 ordered rows, including permuted and carried genealogies. [Candidate review](../quality/COMPLETION-CANDIDATE-REVIEW.json), [proof review](../quality/SEMANTIC-COMPLETION-REVIEW.json), [actual execution](../lean/ORIGINAL-COMPLETION-NATIVE-EXECUTION-RESULT.json). |

The finite-word row count is `1 + 2 + 2 + 3 + 1 + 1 + 19 + 1 = 30` for
eight cases. Two additional hybrid cases contribute six rows each, giving
42 rows across ten cases. The30 is a subtotal, not another addend. A row is
one complete output state with its probability polynomial. Cases, output
rows, Lean modules and theorem declarations measure different things;
they are not interchangeable and do not define a completion percentage.

The private completion build also passes 71 Rust tests, the unchanged eight
finite-word plus two hybrid controls, and a fresh 117-case Lean/Rust protocol
comparison. These are finite checks, not a general Rust-to-Lean proof.
The complete source/calendar admission pipeline, physical timed readout and
source-to-optimal-policy engine remain incomplete. Original G1/G2/binary M3 G5
Lean results stay complete at their [declared contracts](GOAL-STATUS.md);
full G6/G7 formal and practical assembly remains open.
