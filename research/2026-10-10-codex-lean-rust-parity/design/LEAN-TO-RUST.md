# How Lean, Python and Rust fit together

## Dated integration update — 10 October 2026, 20:56 UTC

The current [coherent1,497-module library review](../quality/HISTORY-ACCEPTED-UNION-1497-REVIEW.json)
now includes the separately accepted semantic, actual-gathering and original
completion libraries omitted by the earlier1,487 context. Native frontend,
core, runtime and protocol bytes were unchanged during this history review.
The [runtime assembly audit](../rust/notes/HISTORY-RUNTIME-ASSEMBLY-AUDIT-20261010T2043Z.md)
finds existing source fitting and restricted policy implementations to reuse.
The key interfaces are lossless request representation, logarithmic witness
rates versus rational calendar inputs, original parent orientation and timed
history. Lean proves its stated model; finite parity does not automatically
prove a Rust binary. The earlier discussion and dated receipts follow.


Codex coordinator, 10 October 2026, 10:48 PDT. Explanation and dated status;
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
not collections of packages or compilers. Lean has no standard build hierarchy
called an epoch; any build-run use of that word is informal terminology.

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
| Supplied rational compression | Private Rust port at M=2,3,4 passes10 tests,8 certificates,25 controls and331 saved row transfers. Generic soundness98, fixture/Main99/100, actual9 outcomes, kernel Facts100 and checked original rows101 pass separately. Accepted libraries enter the1,487 union. Native refinement, arbitrary-real extraction and legal source reconstruction remain open. [Chain](../quality/RATIONAL-COMPRESSION-CHAIN-REVIEW.json), [checked rows](../quality/RATIONAL-COMPRESSION-CHECKED-ROWS-REVIEW.json). |
| Concrete original-calendar physical laws | Separate200/201/202 phase/root/law audits now bind sorted phases, initialization, every raw endpoint and completion to the selected physical PMF for the three fixed calendar families. Finite nonempty samples, positive shared rates, interior gammas and exact durations remain explicit; timed merger ages are not retained. [Law review](../quality/ORIGINAL-CALENDAR-LAW-REVIEW.json). |
| Named original decoder/registry | Fixed N2 fork and NP parallel instances pass a172-module audit; three exact Rust requests match the typed code projections and preserve parent occurrences2/3. Generic native parsing/validation and source census remain separate. [Proof](../quality/NAMED-CALENDAR-SOURCE-ADMISSION-REVIEW.json), [input review](../quality/NAMED-CALENDAR-INPUT-REVIEW.json). |
| Connected Lean library baseline | Latest1,487-module library union retains all earlier1,463 source pins and integrates the accepted compression/calendar-law/decoder consumers. Authenticated earlier components plus fresh aggregate/full audit:100,217 unique declarations/91,274 theorem declarations, no owned/nonstandard axioms or missing modules. Two executable Main modules retain separate checked contexts after a preserved collision. [Union review](../quality/INTEGRATED-LIBRARY-UNION-REVIEW.json). |
| Original population recurrence | Eight actual original Lean/Rust/independent-generator comparisons pass. [Receipt](evidence/population-lean-rust-review-1/RECEIPT.json). |
| Mixed-population epochs | Eight ordinary and one parallel-edge original Lean/Rust/reference comparisons pass. [Ordinary execution](../lean/ORIGINAL-EPOCH-NATIVE-EXECUTION-RESULT.json), [parallel execution](../lean/ORIGINAL-PARALLEL-EPOCH-NATIVE-EXECUTION-RESULT.json). |
| Boundaries | Generic sparse source-boundary theorem passes a 133-module audit; all twelve actual original Lean/Rust/reference full-table comparisons pass separately. [Proof review](../quality/EFFECTIVE-BOUNDARY-REVIEW.json), [actual execution](../lean/ORIGINAL-BOUNDARY-NATIVE-EXECUTION-RESULT.json). |
| Finite operation words | Eight original cases plus two natural hybrid controls pass full-table/reference comparisons. Root independently checked all 42 captured full rows, exact work, literal witnesses and frozen build identities. [Review](../quality/WORD-CANDIDATE-REVIEW.json). |
| Actual finite-word source and execution | Concrete source bridges pass135/139/138/141/150 overlapping module audits. Original fixture/main pass171/172 audits and actual Lean/Rust execution agrees on9 cases/39 full rows. [Bridge review](../quality/WORD-BRIDGES-REVIEW.json), [fixture review](../quality/WORD-FIXTURE-REVIEW.json). |
| Supplied rational calendars | General Rust frontend is integrated into `calendar-law`. Its11 new tests, independent34 inputs/259 ordered views,18 adapter plus6 independent controls, and14 current launcher checks plus4 lifecycle/request-binding controls pass. Shared physical exposures remain symbolic; full source admission and universal Lean correspondence remain open. Earlier private82 tests and unchanged RC1 exact117 receipt remain separate. [Application review](../quality/CALENDAR-APPLICATION-REVIEW.json). |
| Generated-calendar root and completed coefficients | Separate170-module complete Lean audit proves every naturally initialized raw calendar endpoint has an ancestral root, including zero-coefficient rows. It supplies the old completed-word premise under nonempty-copy, original initialization, positive rates and SameOrder assumptions. Universal native parser/phase/slot/encoder correspondence remains separate. [Proof review](../quality/RAW-CALENDAR-ROOT-REVIEW.json). |
| G6 original population generator | Separate93-module complete audit proves the physical capped law, identity at survival one, original ordered half-rate generator and coarse full-row L1 remainder, consuming old coefficient/power bounds. Positive compression now passes a separate95-module audit; its real-weight existence proof is noncomputable, so a Rust extractor and legal source reconstruction remain separate. [Proof review](../quality/G6-GENERATOR-REVIEW.json). |
| Phase-permutation source integration | Separate181-module audit transports complete valid phase lists to the original same-bank physical PMF and supplies raw-root support. This is distinct from symbolic independent-slot polynomial equality and native parser/phase/slot refinement. [Proof review](../quality/CALENDAR-PHASE-REVIEW.json). |
| Integrated completed-calendar execution | Three actual original Lean completed-word evaluations match saved actual Rust outputs at38 full ordered views/66 terms. Canonical mathematical tables agree after normalization; witnesses are independently checked. The later finite physical-law consumer has separate premises; universal refinement remains open. [Combined review](../quality/CALENDAR-FIXTURE-REVIEW.json). |
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

The [32-provider extractor audit](../reuse/G6-LEGAL-FACTOR-EXTRACTOR-AUDIT-20261010T1618Z.md)
recovers the existing exact rational geometric-moment elimination algorithm. Its
bounded private Rust port and a rational certificate-to-original-row Lean consumer
now pass the scoped checks above. This reuses the common-atom baseline; it does not
identify rational atoms with generally transcendental calendar survival values.
