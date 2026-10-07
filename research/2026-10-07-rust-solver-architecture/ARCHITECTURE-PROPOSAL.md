# Practical scientific solver: Rust-core architecture and migration proposal

**Status:** design prototype only. Unimplemented, unbenchmarked, and not an adopted roadmap. No repository changes, package installation, deployment, or publication were performed for this proposal.

**Evidence baseline:** the five source files listed in §12 were read at Research-Commons commit `c9a6934ecb09ea22dc0204def2ad6398dfb43fa2` on 2026-10-07. This is a bounded source review, not a repository-wide audit or a claim that those programs were executed. Proposed module names, types, protocols, and tests below do not yet exist.

## 1. Recommendation and decision rule

Make Rust the owner of the production solver's exact arithmetic interfaces, bounded execution, claim construction, and stable application protocol. Preserve access to the strongest specialist engines in their native ecosystems. Keep Python as an independent executable specification and optional research client; Python need not own the application, runtime, GUI, or deployment.

The architectural unit is a **mathematical contract and independently checkable result**, not a language preference. Choose a backend for the actual problem class and required evidence. A capable C/C++ algebra engine, Julia numerical package, Python/Sage symbolic tool, or Lean checker should remain available without becoming the owner of every other part of the program.

Rust is a strong proposed systems foundation, not an established winner for every mathematical algorithm. No performance result supports replacing an existing engine yet. “General solver” means a framework for multiple supported problem classes; it cannot mean a procedure guaranteed to solve every mathematical problem.

## 2. What the current code requires us to preserve

| Component | Source-observed mathematical behavior | Migration constraint |
|---|---|---|
| `count_certificate.py` | Exact `Fraction` recurrence, first qualifying cutoff, normalized-prefix law; `CERTIFIED` or `RESOURCE_LIMIT` | Preserve the count law, first `K`, `S/T/U/delta`, inspected count, and optional exact weights. A limit conveys no negative scientific conclusion. |
| `signed_receiver.py` | Exact rational intermediates; outward dyadic rounding at every interval construction; signed residuals; bounded input grammar and arithmetic; frozen exponential-provider bytes | Preserve operation order, rounding sites, domains, refusals and strict `maximum < 1/20`. Its success is only conditional pair-width certification. |
| `certified_forward.py` | Exact rational interval formulas; bounded Taylor exponential with range reduction; selected dyadic rounding points; 330 feature outputs | Do not conflate its interval policy with the receiver's round-on-construction policy. Preserve exponential and final width contracts. |
| `tight_rounded_betting.py` | Per-row exact replay, lower factors, downward-rounded capital, budget checks before state commit, first threshold crossing | Preserve row order, mixture weights, first crossing, processed prefix, hashes, and conditional exclusion scope. Rounding to nearest is invalid. |
| `verification/run.py` | Frozen-source traversal, pinned Lean executable/Mathlib, serial subprocesses, time/memory settings, dependency blocking, declaration and full custom-environment audits | A driver rewrite must preserve evidence completeness and distinguish selected-module success from whole-workspace or whole-solver verification. |

Important nonclaims are part of the interface. The signed receiver does not perform source-forward evaluation or observation replay; its result does not admit mean-band coverage or prove compatible-source existence. The betting receiver does not verify scientific admission or issue a data-confidence certificate, physical-source exclusion, parameter accuracy, witness, or Lean-kernel claim. These qualifications must survive every adapter and every GUI summary.

## 3. Proposed modules and dependency direction

Start with a small workspace. Split into crates when a boundary needs independent testing or deployment; do not create a dozen crates merely to mirror this document.

1. **`solver-contract`**: versioned requests, result records, exact serialized values, claim kinds, budget definitions, stable refusal codes, and compatibility profiles. No solver algorithms, network, GUI, or foreign runtime.
2. **`solver-arithmetic`**: canonical arbitrary-precision rationals, explicitly directed rounding, checked intervals, budget accounting, and the bounded exponential implementation. No scientific admissions or “certified” public constructors.
3. **`solver-models`**: fixed-model parameter validation, exact formulas, count certificates, signed geometry, and sequential betting replay. Depends on contract and arithmetic. Each algorithm names its model, assumptions, rounding policy, and evidence scope.
4. **`solver-evidence`**: canonical statement/input digests, algorithm and build manifests, certificate serialization, replay/checker interfaces, and evidence status. A digest establishes identity, not correctness.
5. **`solver-runtime`**: bounded jobs, cancellation, deterministic task ordering, backend selection, checkpoints, and subprocess management. Orchestrates models and evidence; owns no alternative arithmetic meaning.
6. **Adapters**: Rust CLI, GUI/client bridge, optional Python bindings, and optional C/C++ bindings. They validate transport and render results, then invoke the same runtime/core. None independently decides whether a mathematical claim is established.
7. **External tools**: specialist CAS/numerical/SMT/proof engines, including the existing Lean driver. Communicate through bounded, versioned adapters. They do not reach into internal core objects.

The inward direction is adapters → runtime → model/evidence modules → arithmetic/contract. Cross-cutting serialization should not make arithmetic depend on GUI or Python. The Lean checker remains logically independent; it consumes a precise claim/evidence package rather than trusting the producer's status string.

Retain the frozen Python sources under a reference/testing role. Differential tests call both implementations through a common corpus. Do not have the Rust candidate call the Python implementation to obtain its supposedly independent arithmetic results.

## 4. Data and correctness contracts

The following are proposed abstract types, not implementation code.

### Exact numbers and contexts

- **`Rational`**: arbitrary-precision signed numerator and strictly positive denominator, reduced canonically. Never a machine integer ratio for unbounded intermediate values. `num-rational::BigRational` is a plausible initial implementation, subject to dependency review and measurement.[6]
- **`Interval<P>`**: validated lower/upper rational bounds with an explicit rounding policy `P`. At least distinguish exact-rational intervals, receiver-style dyadic intervals, and downward-capital arithmetic. Avoid an implicit global rounding mode.
- **`ArithmeticContextId`**: binds precision, budget semantics, algorithm version, and rounding policy. Do not combine intervals from different contexts accidentally.
- **`ExactInput`**: validated representation plus original-input identity. Input parsing is bounded before arbitrary-precision conversion. Canonical mathematical value and original byte identity are different concepts.
- **`Budget`**: input sizes, precision, permitted intermediate sizes, exponential invocations, inspected cutoffs/rows, memory envelope, and optional deadline. Mathematical work counters are deterministic; wall-clock interruption is separately recorded.

Receiver v1 currently checks endpoint bit sizes before outward rounding. The forward provider checks reduced input size and has different parsing/precision contracts. Betting checks specific intermediates before committing the next row. A generic “safer” check inserted elsewhere can change accepted inputs or the refusal point. Compatibility mode must reproduce the existing schedule; preventive allocation caps or stricter validation require an explicit new policy/version and separate tests.

Keep the reference rounding schedule initially. An integer-endpoint dyadic representation may later reduce normalization work, but it can alter intermediate bit accounting. Admit it only after proving or testing the declared equivalence relation, not because both implementations use the word “interval.”

### Outcomes, claims, and evidence

Distinguish:

- `EstablishedClaim`: an exact claim kind, assumptions, statement digest, evidence and scope; constructible only after the relevant checks.
- `Unknown`: valid inputs, but the requested mathematical conclusion is not established; include reason and bounded partial evidence where appropriate.
- `ResourceLimit`: work stopped at a named limit, with the exact progress boundary.
- `InvalidInput`: malformed or outside the supported mathematical domain.
- `ExecutionFailure`: process exit, panic, missing provider, corrupt output, or other operational failure. It is not a negative mathematical result.

A legacy renderer maps these to each existing file's actual schema and behavior. For example, the signed receiver currently reports refusals inside an `UNKNOWN` record, whereas the count component has a distinct `RESOURCE_LIMIT`. Do not silently rename v1 output or swallow operational failure as a successful v1 certification.

Claim kinds should be specific: normalized-prefix certificate, forward-feature enclosure, conditional pair-width bound, or conditional mean-box exclusion. Never replace all of these with an unqualified `CERTIFIED` badge.

Evidence status is independent of the claim kind: arithmetic replayed, reference-equivalent on a defined corpus, independently certificate-checked, or Lean theorem checked. A Rust memory-safety property is not a proof of the mathematics. A checked lemma is not full verification of a program, its parser, statistical assumptions, or its data provenance.

### Stable wire protocol

Use a documented, versioned envelope for requests and results. Include:

- request ID, problem/algorithm/model version, exact inputs, required claim/evidence scope, budget and rounding profile;
- outcome, exact intervals and residuals, progress boundary, assumptions, missing admissions, and refusal details;
- input/statement/certificate digests, implementation/build identity, dependency manifest, checker identity and actual check results.

Serialize large integers and rationals as canonical strings or integer-string numerator/denominator pairs. JSON numbers must not carry arbitrary-precision values through JavaScript. Reject duplicate keys and nonfinite numeric tokens at the protocol boundary. Use named stable ordering for digests; do not hash presentation JSON opportunistically.

An exported result cannot inherit the Python provider hash as its own implementation identity. Preserve that hash as the reference identity, and add the actual Rust source revision, toolchain, lockfile, build features/flags, target, and produced executable digest. Compiled provenance is a separate chain, not the same single-read Python source authentication mechanism.

## 5. Specialist-engine routing for mathematical depth

Represent a problem with its mathematical domain, exact/approximate coefficient semantics, constraints, objective or theorem statement, desired output, evidence requirement and budget. Each backend declares matching capabilities and limitations. The router must be able to return “unsupported by available backends.”

Distinguish three roles:

1. **Candidate producer:** may use approximate numerics, heuristics, symbolic experimentation, or external optimization to propose a point, expression, witness, partition, or proof strategy.
2. **Evidence producer:** generates rational enclosures, finite witnesses, decomposition traces, proof objects, or other checkable certificates.
3. **Checker:** validates the precise certificate against the precise statement and assumptions.

A fast approximate backend may be an excellent candidate producer without being allowed to issue the final exact verdict. Arbitrary-precision floating point alone is not a rigorous enclosure. Proof-producing SMT is useful only for the supported theory and a proof format that the selected checker actually verifies. A symbolic simplification still needs domain and branch conditions.

| Ecosystem's strongest architectural role | When to retain it | Boundary |
|---|---|---|
| Rust application and exact kernels | Bounded services, parallel independent jobs, explicit errors, native distribution, auditable state transitions | Native core API and stable external protocol |
| C/C++ mathematical libraries | A mature algebra, integer, interval, optimization, or sparse-numerical implementation supplies the actual needed capability | Narrow reviewed FFI or isolated process; preserve its exactness contract |
| Python/Sage/SymPy-style research stack | Broad symbolic/number-theoretic tooling, notebooks, reference models and rapid experiment composition | Optional client or backend worker; no mandatory Python production ownership |
| Julia scientific stack | A suitable native numerical/differential-equation/optimization workflow is the real workload | Coarse-grained worker returning typed results and evidence limits |
| Lean and other proof assistants | The required outcome is a theorem with explicit assumptions and a checked proof | Separate proof package/checker with pinned dependencies and audited axioms |
| Other specialized languages/tools | Their existing mathematical engine is demonstrably the best fit for a supported subproblem | Same capability and evidence contract; assess licensing, reproducibility and deployment before adoption |

This is a division of responsibilities, not a ranking of the full mathematical ecosystems. Backend-specific package selection and comparative benchmarks remain separate research. No new backend, license commitment, data disclosure, or deployment is authorized by this proposal.

## 6. Integration patterns, steelmanned

### Native Rust core and Rust CLI

Strongest case: one production runtime, direct exact typed API, straightforward standalone deployment, no IPC for internal operations. It is the proposed default for the existing small exact kernels. It loses when the effort to recreate a mature specialist algorithm outweighs measurable benefit.

### Python client calling Rust

Strongest case: retain notebooks, experiments, rich data tooling and familiar research workflows while moving arithmetic and verdict construction into Rust. Begin with the CLI/protocol for independence; add PyO3 only if in-process ergonomics or measured call overhead justify packaging complexity. PyO3 supports Python extension modules and embedding, so either direction is possible; this design prefers Python as a client.[7] Batch calls across the boundary; do not bounce every rational operation through Python.

### Rust orchestrator calling a specialist subprocess

Strongest case: language independence, crash containment, coarse-grained cancellation, simpler license/runtime separation, and an easy route to existing tools. Appropriate first boundary for Lean and experimental CAS/Julia engines. Costs include serialization, startup, process supervision and deployment of each engine. Set bounded message sizes and output limits. Never accept a backend's success word without validating its schema, problem identity and evidence requirement.

### C ABI or C++ bridge

Strongest case: use the mature native mathematical engine directly, with batching and low call overhead. Prefer a narrow C ABI for stable cross-language consumption; CXX can be appropriate for a deliberately constrained C++ interface.[8][9] Use opaque handles, explicit ownership and buffer lengths, documented thread safety, explicit errors, and no borrowed memory outliving its owner. Never unwind Rust panics or C++ exceptions through an incompatible boundary.

Keep unsafe/foreign code in a small module with a safe checked wrapper. A safe bridge helps uphold type and memory contracts; it does not prove a C++ algorithm mathematically correct. If a library's global rounding state or thread-safety constraints cannot be controlled, serialize access or isolate it in a process rather than pretending Rust ownership makes it safe.

### Lean as an independent checker

Strongest case: an untrusted fast producer can propose evidence while a smaller trusted proof boundary establishes a precisely stated theorem. Do not put Lean in every inner arithmetic loop. Either produce a proof term/package checked under the allowed axiom policy, or formalize a certificate checker and connect its successful evaluation to the exact mathematical proposition.

Do not equate a zero subprocess exit status with this result. Require the expected theorem statement, pinned source/dependencies, complete audit, and exact evidence linkage. Native evaluation or compiler-trusting axioms must not be introduced silently. The reviewed driver already excludes `sorryAx`, `Lean.ofReduceBool`, and `Lean.trustCompiler`, and allows only its named standard axiom set.

## 7. CLI, GUI, cancellation, and reproducibility

The CLI is the first stable user interface. Provide machine-readable results separately from human progress diagnostics. A command completing successfully is distinct from its mathematical outcome; scripts must inspect the outcome, not merely the process exit code.

A GUI may be native Rust or a web-technology shell. It displays the same results and sends the same requests. Keep exact values in strings across a JavaScript bridge. Show claim scope, unresolved conditions, precision/budget and evidence level together. Require no scientific state in a browser global or UI event handler. A local worker process can keep the GUI responsive and isolate expensive jobs.

Cancellation takes effect at an explicit safe boundary: between count cutoffs, rows, independent boxes, or bounded algorithm phases. The result says where work stopped; interrupted work must not be relabeled “no solution.” Checkpoints include exact state, input/algorithm/budget identities, and an integrity digest. Resume only after validating those identities. Betting rows remain sequential because the next state depends on the prior prefix.

Parallelize independent requests, boxes or parameter evaluations first. Fix aggregate ordering and mathematical work accounting so worker scheduling does not change certificates or reported prefixes. Wall-clock-limited jobs may legitimately stop at different points; record that difference instead of claiming deterministic timeouts.

## 8. Incremental migration stages and release gates

| Stage | Work | Gate before proceeding |
|---|---|---|
| 0. Freeze contracts | Archive exact source identities; enumerate inputs, schemas, fixtures, refusal schedules and current execution evidence; separate existing tests from proposed tests | Every existing public mathematical claim and important nonclaim has an explicit contract; no invented build pass |
| 1. Count-kernel pilot | Port only exact normalized-prefix recurrence and weights; add CLI adapter; keep Python reference independent | Exact first-cutoff and full mathematical-output agreement over corpus plus boundary tests; independent recurrence/inequality/normalization checks; benchmark and packaging evidence |
| 2. Arithmetic and exponential pilot | Introduce canonical rationals, both interval policies, directed rounding, exact budget accounting and pinned forward exponential | Exact endpoint equality for compatibility profile; independent enclosure/width evidence where available; signed-floor/ceiling and resource-edge tests |
| 3. Signed receiver | Port formulas and domain checks in their existing order; preserve strict threshold and conditional limitations | Exact residual/interval/bound/status/refusal agreement, source/build identity distinction, tamper tests and no claim escalation |
| 4. Betting replay | Port per-row lower-capital transition and first-crossing logic, including related factor/strategy contracts after reading those sources | Exact state/crossing/prefix/refusal equivalence; replay trace checks; interrupted/resumed versus uninterrupted agreement |
| 5. Common runtime/adapters | Route production CLI through Rust; optionally introduce GUI and bindings | Same results across adapters; bounded inputs/outputs, cancellation, deployment and cross-platform test evidence |
| 6. Optional specialization | Consider dyadic internals, C/C++ backends, parallel batches or specialized search engines | A measured bottleneck or missing capability, explicit semantic policy, matching evidence, and target-platform deployment/license review |
| 7. Optional Lean-driver migration | Replace orchestration only if maintenance/distribution benefit is demonstrated | Exact target and dependency coverage, successful/failed/blocked classification, axiom inventory, source freeze checks and receipts retained |

Each stage can be retained independently. A failed optimization leaves the frozen reference and last accepted implementation available. Changing a numeric backend must not automatically change a model, statistical procedure, theorem statement, or threshold.

## 9. Exact tests and acceptance criteria

### Differential equality, not decimal tolerance

For the compatibility profile, compare canonical rational values exactly and compare every semantically relevant field. Exclude only deliberately renamed implementation/build identifiers from cross-language equality. Compare those identifiers against their own expected artifacts instead. Legacy JSON presentation requires a separate serialization test if byte-for-byte output is a requirement.

1. **Count:** `a=0`; positive rational inputs; epsilon near 0 and 1; zero-step limit; cutoff immediately before/at success; equality cases for both inequalities; exact first `K`; `S/T/U/delta`; weights sum exactly to one with the normalized-prefix law. Test unlimited and sufficient finite budgets on bounded examples. Decide explicitly whether Python bool-as-int and parser quirks are compatibility requirements or versioned corrections.
2. **Rationals and intervals:** negative and positive values, zero, reduced/nonreduced inputs, signed floor/ceiling at exact dyadic boundaries, all multiplication sign combinations, reciprocals of negative intervals, zero-crossing denominators, empty meets, mixed contexts, and raw/reduced/intermediate bit-limit edges. Reproduce differences between the two current parsers rather than merging them accidentally.
3. **Exponential:** zero; values around 1 and every tested range-reduction boundary; the `x >= bits` shortcut boundary; allowed precision endpoints; Taylor/width limits; exact endpoint agreement; correct reversal of input interval endpoints for a decreasing function. Preserve receiver counting of endpoint calls even if a later implementation caches their values.
4. **Signed receiver:** exact allowed key sets, endpoint order, physical boundaries, root/pulse denominators, empty intersections, precision/budget validation, provider tampering, every refusal path, and results just below/equal/above `1/20` where constructible. Test early failures as well as successful records and their nonclaims.
5. **Betting:** invalid row shapes/types; one row and bounded long replays; all-zero/all-one and alternating data; mixed signs in valid projections; precision endpoints; threshold equality; first crossing; refusal before row commit; exact totals/squares/lower capitals/mixtures; input/plan hashes; repeated runs. Reading `joint_betting.py` and `tight_factor.py` is a prerequisite for specifying their full test contract.
6. **Orchestration/checker:** wrong input hash, stale certificate, mutated source, wrong toolchain/dependency identity, missing report, disallowed axiom, missing custom module, failure of a dependency, timeout and process crash. Every case must be rejected or classified precisely, never upgraded by an adapter.
7. **Metamorphic checks:** encode/decode preserves exact values; count weights normalize; known exact values lie in constructed arithmetic enclosures; downward rounding never exceeds its input; checkpoint/resume matches uninterrupted state; adapter choice changes no mathematical result. Do not assume that higher precision or budget makes every existing report monotone without establishing that property.

Differential testing alone can preserve a shared mistake. Pair it with independent algebraic checks, adversarial/mutation cases, and proved arithmetic or certificate properties as they become available. Fuzzing is evidence about tested executions, not formal verification.

### Performance and operational success

Record wall time, CPU time, peak resident memory, exact operation/work counts, output sizes, cold startup, dependency/package footprint and reproducibility. Measure the current Python version and Rust candidate on the same frozen workloads and machine, with multiple repetitions and distributions. Separate kernel cost from startup, serialization and Lean subprocess time. Record debug/release configuration; Cargo optimization and overflow behavior depend on build profile.[10]

Set a meaningful performance or deployment target before deciding a pilot has won. No numerical speedup threshold is proposed as measured here. Correctness, scope, and evidence gates are mandatory even if the new implementation is faster. If it offers no material benefit, keep the smaller provenanced implementation and its clear boundary rather than expanding the rewrite.

## 10. Improvements that can be bundled carefully

Low-risk companion work: one documented status schema; deterministic golden fixtures; shared exact serialization; structured refusal codes; evidence manifests; explicit progress/cancellation; independent replay; and clearer UI wording for conditional results.

Benchmark-led later work: dyadic endpoint storage, reusable allocations, batched FFI, independent-job parallelism, memoization with fully specified keys, and streaming input processing whose hashes/order remain equivalent. None may weaken outward/downward rounding or silently move the resource boundary.

Separate approval/design tracks: new scientific models, replacement count laws, different statistical tests, new confidence/coverage claims, widened data admission, new approximate-versus-exact policies, network services, public publication, or a GUI product commitment. A language migration supplies no scientific validation for these changes.

## 11. Stop conditions and unresolved decisions

Stop promotion if an accepted claim loses a caveat, an endpoint/refusal differs unexplained, a first crossing moves, a proof audit is incomplete, a build identity is unverified, unsafe/foreign ownership cannot be justified, or a backend license/deployment requirement is unmet.

Before implementation, decide the first real workload and target machines, supported input/output compatibility policy, memory/time envelope, desired evidence level, and whether a standalone CLI already satisfies the practical need. Choose an arithmetic dependency only after testing the required ranges and build targets. Do not select a GUI framework or an extensive backend catalogue before the numerical contract is stable.

Dependency approval includes the build path. Cargo compiles and executes package build scripts before building the package, so a proposed dependency is not merely passive mathematical source.[11] Review and pin the transitive dependency graph, build scripts, native-library discovery and code generators; record the actual build inputs and respect the existing installation/execution permissions. A dependency from an unfamiliar source is not made trusted merely by placing it in a Cargo manifest.

The smallest informative next experiment is a count-certificate Rust pilot with exact differential tests and a benchmark report. It can validate tooling, certificate serialization, resource semantics and distribution without committing to a wholesale rewrite. It does not establish that the later solver is complete, fast, formally verified, or scientifically admitted.

## 12. Source record

Repository sources read at the fixed commit:

1. [Exact normalized-prefix certificate](https://github.com/Sodelin/Research-Commons/blob/c9a6934ecb09ea22dc0204def2ad6398dfb43fa2/research/2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py).
2. [Signed pair receiver](https://github.com/Sodelin/Research-Commons/blob/c9a6934ecb09ea22dc0204def2ad6398dfb43fa2/research/2026-10-07-cloud-practical-signed-guard-2159z/signed_receiver.py).
3. [Certified forward evaluator](https://github.com/Sodelin/Research-Commons/blob/c9a6934ecb09ea22dc0204def2ad6398dfb43fa2/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py).
4. [Downward-capital replay](https://github.com/Sodelin/Research-Commons/blob/c9a6934ecb09ea22dc0204def2ad6398dfb43fa2/research/2026-10-07-cloud-practical-1619z/tight_rounded_betting.py).
5. [Frozen-source Lean verification driver](https://github.com/Sodelin/Research-Commons/blob/c9a6934ecb09ea22dc0204def2ad6398dfb43fa2/research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/run.py).

Technical references checked on 2026-10-07; these are candidate-interface documentation, not dependency selections:

6. [num-rational documentation](https://docs.rs/num-rational/latest/num_rational/), including the arbitrary-precision `BigRational` alias.
7. [PyO3 user guide](https://pyo3.rs/main/), Python/Rust interoperability.
8. [Rustonomicon: FFI](https://doc.rust-lang.org/nomicon/ffi.html), boundary ownership, unsafe interfaces and calling conventions.
9. [CXX project documentation](https://cxx.rs/), constrained Rust/C++ bridges.
10. [Cargo build profiles](https://doc.rust-lang.org/cargo/reference/profiles.html), optimization, overflow checks and panic strategy.
11. [Cargo build scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html), code executed during package construction and native-library integration.

**Verification of this proposal:** source inspection and documentation review only. No migration code, test execution, performance measurement, formal proof, deployment or publication is claimed.
