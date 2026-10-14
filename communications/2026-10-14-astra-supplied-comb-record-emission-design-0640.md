# Supplied COMMON input-record emission: bounded design

Status: **DESIGN ONLY; no implementation, import, query, test, or compilation performed.** This is an additive proposal after source inspection. It does not change any frozen emitter, runtime, provider, or selection. Root chooses implementation and the compiler owner chooses execution.

The existing exact emitter is sufficient in principle for the full supported certificate language, without restricting the new constructor to cubic certificates. The missing output is a literal `DotG3.CertifiedCommonBoundedWitness.SuppliedCombCertificates (Fin n)`. Its eight fields contain only supplied levels, values, coefficients and their arithmetic proofs; there is no unknown physical source `P` field.

## Proposed minimal construction

1. Read original menu bytes through the pinned `certificates.loads` and validate the whole menu with `common_packet`. Its `UNKNOWN` source-decision result is expected and must remain unchanged. Preserve raw bytes and their SHA separately from the canonical menu digest. Do not reconstruct the input from a result JSON.
2. For each distinct original certificate digest, call unchanged `emit_support.render`. Preserve its base and support sources byte-for-byte. Dedupe files by digest only; retain every ordered-pair reference, including diagonals, duplicate mathematical certificates with distinct token spellings, and repeated uses of one certificate.
3. Add one thin per-certificate module with a literal `value : Nat → ℝ` (the supplied values at 1 through L, zero elsewhere) and a constant `SuppliedCombCertificates Unit`. Its coefficient function is the existing emitted `coefficients`, not a reconstructed alternative polynomial. Discharge:
   - `level_pos` by literal arithmetic;
   - `nonzero` from the existing `polynomial_identity` and `nonzero_value`: a zero sparse polynomial would make its evaluation at the existing concrete test point zero;
   - `nonnegative` by rewriting through that same identity and applying existing `nonnegative` to the two components of membership in `[0,1]`;
   - `annihilates` by the existing `levels_eq`, literal coefficient/value simplification, and the existing base `annihilation` theorem. No bank, root, support-cardinality, or law premise is needed.
4. A small reusable Lean assembler takes `row : Y × Y → SuppliedCombCertificates Unit` and builds `SuppliedCombCertificates Y` by field projection at `((),())`. The generated menu supplies a total finite table for `Y = Fin n` in the original taxa-list order. This avoids duplicating proof obligations at every pair. Use explicit finite constructors or an authenticated selected vector API; no search-dependent indexing or graph indices.
5. Emit exact projection checks for every row's level and every supplied coefficient/value index, plus companion literal taxon and certificate-ID tables. The output manifest binds each row's original menu index, original i/j labels, Fin indices, canonical certificate digest, raw rational tokens, normalized rational values, level, exact exponents, generated declaration names and source hashes. The target Lean structure itself has no certificate-ID field: the companion table/manifest supplies identity provenance; it must not be described as a Lean SHA256-refinement theorem.
6. Reuse `external_encoding.fixed_queries` for the query ledger. Keep each original certificate digest and exact row digest, allocation, configuration table, masks, normalization coefficient and derived raw observation requirement. These are supplied requirements, not checked physical observations. Keep the same joint configuration table, including zero-mass entries, in retained input/ledger bytes; no factoring or renormalization.

No new probability decoder, native arithmetic implementation, certificate format, source inverse solver, or probability acquisition method is required. A separate additive CLI can consume a validated `supplied_common_menu_v1` input and emit this record. It can later be composed with the existing common-menu path through a new reviewed entry point; frozen `runtime.py`, `solve.py`, `certificates.py`, `emit_lean.py` and `emit_support.py` need not change. The existing native checker and its wire remain reusable optional corroboration, not proof of the emitted Lean record.

## Supported profile and refusal boundaries

Reuse the current exact grammar: 256 KiB request, JSON depth 64, 4–8 taxa, exactly n² ordered pairs including diagonals; typed taxon/PE/PH ID namespaces are independently unique and may share text across namespaces. There are 1–32 complete joint configurations of exact nonnegative mass summing to one, and the supported parameter-constraint list is empty. Do not silently drop ties or add protected IDs.

Each certificate has L in 1–8, L coefficients and values, exponents `k choose 2` for k=1,…,L, a nonzero coefficient vector, first value 1 and all values in [0,1], 1–16 rational nonnegative weighted-square terms, at most 15 square coefficients and endpoint factors in {1,x,1−x,x(1−x)}. Exact rational tokens have at most 80 characters and reduced numerator/denominator at most 128 bits. The existing checker verifies the exact SOS identity and annihilation. Zero coefficients and a nonzero test point other than zero are legal. The degree bound is 28, with at most 29 existing bounded nonzero probes.

Although L=1 is within the syntax, there is no accepted L=1 certificate under this checker: nonzero constant c and y1=1 contradict c*y1=0. This is an arithmetic refusal, not an unknown physical decision. L=2 can accept a purely input-side certificate such as p=x and values (1,0); that does not assert a positive-survival physical realization. The constructor must not add such a premise or turn absence of a source into a decision.

Proposed additional emission budgets: 64 unique certificates, 16 MiB total newly emitted payload, 256 MiB address space, 30 CPU seconds and an owner-selected finite wall guard (suggested 60 seconds). These are proposed limits, not observed performance or a guarantee every maximal input will compile. Validate the total output before publishing a complete manifest; preserve any partial/failed receipt. A valid certificate that exhausts emission/compilation resources remains `UNKNOWN` for this operation, not a negative source answer. Malformed/unsupported transport retains the existing explicit refusal. Unsupported future schema/certificate profiles receive an explicit unsupported status without weakening their obligations.

## New files only if implementation is authorized

An isolated packet would contain `emit_supplied_menu.py`, a small `lean/Astra/SuppliedCombCertificateAssembly.lean`, focused emitter tests, bounded menu fixtures, and an additive Lake/audit target. Generated outputs would contain unchanged `Certificate_<digest>.lean` and `Support_<digest>.lean`, new per-certificate wrappers, one menu aggregate and an input/query/identity manifest. No changes to frozen 2350 runtime/proof sources or recovered accepted provider are necessary.

The new bridge imports the exact consumer `400153aa…`; generated per-row modules also import the existing emitted support module. Its support/kernel dependencies must resolve to the authenticated selected versions. The implementation must fail closed on source pin or module-origin mismatch; it cannot infer compatibility from a same-named declaration.

## Focused validation after owner approval

Bounded Python controls should check: complete pair coverage; missing/duplicate/unknown/diagonal-pair rejection; original taxa order and original pair-list order retained separately; legal same-text IDs across typed namespaces; no merge of distinct certificate token identities; repeated digest reuse with all row references preserved; mixed levels including zero coefficients and nonzero evaluation away from zero; endpoint 1; exact current SOS/annihilation refusals; rational, JSON and emission-budget limits; nonempty parameter ties refused; and zero-mass/correlated configurations kept without renormalization.

Differential checks should compare generated literal coefficient/value/level projections and query-ledger rows against the same pinned checked input and existing `fixed_queries` results. Mutating a coefficient, moment, polynomial identity or wrong row reference in a generated proof fixture should fail the appropriate equality/identity audit, without claiming this small corpus proves generator refinement. Reusing an identical certificate for another pair is legal, so mutation controls must use numerically distinct row data when testing pair misbinding.

The owner’s narrow serial Lean run must first authenticate/compile the exact recovered provider and consumer closure, then the new assembler and a bounded set of literal generated wrappers/menus. Include a mixed-L menu, L2/zero-constant certificate, cubic endpoint-1 certificate, and a sparse degree-28 L8 certificate; include literal projections and printed theorem types/axioms for the actual `SuppliedCombCertificates (Fin n)` value. L1 belongs in the rejection controls. All newly compiled components must be listed separately from authenticated reused dependencies. A successful wrapper aggregate would not mean a from-scratch rebuild or acceptance of every possible emitter input. No `axiom`, `sorry`, `admit`, or `native_decide` is proposed.

## Exact remaining semantics

Emission alone is `compiled = false`. Even an actual compiled record certifies only the arithmetic properties of supplied inputs. It does not supply `hmatch`, prove that normalized moments came from the same physical source/parameter tuple, authenticate the fully expanded protected footprint h, instantiate physical/outer admission, or prove a native/Lean parser or solver refinement. Current raw declared PE+PH counts remain metadata and must not become an effective complete search bound. The original arbitrary correlated PMF and fixed external encoding remain binding obligations. The conditional representative theorem and finite code coverage do not themselves implement exact parameter feasibility or a terminating arbitrary-input G3 decision. Physical/source decisions remain `UNKNOWN`.

## Exact inspected source ledger

| Relative path under Research-Commons | SHA256 |
|---|---|
| research/2026-10-13-astra-unified-solver-0645z/certificates.py | ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3 |
| research/2026-10-13-astra-unified-solver-0645z/emit_lean.py | 27264a92409966415094b902df8226e7a86f305c0cef148325c7f6f60795ae37 |
| research/2026-10-13-astra-emitted-support-2110z/emit_support.py | 6e7dc1faea63642464b802b59aceed7c809ea2f5148abb62bca36dab9b11bfdd |
| research/2026-10-13-astra-unified-solver-0645z/lean/Astra/CommonCertificateKernel.lean | 1f35f9e11cef727b27ed30230a390ada2a32dfc50733ea0d4cb172fb7c053266 |
| research/2026-10-13-astra-positive-support-adapter-0830z/lean/Astra/PositiveSupportAdapter.lean | 29782b7ff42fefd5b1634e20ea1f0c695714e5cd625c2730a255bbda656ab479 |
| research/2026-10-13-astra-unified-solver-0645z/external_encoding.py | 78dfd11a8157a5102c520be85a5fc42f4b4137250846ce510df9df98a90f4d69 |
| research/2026-10-13-astra-unified-solver-0645z/solve.py | cebe79e7fcebe554faaf38580b831770f5c877affc41020b891d830532080b9e |
| research/2026-10-13-astra-unified-runtime-2350z/runtime.py | 07c9e49cd05eea2ac9fe590a0f3b01c922da08deefc55f1c5ca01da4711e7f4b |
| research/2026-10-13-dot-g3-certified-consumer-0631z/G3CertifiedCommonBoundedWitness.lean | 400153aac6adeb8905447f38c616a7d4008605668ffb2d2846dc9a9d5673f94c |
| research/2026-10-14-astra-exact-0616-provider-recovery-0555z/source/G4ProtectedCommonRepresentative.lean | 0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04 |

This review read and hashed only the bounded selected source set. It performed no helper imports, native runs, Lean queries/compiles, object inspection, or publication. Earlier execution receipts remain earlier evidence; this note does not assert a new successful receipt or complete public 1614 delivery.
