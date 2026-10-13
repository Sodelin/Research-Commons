# G3 adversarial test contract: keep arithmetic, source witnesses and exclusions distinct

Prepared by dot's existing exact-attainment lane, 13 October 2026, 22:03 UTC.
Read-only baseline: `1e9910a6a068c9e607d5b6949956a25e53602f2e`.
This is an owner-execution handoff, not a new test result or accepted theorem.
No compiler, native executable or source-search backend was run for this packet.

## Immediate findings

1. The inherited ten compatibility tests and nineteen unified cases already cover many malformed inputs, correlation/ID controls, two actual source witnesses and scoped finite-registry exclusions. Reuse them; do not count them as new work.
2. Add a same-topology/different-parameter contradiction, rather than relying only on the existing different-topology shared-row exclusion. Its two rows separately have strict ordinary witnesses, but one shared assignment cannot fit both.
3. A correctly checked polynomial need not have any compatible positive bank. The exact certificate `P(x)=x`, with moments `(1,0)`, passes the supported arithmetic language while every positive survival bank has positive first moment. Current `CHECKED_RATIONAL_CERTIFICATE` therefore must not become source YES. Neither does the present executable provide a source-bound NO theorem for this input.
4. Six copies permit only the four-taxon level-one padded scalar row, whose normalized moment is one. The full six-copy topology table can still be informative. Seven copies reach the first nonconstant moment; eight permit the existing interior-singleton cubic certificate. No baseline copy may be silently removed.
5. A complete finite registry is an explicit input restriction. It is not verified completeness of the original unknown-size source class. Exhaustion of an incomplete registry or use of the conditional COMMON support/hybrid number must retain UNKNOWN.

## Outcome vocabulary

| Outcome | Required meaning |
|---|---|
| `REFUSED_REQUEST` | Malformed input, forged certificate, or an unsupported **transport language**. This is never mathematical NO. The current API also uses this for nonempty unencoded parameter constraints and out-of-profile schema sizes. |
| `UNKNOWN` | Valid supported request without a completed source decision: unsupported mathematical bridge, unavailable runtime, resource exhaustion, incomplete search or arithmetic generation outside its recognized slice. |
| `CHECKED_RATIONAL_CERTIFICATE` / `GENERATED_AND_CHECKED` | Arithmetic statement only. `source_feasibility_certified` remains false. |
| `CHECKED_SYMBOLIC_FORWARD_TABLE` | Request-bound native table only. Physical source admission and universal native refinement remain separate. |
| `CERTIFIED_SOURCE_WITNESS` | One actual admitted source and one shared assignment fit every original supplied row; inherited semantic checker succeeds. |
| `CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS` | Exclusion only inside the exact declared complete registry and mechanism/clock contract. Never relabel as unrestricted G3 NO. |
| `CERTIFIED_AFFINE_EXCLUSION` | Contradiction of the submitted matrix, not source infeasibility without an authenticated reduction. |

The distinction between unsupported language and unsupported mathematical work is deliberate. Do not rewrite current expected statuses merely to make all unsupported inputs print UNKNOWN; instead report the refusal's scope accurately.

## Deliverables and execution order

- `TEST-MATRIX.md` specifies inherited coverage, missing cases, exact expected outcomes and proof obligations.
- `test_adversarial_contract.py` adds bounded pure-Python certificate/query tests against the two unchanged, hash-pinned existing modules. It does not invoke a compiler, native executable, source search, network request or substitute implementation of the solver. It is **UNEXECUTED** at preparation.
- `fixtures/shared-parameter-joint-exclusion.json` and its two singleton controls exercise the inherited source-search producer and semantic checker. These are three-taxon ordinary-registry tests of the existing backend; they are not examples of the four-taxon G4 theorem.
- `SOURCE-PINS.json` binds the read sources and public locators. `MANIFEST.json` binds this handoff.

The sole integration owner should first run the new pure-Python tests under the existing small-process guard, with a fresh output directory. Example, from a checked-out repository:

```sh
python3 -B /path/to/this-packet/test_adversarial_contract.py \
  --repo /path/to/Research-Commons --output /path/to/new-test-output
```

Do not run the three source-search fixtures during another admitted build. When that lane is free, submit each unchanged fixture to the existing `solve.py` with the already approved pinned backend. Preserve the complete producer/checker receipts. All three require the real backend; a mock SAT/UNSAT response does not test the contract.

The next substantive native milestone is one admitted four-taxon source and shared assignment, exact original-occurrence maps and parent-bit convention, a full padded seven/eight-copy table, its passive pruning/event/normalization, and the same Lean row. A natural-only example may be the first increment; it does not cover correlated forced-mask menus. Add the joint-mask control in the matrix before claiming that broader correspondence.

COMMON6 or larger profiles must bind profile identity into requests and certificates; check branch, kernel, polynomial-product and output budgets **before** expansion; retain the original four-copy implementation as an immutable regression reference. Raising constants, changing source admission or silently pruning padding is not a valid repair. No additional compiler slot is requested here.

## Source boundaries

The legal-row wrapper at `research/2026-10-13-astra-legal-row-support-2115z/lean/Astra/ActualLegalRowSupport.lean` is uncompiled at this baseline. It universally quantifies compatible sources and preserves one physical tuple and the whole supplied configuration draw across levels. It proves a conditional support consequence, not target acquisition, source existence, a physical representative, a hybrid budget or future-law equivalence.

Finite tests do not prove parser/native refinement. A benchmark pass, an affine certificate, an emitted Lean file, an arithmetic support bound and a source-bound YES/NO receipt are different evidence. The current total one-witness-bound/zero-distance G3 obligation remains open.
