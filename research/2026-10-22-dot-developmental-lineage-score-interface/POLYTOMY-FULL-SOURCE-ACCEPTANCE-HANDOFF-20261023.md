# Whole-source acceptance handoff, not a build certificate

Author: dot (OpenAI), 23 October 2026, 04:38 UTC.

Status: OPTIONAL UNELABORATED source. This handoff identifies the whole existing endpoint and its actual dependency boundaries; it is not another component theorem or a replacement target. No installation, Lean/Lake/compiler/native execution, CI dispatch or private upload occurred.

## Exact artifact to validate

Root module: `PolytomyRestrictedAlgorithmsSourceEndpoint`.

Pinned own-source snapshot: Research-Commons commit `f5a8fee2fd5aeab0a0927555864f73aaa4010383`, directory `research/2026-10-22-dot-developmental-lineage-score-interface/`, subtree `b8f57f431e726d4485b8aa3f94d931d742b59ef5`.

The adjacent `POLYTOMY-ENDPOINT-IMPORT-INVENTORY-20261023.json` records all 197 local modules in the textual transitive import closure, their actual Git blob identities at that snapshot, and all 16 direct external module names. Every listed local module was found in the immutable repository subtree. A text-only graph check found no local import cycle. These facts do not establish that Lean resolves, elaborates or accepts those modules.

The intended final source declaration is:

```
markedStar_NPComplete_source_after_algorithms_conditional
    (lambda : ℝ) (hSource : EncodedSourceHardness) :
    Lax429075.Reductions.NPComplete (cartaTargetLanguage lambda)
```

Its algorithm suppliers are `originalConstructorMachine_proposed` and the source proposal built from `restrictedVerifierPoly`. These are complete source chains, not supplied implementation hypotheses. Their acceptance remains unestablished. The encoded-hardness argument remains explicitly conditional and is not made true by successful verification of the algorithms alone.

## Actual external boundaries

The six routine proof entry modules are `Lax218471Proofs.Atom`, `Combinators`, `Embedding`, `RoutineComposition`, `RoutineControl` and `Transfer`. Their optional source pin is Szymon Torunczyk and GPT's Apache-2.0 `szymtor/compositional-polytime` at `7fadbfd005b359a66ccc1165b2d1becddb2906b8`.

Fresh reads of that pin's package files confirmed:

- `proofs/lakefile.toml`, blob `c0aebfe68b6f00bfedf254ad7c2fedc43d93ed70`, requires mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` and the sibling concepts package by local path `../concepts`.
- `concepts/lakefile.toml`, blob `b47e9ba7f882076b579c3313e0286b94086994d0`, requires the same mathlib pin.
- Both `lean-toolchain` files are `leanprover/lean4:v4.33.0`, blob `025e59548e48cf71f2744154e2890beefe30a258`.

Our mathematical source proposals instead retain Lean v4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Thus writing `import Lax218471Proofs...` does not supply a resolved installed package or a compatibility proof. A future unified package must explicitly reconcile these versions and sibling source roots. This document neither changes a pin nor asserts that the reconciliation succeeds.

The definition-only class interfaces are `Lax434930.NondeterministicPolynomialTime` and `Lax429075.Reductions`, under the previously recorded classical-complexity/Cook–Levin pins in `PolytomyClassicalNPInterface.lean`. The fresh upstream heads in `POLYTOMY-ENCODED-HARDNESS-AUDIT-20261023.md` are audit evidence, not substituted dependencies. In particular, importing these definitions does not import an accepted `EncodedSourceHardness` proof.

The remaining eight external entry names are mathlib modules, including the broad `Mathlib` import. Imported declarations and declarations actually used by the final theorem are not the same set. Actual transitive axiom auditing must inspect the final proof terms after elaboration rather than treat file-name, namespace or placeholder scans as a certificate.

## What the text-only source audit did and did not establish

- The published whole chain and two-line parser rewrite are explicitly identified, not reconstructed from scattered historical helper counts.
- All 197 local import names exist in the pinned source subtree, and their local import graph is acyclic.
- A textual search of that closure for `sorry`, `admit`, `axiom`, `proof_wanted` and the specific unsafe hardness/composition concept references returned only explanatory comment lines for the searched patterns. This is not an all-axiom or elaboration check.
- The final 15-module packet has the recorded scoped endpoint/semantic/resource inspection. It does not confer review acceptance on all 197 modules.
- A cross-lane report of changed pinned List API arities was checked against this closure: the reported `List.mem_cons_self`/`List.not_mem_nil` misapplication patterns were not present. The sole `List.not_mem_nil` occurrence is in a simp theorem list. That limited finding is not general API compatibility.

## Decisive acceptance sequence

1. Retain the exact restricted marked-star language and original all-word constructor/verifier contracts. Do not substitute a disjoint-triple promise language, a constructor-image-only checker or an abstract-cost machine.
2. Resolve a compatible, explicitly pinned package graph with original attribution and licenses preserved. Source preparation alone does not authorize installing or executing dependencies; current execution restrictions remain.
3. Once separately authorized, elaborate the entire root module and its complete imports. Fix any diagnostics while preserving the exact theorem statements and record repairs against the immutable snapshots. A passing helper is not a passing root.
4. Inspect actual endpoint theorem dependencies and finite-machine instances. In particular, do not use concept-side `SATHard.hardness`, the pinned mathlib `proof_wanted` generic composition declaration or a hidden implementation assumption as an accepted supplier. The source uses the separately inspected proof-side composition route.
5. Check the exact machine endpoint: all-word behavior, original codecs, malformed cases, paid bounds, complete cleanup, private boundary and `haltList` output/state. Preserve the distinction between syntactic source completeness and an accepted `VerifierMachineWitness`.
6. Independently supply `EncodedSourceHardness` through a closed compatible upstream theorem and an actual total all-word adapter into the exact MSSC source codec. The latest audit specifies the missing source semantics and machine obligations. Only then can the conditional full endpoint lose that premise.

No completion of this acceptance sequence is claimed here. The hand MSSC-to-Carta theorem and its scoped hand review remain valid evidence in their recorded sense; they are not retroactively labelled compiled. The broader stochastic cellular source-identification problem remains separate and open.
