# Additive portable reproduction contract

The executed local result is the [qualified 53-profile union certificate](https://github.com/Sodelin/Research-Commons/blob/a8545d355ff01e8959847af1d6b04b097624ed39/research/2026-10-10-dot-connected-53-qualified-certificate-0842z/README.md). This new reproduction configuration has passed source-pin validation, bounded policy controls and Lake configuration elaboration. It has **not** undergone a fresh end-to-end mathematical run from the public layout.

## Entrypoints and preserved history

`lake build connectedQualified` selects exactly the 53 required profiles in the frozen graph. The original `connected`, `candidates`, `verify` and historical `remaining49` definitions are preserved byte-for-byte as the prefix of the additive Lake file. The old default `connected` command still uses the historical 4 GiB aggregate limits; it can reproduce the recorded aggregate memory failures. Use the explicit new target for the qualified policy. The historical `remaining49` continuation requires its original run records and raw execution graph; it is provenance, not the portable fresh-run path.

The wrapper calls the byte-identical reviewed `build_connected.py`. It does not require any old run, failed receipt, author pathname, object cache or prefilled pass list. A fresh directory compiles every selected component context; subsequent exact-context reuse is reported by the unchanged cache mechanism. Compiler, source, imports, object/IR companions, measured native libraries and namespace resolution are bound to the new run. The public graph has only a provenance-path projection; the selected mathematical execution graph is unchanged.

## Exact resource policy

- Ordinary components, aggregates and full owned-declaration audits: 4,096 MiB, original wall bounds.
- Existing component exception: only `ThetaCertificate5` at source SHA256 `e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab`, 6,144 MiB/600 seconds.
- Only `connected/compatible` aggregate and complete audit: 6,144 MiB/300 seconds each, all 1,124 selected modules.
- Only `connected/20261009-canonical` aggregate and complete audit: 6,144 MiB/180 seconds each, all 1,411 selected modules.

Every 6 GiB invocation requires at least 7 GiB measured available memory initially. An active observer stops on less than 1 GiB available or uncertain observation. These are bounded Linux memory observations, not a claim about inaccessible cgroup settings. Compilation remains serial, trust zero, kernel checking enabled. No theorem statement, proof body, import, selected module, axiom criterion or audit is removed.

The wrapper records its own SHA256, graph/core/audit/compiler/mathlib/native identities, exact generated aggregate/audit source hashes, exception scopes and effective per-invocation resources. Its `RESOURCE-QUALIFIED-FINAL.json` is authoritative for this entrypoint. The unchanged core's `FINAL-RECEIPT.json` remains preserved and is explicitly linked to that qualification rather than silently rewritten.

## Fail-closed additions

Every source-store file used by all 78 inventoried profiles is checked before execution. The exact 53 required selector and the two aggregate scopes are pinned. Invocation validation refuses source/import/name/object-mode/time/resource drift. Import measurement must agree with Lean's literal first namespace-root lookup; sparse namespace fallback is rejected. Audit success additionally requires stable runtime/source/import bindings, even when the process returns zero. Component failure-key handling remains in the original core.

The package provides complete owned-declaration axiom/reference census coverage. It does not claim full type/body DAG equivalence or verified runtime behavior of generated companions; those are different obligations. It does not turn the 25 provisional profiles or later candidate extensions into accepted passes.

## Validation performed

`POLICY-TEST-RESULTS.json` records 25 bounded controls, 14,021 component-context contracts, 156 generated aggregate/audit contracts, and 1,439 selected source versions. No mathematical compiler was invoked by those tests.

`LAKE-CONFIG-VALIDATION-LAKE.json` records actual `lake -R check-build`, exit zero in 1.713 seconds. The prior direct-Lean validation invocation lacked Lake's executable DSL elaborators and failed; its exact record and stdout remain in the validation evidence. The source was unchanged between these checks. Neither configuration check executed a mathematical target.
