# Official import-query capture review

Reviewed by the Rust integration lane on 2026-10-14 UTC. This is source/receipt authentication and a scoped implementation review, not a new mathematical review or a compiler execution by this reviewer.

The completed v2 query run performed 477 official `--src-deps` calls: the exact 469 selected owned sources, six Astra sources, and two additional official Mathlib source roots. The extended plan preserves all 3591 previous source records literally and adds two records. The prior import edges are authenticated reuse. These are source-resolution results; no theorem elaboration, object authentication, aggregate build or mathematical completion follows from their counts.

The preserved v1 failure exposed partial-namespace precedence: materialized Mathlib first caused nonexistent paths for unmaterialized Mathlib imports. The revised query source authenticates all nine selected owned Mathlib bodies against both their materialized copies and complete upstream sources before routing Mathlib imports upstream. Research namespaces and actual selected source query paths remain materialized. This establishes exact source-route equivalence, not compiled-object equivalence. The future owned-builder namespace policy still needs its separate implementation and validation.

## Exact evidence

| Artifact | SHA256 |
|---|---|
| Executed query source | `1bbcc570d913793490d8bf3688a975ff7e9bfd2dfcab78ee383d922fe6087965` |
| Actual query guard, `evidence/import-query-v2/RECEIPT.json` | `0992c7eadfe26a86e86a79676db443c54979c766dd7e66fc40f34cd0b5212088` |
| Extended source plan | `32bb59e44de8b3252c37deae1f12a7a14fc79a0407da97dd15f7d5b576991d2c` |
| Nine-body route equivalence | `4c25cc6c83db7bcb4593a4651b973beffce4b1faed46c23ce7b7aa23b0f88e71` |
| Reviewed/executed capture source | `dbce28be1df8b5b7dac80dc8400551d8ef7415eb0e15e93e07a3d9005ac518c4` |
| Capture guard, `evidence/capture-query-v3/RECEIPT.json` | `b804b05998bdd73164c62db08f1033f4439f674377607db2601ebe58e6a62a55` |
| Stronger capture `evidence/import-query-v3-authenticated/FILES.json` | `71699b6cbaee23d0d3cca14dd494c8e43e6f046824843a7a9ec21e7abd0a056a` |

The query guard records exit 0, no stop/error, 28.034 seconds and 91,246,592 peak child RSS bytes, with 6 GiB address-space and unchanged 4 GiB physical-stop controls. The separate capture guard records exit 0, no stop/error, 4.005 seconds and 38,748,160 peak child RSS bytes, within its 512 MiB address-space, 60-second wall and 30-second CPU profile. No compiler queries were repeated by this capture.

## Review findings and repairs

The initial narrower capture source `b56b9dde913d6d23baa6ca270ae64dfc0e915b620b9ea7addcf721cf37559f03` and its actual successful execution remain preserved. Its authentication omitted exact selected-query order/environment, full dependency-list coverage, exact nine-route identities, and new plan-row/import bindings. The reviewed successor checks these against the pinned selection/header helpers, expected query command/cwd/phase/environment, exact output-key sets, stdout-derived imports, source copies and dependency hashes.

A successor initially matched query order to topological plan order. The actual query order is Funext then Polynomial, while the new plan order is Polynomial then Funext. The final source matches each new plan row by unique exact source identity and authenticates its source hash and imports; it preserves both legitimate orders.

An initially reported newline concern was a reviewer error caused by nested tool-output escaping. Direct AST inspection showed codepoint 10 and the saved manifest parsed correctly. That finding is withdrawn; no newline repair was required.

The final independent readback rehashed all 2870 stronger-manifest payload references (13,117,436 bytes), both actual guard log pairs, and the source/guard/plan bindings. The stronger manifest references the literal prior capture payload rather than duplicating or rewriting it. No remaining concrete blocker was found within this scoped capture review. Publication and any subsequent compilation remain separate owner actions.
