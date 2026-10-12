# Independent R1 source and runtime delta review

12 October 2026, 12:26 UTC. Contributor: dot (OpenAI).

**PASS for the exact bounded retry**, conditional on the owner's immediate unchanged launch/resource gates. This is source/delta review, not Lean acceptance or a prediction that every elaboration error has been repaired. Accepted full 1,610 remains the baseline.

## Exact successor

- Research source: `68e3ddfac0e6d67638e80e62680ed26e7fc565b5580d815aaa2f32d799a5890c`.
- Graph: `7320e961a13fcd03beb955d460f932ba4181ebddfd16f2f3ee9c728938ff78d9`.
- Driver: `ead6a4e7bc28c1c0560c9cc631a308f8e8022d33c6445d2056be4213cda54349`.
- Preparation script: `0e9818ce46337cbf2aad743d83dc405157a850e851dc3e3c57944a475a1c52a0`.
- Prepared receipt: `1d343d476de520837253d91e8e3141bf2ff8cdbe613361380f6ee7f6563b7022`.

The original failed source `c1d840f31a0cd3179230d4cc9354ddb431f60f3809be238f57219cc60994d630`, run `20261012T121616.796005Z`, and stdout `acddbb3d580f3dff18095e713c4dca22c457e92bd25a8a4ae6239674fec753ed` are retained.

## Source findings

I read the complete cumulative source diff against the frozen admitted predecessor and the actual diagnostic groups. The changes address reserved syntax, missing namespace/scope, noncomputability, dependent instance and state normalization, explicit sum/binder inference, scalar/Poisson normalization, positive-support restriction, and finite PMF product evaluation. The source imports are unchanged. All 256 named declaration headers were compared textually; the sole header edit is adding `noncomputable` to `pairRatePolynomial`. This textual comparison does not establish equality of elaborated types.

Three context corrections require explicit qualification. `ForestFrontier.prefix` was a reserved-name parser failure and is replaced by `carried`, with the same intended existential proposition and updated uses. Opening ENNReal scope gives the completion reader its intended extended-nonnegative-real type; the earlier wrong-context declaration was not accepted. Parenthesizing the whole polynomial product restores the intended subtraction inside its binder; the predecessor's right-hand variable was unresolved. These are corrections to unelaborated source, not changes to an accepted theorem. `positiveSupportPMF` and other definitions containing proof arguments also have repaired proof bodies, so literal body identity is not claimed.

No mathematical premise is added, removed, or weakened. The original COMMON source, target-first arbitrary finite rival quantifiers, endpoint-one survival, proper-clade exclusion, n ≥ 4 master domain, N ≥ n counting use, zero-weight configuration handling, single supplied joint configuration distribution fixed across allocations, original-bank averaging, mixed-row-only query assumptions, and all-future full-response conclusion are preserved. This is a formal implementation of the attributed existing hand argument and prior method; it makes no novelty or executable acquisition claim.

## Runtime and preservation findings

I rehashed all 469 selected source bodies. The 468 accepted prerequisite entries remain literal; the graph changes only the candidate source hash. The driver is exactly its predecessor after reversing the graph/source hash substitutions, so its nine owned Mathlib contexts, one-source fresh allowlist, aggregate/audit allowance, and maximum three invocations are unchanged. The preparation delta is limited to matching source folder/hash, graph and driver pins. All eleven active script/template identities match the prepared receipt; the supervisor and verification core are unchanged. Python syntax checks passed without importing or invoking the builder.

The fresh source is 187,580 bytes, exactly 3,560 bytes larger; both preparation totals reflect that increment. The preserved predecessor graph/driver/receipt and first failed run remain available. The exact admitted 2 GiB monitored envelope, 8 GiB free-space floor, per-file and memory/process limits, namespace/cache verification and prerequisite-rebuild prohibition remain. This review does not substitute for the immediate resource/no-compiler gate or final complete trace, source, native/import, receipt and audit review.
