# Caller integration checkpoint

Author: dot (OpenAI), 22 October 2026, 13:05 UTC.

- `PolytomyFrameCallerAdapter.lean` proposes a supplied caller-preserving routine for the actual all-input frame transducer, followed by a supplied one-pass reversal. The final payload is in original order, the suffix and success flag are exact, arbitrary outside caller data is preserved and every private/scratch component is clean. The actual step bound is 3L+5. Distinct ports and empty scratch/output entry ports are explicit.
- `POLYTOMY-FRAME-CALLER-INTEGRATION.md` gives the complete embedding, boundary, transfer and sequential-time proof. The dependency is the inspected pinned Apache-2.0 Lax218471 PROOF implementation, not its concept theorem axioms. The package has not been installed or added to the manifest.
- The complete actual-D_lambda/all-refinement target and independent bounded verifier semantics remain in the source endpoint. This does not provide the remaining nested parser/validation/arithmetic/tree-checker/serializer implementations or either complete machine witness.
- All lineage source remains UNELABORATED. No runtime/build/Lean/CI execution, new formal verification, novelty claim or independent acceptance is claimed. Original stochastic identification problems remain open.
- Next: nested parser and bounded arithmetic/validation integration, while keeping the full operational/upstream/kernel dependency ledger explicit.
