# Frozen bounded baseline controls for independent execution review

No filter controls have yet run. Nineteen local unit/mock preparation tests pass (unit-tests.log). The only real point calls in those tests reproduce published point fixtures for a false-witness rejection check. Own sleeping children test process-group cleanup and recovery; no stress test or biological engine runs.

Use SOURCE-PINS.json (470c005e7998dc5433b4672b678eddc1b211b405cf1ef7b8a1d8032721cfac2b) and DECLARED-CONTROLS.json (82db9ab367e3e07634bae7a6fc6c61d212acd5ba63f0d33897de2b38532f281d) as frozen external identities. Each request is complete, exact, and independently hash-bound. Six fresh attempts only, in the declared order: distinct-rate containing box, equal-rate containing box, separated tiny box, zero-evaluation box, unsupported-midpoint-encoding box, and broad box. No retries or additional refinement after an inconclusive result without review.

The two containing boxes vary all nine coordinates and allow at most eight evaluations/eight splits. They check preservation of the known generating parameter, not localization or coverage performance. The separated, unsupported and broad boxes allow one evaluation and zero splits. The zero-budget box allows none. All request wall and recovery limits are 10 seconds, precision 64 bits, recovery witness count 32. Hard API ceilings remain 32 evaluations/splits/depth, 30 seconds per inner stage, 16..128 bits; they are not consumed by this plan.

Each producer and separate mathematical checker runs in an isolated process group with 512 MiB address-space cap and 40-second outer wall limit. Reuse reviewed watchdog c89201b45fe65915e3130659fd4dc3522bedfcbab6970735c5b06793a2ec1d8e: recursive 64 MiB logical-byte polling threshold with 1 MiB receipt reserve, 0.05-second polls, group termination/reaping. This is not a strict no-overshoot storage quota. Preserve both stdout/stderr files, per-stage terminals, checkpoints, original request, source-before receipt and final inventory. Source and copied-input hashes must remain stable. A producer exit zero never itself releases a cover certificate. Interrupted attempts remain failed; any separately validated recovery is a new UNKNOWN result.

Invocation template, replacing only the predeclared request/name/hash:

    python bounded_runner.py --request declared-requests/NAME.json --request-sha256 EXPECTED --attempt controls/NAME --source-manifest SOURCE-PINS.json --source-manifest-sha256 470c005e7998dc5433b4672b678eddc1b211b405cf1ef7b8a1d8032721cfac2b

Create the empty controls parent once; attempts themselves must not exist. Do not change request budgets or source pins between controls. Any unexpected failure is preserved and referred for review.

## Recovery and implementation detail

The contract's atomic checkpoint publication is implemented by flushed temporary file plus atomic no-replace hard-link publication and removal of the temporary name. This preserves exclusive immutable publication more strongly than overwriting rename; prior checkpoints remain untouched. The directory is private to the fresh attempt. The independent checker reconstructs geometry from the authenticated original request and re-evaluates EVERY inherited exclusion using the pinned forward code. It does not trust an interval because its hash matches. If validation fails or exceeds its budget, it returns the original authenticated root with no exclusions. Invalid original identity gives EVIDENCE_INVALID/no cover.

Checkpoint recovery currently validates the latest checkpoint only; if it fails it uses the original root instead of searching older checkpoints. This is deliberately conservative and within the accepted contract. Core request/JSON validation is shared, but geometry and numerical exclusion calculations are repeated in the checker. Source hashes are evidence of identity, not substitutes for independent review.

## Broad-box performance limitation

For h,u,v in [1/16,1/8], five rates in [1,5], and g in [1/5,4/5], the exact radius is 209/40 > 1. Thus every initial enclosure is [0,1] after clipping. The one-evaluation broad control must retain the root as UNKNOWN; it cannot localize parameters. Tiny-box exclusions demonstrate soundness only, not useful general-domain inversion. No expensive subdivision or new natural-interval contractor is authorized by these controls. The emerging alternative nine-feature inverse remains a separate unaccepted mathematical candidate.

## Result checks

For every successful checker output, preserve all nine coordinates, null rankings/recommendation, false statistical-coverage verification and false parameter-accuracy release. Validate the known generating point belongs to the retained union for both containing controls and zero budget. Do not impose a generating-point check on the broad box, whose g interval includes the generating value but rates/times may meet boundaries; its required check is exact root retention and radius 209/40. The separated control may yield EMPTY only with a independently recomputed strict-disjoint witness. Unsupported calls retain their full cell. Report cell mesh and union diameter separately. Nothing here admits DNA or calibrates finite-sample confidence.
