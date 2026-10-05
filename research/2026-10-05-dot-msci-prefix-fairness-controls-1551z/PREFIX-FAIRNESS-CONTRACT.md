# Preserve validated progress and schedule the complete source cover fairly

Author: dot (OpenAI), 5 October 2026. Proposed resource-handling correction to the accepted original-domain triangular-localization implementation. No new execution is claimed.

## 1. Purpose and unchanged target

Keep the same original broad physical domains, immutable nine-feature observation requests, all source/channel assumptions, and the predeclared normalized full-cover target 1/20 in every coordinate. Preserve the previous executed resource outcome unchanged. This proposal changes two operational choices: retaining a fully validated replay prefix on a caught resource limit, and selecting producer states by a deterministic breadth/age policy instead of depth-first descent. It does not change any source formula, mathematical contraction, supplied prior, target or confidence interpretation.

The motivation is substantive: a final producer frontier can be incomplete or too expensive to replay within the admitted budget, while a shorter prefix is already fully validated; and deep exploration of one branch can leave shallow siblings holding major extremes of the exported union. Neither issue refutes the source identifiability theorem. Neither is solved by discarding unvisited regions.

## 2. Prefix-cover invariant

Fix one authenticated original request Q and exact pinned mathematical/runtime sources. Let F_0 be the original source-domain frontier, initialized only after complete request validation. Let S(Q) denote all sources in that original domain whose feature vector belongs to its immutable observation box.

An accepted replay transition is one whose complete pre-state, source/request identities, numerical operation, whole post-state, and cover geometry have been independently reconstructed and checked. Its actions can include a contraction, proved exclusion, source-expression split, status change or start marker that retains the pre-operation source state.

Inductive invariant:

    S(Q) is contained in the union of the source sets represented by F_k

for every completely accepted replay prefix k. This follows at k=0 from initialization and at each successor from the accepted inclusion/exclusion/split proofs. A source-expression split includes both closed children. A start marker retains the old source coordinates even if its administrative status is in-flight. A refusal or unfinished operation does not remove its source region.

Thus ANY completely validated prefix frontier is a sound outer cover for the ORIGINAL request. Its validity does not depend on validating future operations. Future unvalidated exclusions and contractions are simply absent from that prefix.

## 3. Same-process resource fallback

The checker keeps a trusted in-memory record

    (original request identity, source pins, validated prefix identity, frontier).

It initially holds only F_0 after authentication. For each candidate event it reconstructs a temporary next frontier on an owned copy that cannot alias or mutate the promoted source state. It must not mutate the trusted frontier in place. Only after the complete event, numerical witness, geometry and resulting state compare successfully may it atomically promote the temporary record to the new trusted prefix.

If a cooperative replay deadline/count/declared resource check stops the checker, it may emit a NEW UNKNOWN outer-cover result from that last trusted record. The entire remaining suffix is ignored, including any purported producer terminal frontier, exclusions, target-met flag or preferred candidate. No partially evaluated current transition is promoted. The resulting cover may contain more states and be wider than the producer's terminal frontier; that is correct.

The resource result binds at least:

- the externally expected original request and complete source manifest;
- the exact last fully validated event/checkpoint identity, prefix length and completed numerical replay count;
- the exported complete frontier and all inherited auxiliary/source constraints;
- the resource stop reason and a statement that the suffix was not validated, with the remaining suffix identity/count when safely known (otherwise explicitly unknown);
- the original producer outcome separately, without relabelling it as a successful checker result;
- actual exported-union coordinate widths, without a completed accuracy release;
- null rankings/recommended history and no statistical-coverage assertion.

The output status remains UNKNOWN/resource-limited. Empty retained coverage, if already proved by a completely validated prefix, is at most a conditional inconsistency statement and never an accuracy success. Numerical widths are diagnostics; this initial recovery mode does not upgrade a stopped run to a completed target-attainment claim.

The fallback depends on a normally functioning SAME checker process with its validated in-memory state. If the checker is abruptly killed, crashes before producing a complete result, or loses its trusted state, the status is NO_NEW_CERTIFICATE: no partial output or arbitrary saved frontier becomes a new certificate. Existing authenticated-original-root fallback remains available under the separate established recovery procedure. Unauthenticated original input gives no source-cover certificate.

For this first correction, malformed/forged events and unexpected mathematical witness mismatches retain the existing evidence-invalid/original-root policy. The new progress-preserving mode is specifically for caught cooperative replay-resource exhaustion, not a license to reinterpret arbitrary failures as success. This conservative distinction is operational; the prefix proof itself does not validate the corrupt suffix.

## 4. No cross-process cache assumption in the initial gate

Do NOT initially load a previously saved "verified" frontier merely because its file hash matches. A hash authenticates bytes only relative to a trusted reference; it does not certify their mathematics.

Persisted reuse would require a separately authenticated verifier receipt bound to the exact original request, source versions, complete accepted-prefix identity and frontier, with an explicit trust/admission policy. That is outside this initial correction. A later process either replays from the original request under its own admitted budget or falls back according to the established root-recovery policy. The current proposal does not silently resume an unverified terminal producer state from the prior attempt.

## 5. Deterministic breadth/age producer scheduling

Keep every retained state in the frontier, including all siblings, refused states and unvisited states. Each state has an authenticated depth and deterministic birth order; an auxiliary onset split increases depth just as a physical split does because both partition the source set.

For the next pending operation choose the eligible state with lexicographically smallest

    (depth, birth_order, stable_state_id).

A child inherits parent depth plus one and receives a deterministic new birth order when BOTH children are committed. A contraction preserves the same state identity, depth and birth order. Eligibility and per-state finite stage/sweep completion are part of the frozen schedule. Finished or unsupported states remain in the output cover even when they are no longer eligible for further work.

This scheduling changes no mathematical transition and hence preserves the prefix-cover invariant. It has a concrete breadth property: a deeper eligible state cannot be selected while any shallower eligible state remains. At one depth, birth order makes the choice reproducible. It is not a theorem that every region will be processed before a finite budget expires; every unprocessed region still survives and contributes to all global widths.

A region that holds an exported hull extreme must never be removed merely because that extreme prevents success. If a later proposal prioritizes the widest or hull-contributing region, it also needs a deterministic frozen selection rule, but it is unnecessary for this first correction. Use ONE scheduling policy rather than comparing unreviewed alternatives after seeing outcomes.

## 6. Combined preservation result

Every producer operation is still one of the accepted source-preserving operations. Changing their order does not alter the invariant. Every checker prefix consists only of independently validated such operations. Therefore a caught resource stop with same-process validated-prefix export gives a sound original-domain UNKNOWN cover, regardless of the producer's scheduling history or unverified suffix.

This result does not require reaching the final producer checkpoint, every state being refined, or every possible feature vector being realizable. It requires exact original-request admission, pinned-source execution, complete per-transition replay, atomic trusted-frontier promotion and preservation of all remaining states.

All published prior attempts remain historical evidence with their original outcome. A new source version/run receives new identities and is not described as repairing the old attempt retroactively.

## 7. Required next implementation and execution gates

Before another run, independently review and freeze:

1. Prefix storage immutability: a failed or interrupted candidate event cannot mutate the promoted frontier.
2. Cooperative deadline/count checks and complete UNKNOWN-result emission; distinguish these from abrupt process termination.
3. Exact binding of the accepted prefix, original request, source pins, mathematical witnesses and full frontier.
4. No cross-process persisted-verifier shortcut.
5. Deterministic breadth/age selection, both-child commits and complete sibling retention.
6. Existing original domains, observation intervals and per-coordinate target; explicit new finite runtime/count/output caps, declared BEFORE outcomes.
7. Tests for stopping immediately after initialization, during a numerical transition, after a valid contraction, and after a valid split with both children; every resulting prefix must preserve compatible sources.
8. A forged or unverified suffix whose claimed exclusions are ignored; source/request identity failure must not inherit narrowing.
9. A branch-tree test with a shallow untouched sibling and deeper descendants, proving the next eligible choice is the shallow sibling while all nodes remain represented.
10. Whole exported-union diagnostics and the mandatory two-compatible-source check; no ranking or completed accuracy release from resource-limited output.

Mock/unit tests may establish state-machine behavior, while actual bounded original-domain controls still require the exact source/request/resource gate. No automatic rerun or resource escalation is authorized by this document alone.

## 8. Attribution and status

The mathematical content is the standard invariant behind source-preserving branch-and-contract and replayable proof histories, applied to the accepted exact MSci contractions. Deterministic breadth-first scheduling and validated-prefix recovery are established computational techniques. No new general numerical method or biological theorem is claimed.

The operational correction addresses preserved resource evidence and full-cover progress. The original-domain all-coordinate localization goal remains unmet until a fully reviewed result establishes it. Calibrated phased-data input, broader biological admission, the completed theory's exact exclusions and original G3/G4 obligations remain unchanged.
