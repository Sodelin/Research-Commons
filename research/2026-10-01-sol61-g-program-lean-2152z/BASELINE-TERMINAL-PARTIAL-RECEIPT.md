# Terminal fresh baseline verification receipt

Dedicated Sol6.1 Lean lane, 2026-10-01. Original source attribution retained.

Pinned source: Sodelin/Work-on-Samuel-Alexander-Research- commit
e2502c82ab9a77c00543932f775a71e5374221f7. All 117 top-level formal-full files
match original Git blob and publication-manifest SHA-256 hashes. Three explicit
original exclusions remain excluded: GraphQuartetPortCounts, SourceProbe,
ThetaProbe.

Matching official Lean 4.33.1 and pinned mathlib
0df444a360eaa60ab8c11dca51a86af692955474 were installed/verified on the cloud.
The official archive digest was checked before compiler execution. The full
8690-file official mathlib cache completed successfully.

## Actual terminal result

96 of 114 included original modules compiled successfully from exact source.
Successful source hashes, exit codes, elapsed times, log hashes and explicit
axiom lines appear in `receipts/baseline-independent-completion.json`. Full
successful compiler logs are concatenated in
`receipts/baseline-successful-compiler-logs.log`.

Five certificates are resource-blocked:

- ThetaCertificate6: initial 300-second timeout; subsequent external kill;
  final bounded single-thread 6144MB attempt aborted with an explicit Lean
  memory_exception after 436.878 seconds
- ThetaSupportCertificate3, 4, 5, 6: each aborted with an explicit
  memory_exception under a lightweight single-thread 2048MB independent scan

No further certificate retry or budget escalation is running. Source bytes and
proof methods were not altered. These are resource failures, not mathematical
counterexamples. No Lean proof error was reported in those failures.

Thirteen dependent modules remain unchecked: ThetaCertificate, ZeroTheta,
AnchorReduction, ThetaSupportCertificate, BoundedThetaTheorem,
AnchorUnboundedTheorem, AnchorUnboundedSupport, ThetaSourceUnbounded,
ThetaTaxonRestriction, CanonicalTheta, VerifiedCheckpoint, ThetaDeletedHybrid,
ThetaFiniteEndpoint.

## What the receipt means

Actual graph/port/switching/RawNanuq and numerous algebraic/canonical components
have fresh successful runs. CanonicalTheta and the original consolidated
VerifiedCheckpoint do not have a successful complete fresh run in this lane.
Historical local compilation remains separate evidence.

The final raw all-level NANUQ source theorem was already absent from the pinned
source. Conditional AnchorComposition/CircularComposition statements retain
their explicit source graph/port hypotheses; compiling them does not prove the
missing biological source bridge. Neither whole NANUQ nor the entire G1-G7/CG
programme is claimed machine verified.

The independent scan preserved prior successful objects and never retried the
large blocked certificate. New assumption tests used their own small bounded
checks, so the original legacy build is now stopped and other research lanes
can continue.
