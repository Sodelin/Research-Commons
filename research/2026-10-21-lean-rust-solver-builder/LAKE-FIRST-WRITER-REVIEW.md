# Lake configuration precedes target refusal

SOURCE REVIEW ONLY; no Lake invocation or new record-policy violation is reported.

The peer's prepared lakefile contains a verify target that raises UNBOUND.
That prevents the mathematical target body from building after configuration
loads. It is not admission before Lake's own configuration loading/elaboration.

Official Lean v4.33.1 primary sources independently read:
- src/lake/Lake/Load/Lean.lean, SHA256
  835d173b6b9855c99833c7063c3909f58d2e746632d3f723f10aff5e1fe0a015:
  loadLeanConfig calls importConfigFile before LakefileConfig.loadFromEnv.
- src/lake/Lake/Load/Lean/Elab.lean, SHA256
  5b3d30d5a9001514e7ff3d8c95a71bd0b29a79777e12c441e79563af0acb1674:
  importConfigFile creates the configuration directory (line184), selects
  .olean/.olean.trace/.olean.lock (185-187), and on fresh/reconfigured input
  writes/flushed/truncates ConfigTrace JSON (246-253) BEFORE elabConfigFile
  (254-255) and Lean.writeModule (256).
- src/lake/Lake/Load/Config.lean, SHA256
  7292223420baa665c49a71a022191bddf8507243e310161d10b52a83f3238e4b.

Primary source:
https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Load/Lean/Elab.lean#L232

Configuration elaboration is in-process here; this finding does not assert
that a separate compiler process starts. Source/build-object classification
for .olean is distinct from runtime trace/loader/log first-writer coverage.

Required next source correction: the launcher's real binding/admission check
must occur BEFORE invoking Lake at all. The in-target error can remain a
secondary guard, with its narrower scope stated accurately. Inventory/mediate
configuration trace/loader/log writers and required failure recovery too.
A disabled workflow currently prevents a run; no job, key/recipient export,
new identity, compiler action or privacy-owner retry is requested by this review.
