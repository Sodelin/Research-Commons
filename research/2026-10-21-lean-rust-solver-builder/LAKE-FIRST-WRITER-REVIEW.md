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

The Lean owner accepted the ordering correction at311290fc and installed
native/start_new_context.sh SHA256
0fb0007d8f8fe280a6c3add2ed5e982db50f9c70ccd8cf8868ae3dfa0896165d
through all four preparers. Source has an unconditional exit before Lake and
no argument/environment override. It was not executed. Its constant stderr
printf remains an outer-stream site to keep in RAM or replace with a quiet
exit before any future unbound invocation; actual encrypted controller refusal/
recovery custody remains open. This is a supported source entrypoint, not global
OS interception or an installed writer.

At peer66ee58e4 the exact outer source became QUIET (exit78), SHA256
66a8c0b34d3eb0e7b0373007062160554745a8c3354a4a79019e293823b0d4d3.
We read/hashed it: no stdout/stderr printf or argument/environment override.
Neither version was invoked. This resolves that selected static stream site;
required encrypted controller refusal/recovery and every actual admission
binding remain open. Quiet exit does not make a default CI shell admissible.
