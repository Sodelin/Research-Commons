# Admission must precede Lake itself

The mandatory entrypoint for each proposed native context is
start_new_context.sh,558B/SHA256
66a8c0b34d3eb0e7b0373007062160554745a8c3354a4a79019e293823b0d4d3.
It unconditionally refuses before any Lake/config loader, compiler or native
child invocation. There is no environment/argument override: a flag is not an
authenticated recipient, controller sequence or first-writer binding.
The source was installed into all proposed native layouts; it was NOT executed.

The earlier in-Lake target error is only a secondary guard. Earlier prose
calling that target a first-writer gate was incorrect. No Lake invocation
occurred, so this corrects a source proposal, not a reported new execution or
retroactive policy violation.

The exact official Lean v4.33.1 sources were independently read:

- [Lake/Load/Lean/Elab.lean](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Load/Lean/Elab.lean),
  SHA2565b3d30d5a9001514e7ff3d8c95a71bd0b29a79777e12c441e79563af0acb1674.
  ConfigTrace JSON is written/flushed/truncated before elabConfigFile, followed
  by Lean.writeModule. This is in-process config elaboration; a separate
  compiler child is not assumed.
- [Lake/Load/Lean.lean](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/Load/Lean.lean),
  SHA256835d173b6b9855c99833c7063c3909f58d2e746632d3f723f10aff5e1fe0a015.
  loadLeanConfig calls importConfigFile before LakefileConfig.loadFromEnv.

A user manually bypassing the mandatory launcher is outside this proposed
entrypoint. This is a fail-closed source launch path, not an OS-wide claim that
all possible invocations of Lake are intercepted. Direct lake verify is not
an admitted command while the writer remains UNBOUND.

Before any future execution, the real owner-bound writer/controller must
mediate or keep in RAM ALL first writes, including config trace/loader/log
records and the inherited builder/guard/runtime/audit sinks. Source/object
classification is a separate issue from those records. No new key, exported
recipient, invented callback or blanket assertion supplies the binding.
Replacing this unconditional refusal requires separately reviewed source and
actual original-owner binding. Old held/consumed jobs remain untouched.

The current refusal is SILENT: no stdout/stderr printf remains. Required
refusal/recovery belongs to the existing encrypted owner/controller. A default
CI shell may itself persist an exit-status record, so even this quiet script
has not been invoked under an unbound controller. The earlier static-printf
source was never executed and remains in immutable source history.
