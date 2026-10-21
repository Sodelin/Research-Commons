# Online native object retention

The next bounded CI run retains the EXACT two executed ELF objects under
rust-bank-result/native/ in its existing evidence artifact. ci_bank.py checks
their SHA256 before/after every call, copies the completed objects, reads them
back and records bytes, hashes and ELF class/machine in NATIVE-OBJECTS.json.
It does not initialize a new runner, profile, compiler lease or key.

This closes the practical gap between an observed binary hash and an available
online object. Previous run39675913869 proved behavior/hash but did not retain
the executables. New object retention must have its own actual job/artifact
receipt; the previous archive must not be relabelled as containing them.

The target tested is Linux x86_64 on GitHub Ubuntu24.04 with official Rust1.90.0.
Other OS/architecture/libc support is not claimed. GitHub artifacts do not retain
executable permissions: restore the executable bit AFTER checking the exact
recorded hash when using an owned online Linux checkout. The component's
read-only sparse checkout, locked Cargo recipes and source manifests reproduce
both objects. Binary object retention is not a Lean object, full Rust refinement,
physical admission or canonical checker-profile approval.

The existing runtime checker() accepts only its old source-pinned receipt/
observation profiles. Keep the new bank/proposer outside CHECKERS. The proposed
role is auxiliary arithmetic acquisition whose output still traverses the
original independent checker/emitter/runtime. Any new runtime capability or
profile schema must be an explicit source-reviewed integration, retaining the
literal original request, complete outcome/authentication, resource limits,
UNKNOWN/refusal distinctions and physical/master scope.

Current source proposal: snapshot/readback in ci_bank.py. Runtime/bridge/server
and canonical whitelists remain byte-unchanged.
