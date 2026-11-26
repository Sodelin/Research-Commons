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

Actual ONLINE run39676750748 at41217af3de6af9d4a609aa9680ac9025e210a4c6 PASSED and retained BOTH objects in artifact12382691850 (669932 bytes), SHA25668963ed6ddcb092c8409296f876e286fecd4bc29e7a4831c6413ff200f9de1f0. The archive and all10guard stdout/stderr receipt pairs were authenticated in RAM. Both ELF objects were read inside the archive and checked for exact size/hash/class/machine; both identities reproduce the prior independent run exactly. All existing and new bank/CLI/runtime/MCP checks passed again. The observed archive modes are0644; the checksum identifies the bytes independently of restored executable permissions. See evidence/native-custody-39676750748/ and PROPOSED-NATIVE-PROFILE.json. Runtime/bridge/server and canonical whitelists remain byte-unchanged.

The pinned upload-artifact implementation documents permission loss in [its exact README](https://github.com/actions/upload-artifact/blob/ea165f8d65b6e75b540449e92b4886f43607fa02/README.md#permission-loss). The artifact expires2026-11-20T21:12:17Z under30-day retention; exact versioned source, lock and reproduction recipes remain. Binary retention is still separate from canonical adoption.
