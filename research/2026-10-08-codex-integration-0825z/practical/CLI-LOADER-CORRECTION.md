# Authenticated helper loader correction

Contributor: Codex practical role 1, independent integration-review response.
This corrects the reusable CLI's helper execution-identity boundary. Earlier
numerical/native comparison receipts remain unchanged and retain their scope.

The reviewer identified that `SourceFileLoader` could execute a timestamp-valid
stale `.pyc`, or reread different helper bytes after a source check. The earlier
CLI, SHA256 `2a799c36b8cf4dcf1d1389e843731e2c939fa4bc4d46129d429a5d0c8e09279a`,
and its then-current README/file manifest are preserved in
[cli-loader-before](cli-loader-before/). This was a loader identity gap,
separate from the observed four exact native/reference outputs.

Current [pipeline.py](pipeline.py), SHA256
`897fb28e37a34719314103827f30e3baa64cd6045b8c7dc16746a5fb27f5d1c6`,
reads each helper once into a bounded nonsymlink buffer, checks its fixed
expected SHA256, and compiles/executes that captured buffer through ModuleType.
It does not consult `.pyc` or reread the source for execution. The exact executed
helper identities are recorded in `EXECUTED-HELPERS.json` and the final result:

- Original runner: `c901ec815c558990d87ce5ebbbbbef414b27b99a609228e6acefd9b0a908a509`.
- Signed comparator: `0ee32b5d0a72fb1fbe426cde97dd018d009e4b8dee0e63e057d6e3d9cb93598c`.

The actual finite-record pipeline was rerun once into
[cli-finite-record-loader-v2/RESULT.json](cli-finite-record-loader-v2/RESULT.json).
Producer/checker exited zero in 1.619/1.570 seconds, recomputing the complete
23-stage/50-frame journal. All nine union widths remain 1 and the result is
UNKNOWN_OUTER_COVER. All four ordered native pair outputs match the byte-executed
Python reference exactly and return UNKNOWN/PULSE_DENOMINATOR. This changes no
finite-data, biological, source-feasibility or accuracy conclusion.

The unsupported-model path was rerun once into
[cli-model-mismatch-loader-v2/RESULT.json](cli-model-mismatch-loader-v2/RESULT.json):
MODEL_NOT_ADMITTED, no numerical or native solver called. A focused independent
cache control first establishes a genuinely timestamp-valid stale cache: the
old loader executes value 1, while the new verified-buffer loader executes the
source's value 2. A later source substitution is refused before execution or
module registration. [Actual control receipt](logs/AUTHENTICATED-LOADER-CONTROLS.json)
and [control source](test_authenticated_loader.py) are preserved.

No Cargo command, compiler build, original source mutation or data generation
occurred for this correction. The original numerical runtime still relies on
the separately checked clean/frozen runtime and no-cache environment; this
helper correction does not claim a general hostile-loader theorem. Independent
review and publication/readback are separate from these actual test results.
