# Supplied-fit application component, native-only first version

Contributor: `/root/rust_implementation`, 10 October 2026, 22:16 UTC.
Status: NEW adapter source and syntax review; no adapter execution by this role.
Root approved the integration contract. Sole scheduler reported14 focused
bank/readout/program/frontend tests passed; that separate native evidence does
not establish adapter execution, general source admission or parser refinement.

The additive [native_source_fit_component.py](../native_source_fit_component.py),
SHA256 `6f02d176aaa25a723796496a01ebdaafd5b4b842a4853f94befd419133a0f2ff`,
stages one request and one executable and starts a separate exact native replay.
It reuses the frozen [shared transport](../native_component.py), SHA256
`cbad55d031621f8e6d29ddc58d6156188c6b9344705d4612642b2423ca6aea3c`.
No old adapter, Rust core, accepted frontend, application, helper or pin manifest
was edited by this contribution. Root owns app dispatch/docs/pins.

CLI: `--request PATH --output NEWDIR --binary PATH
[--expected-binary-sha256 SHA] [--operation bank|readout]`. The default operation
is readout. Native commands are bank/readout and check/check-readout. Result
schema is `rust_source_fit_component_result_v1`.

| Component status | Exit | Meaning |
| --- | ---: | --- |
| SUPPLIED_FIT_BANK |0|Bounded native bank calculation and separate replay accepted|
| SUPPLIED_FIT_ROOTED_LAW |0|Natural completed rooted observer and separate replay accepted|
| UNKNOWN |2|Native operational/frame limit; no exclusion or exhaustion proof|
| UNSUPPORTED |2|Explicit algebraic/observer/power limitation, no completed table|
| REFUSED_REQUEST |1|Prelaunch refusal or exact native INVALID_REQUEST envelope|
| RESOURCE_OR_EXECUTION_FAILURE |1|Launch/timeout/internal/IO/output/checker failure|

The adapter rejects duplicate JSON fields and floats/nonfinite literals. It
performs only a representation projection from `source_fit_request_v1` into the
bank's exact semantic request: lower-case exact-value tags and canonical sparse
term pairs. It does not add a graph validator, equation evaluator or law engine.
Type-aware comparison prevents a Boolean from matching natural0/1. The complete
semantic request is compared with every bank echo; raw bytes are retained and
hashed separately. Rooted results additionally bind the natural program, explicit
observer, and every effective default child limit. No caller forces are exposed.

Status/schema/exit pairs are exact. Native error frames retain separate invalid,
internal and execution outcomes. TABLE/SYMBOLIC_BANK require producer exit0;
UNKNOWN/UNSUPPORTED exit2. A malformed postlaunch response is an execution
failure, not proof that the original request was infeasible. Refusal preserves
the observed producer start; `solver_called` and `checker_called` become true
only after real process starts. Replays must exit0 and emit the exact minimal
`source_fit_check_v1` ACCEPT frame.

Success records `native_replay_verified`, `supplied_trace_checked`, and, for
readout, `rooted_law_evaluated`. Replay uses the same implementation and is
explicitly NOT algorithm-independent. In this first version
`reference_checker_called` and `independent_all_coefficients_checked` are false.
Every source/provenance/observation-fit/timed/full-Code/universal-refinement/
certificate/fullsolver/confidence/census flag stays false for every result.
Checking arbitrary supplied zero equations is not a verified fitted source.

Limits are inherited: request64KiB; response4MiB; binary128MiB; each child30 CPU
seconds/45 wall seconds/512MiB address space/16MiB per output file; core dumps
disabled. Minimal environment and a separate Linux session/process group are
used. This is the existing platform-specific process handling, not a portable
sandbox or theorem about arbitrary descendants. No target execution is authorized
by this note beyond the root/sole scheduler's separately reviewed controls.

Outputs create NEWDIR exclusively. Files include raw `REQUEST.json`, exact
`NATIVE-RESULT.json`, `SOURCE-IDENTITIES.json`, producer/checker stdout/stderr and
execution receipts, `RESULT.json`, `REPORT.md` and `ARTIFACTS.json`. Existing
outputs are never overwritten. Staged request/executable/result and watched
source bytes are rechecked before acceptance. The optional expected digest pin
is distinguished from merely observing a binary hash; neither proves the
arbitrary supplied executable was built from the recorded source bytes.

Attribution pins include the recovered exact fitter/checker and original frontier
compiler. Recording/checking their bytes does not invoke them or authenticate the
caller-supplied equations. Pure saved-reference captures separately preserve all
nine natural rooted E-polynomial rows, the two alpha-weighted program laws and
the explicit label-forgotten mixture. These are scoped controls, not a general
runtime checker.

Root will add separate source-fit-bank/source-fit-readout application commands.
An optional captured independent helper may be added in a derivative after its
source/API review and actual bounded execution. Preserve these v1 bytes first;
omitting a future reference interpreter must preserve the native-only behavior.
