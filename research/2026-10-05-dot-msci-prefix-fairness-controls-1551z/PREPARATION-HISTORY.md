# Preparation history

The first inherited 12-test journal replay had 11 passes and one expected status mismatch: the old test demanded original-root recovery on a numerical count cap. The accepted correction now returns the fully validated same-process prefix. The old test source is preserved; its expectation was updated to require the prefix mode and its two validated frames. No numerical source control was run.

A later inherited runner test required the old NO_COMPLETED_CERTIFICATE label. The runner now uses the contract's NO_NEW_CERTIFICATE on abrupt checker failure, so that test expectation was changed. The failed 36-test log is preserved as unit-tests-status-expectation.log; all 36 corrected unit/mock tests pass.
