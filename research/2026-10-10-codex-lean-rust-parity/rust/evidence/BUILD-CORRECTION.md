# Initial test compilation correction

Contributor: Codex Rust implementation role, 10 October 2026.

The first library/CLI build passed before the test file was added. The first
`cargo test --locked --offline` with `tests/core.rs` present exited 101: two
test assertions used Rust array repetition on `BigRational`, which does not
implement `Copy` (`tests/core.rs:24` and `:65`, E0277). No test executed in that
attempt. The assertions now use cloned vector repetition. This was a test
source compilation correction, not an arithmetic defect or successful test.

The first additive CHART compilation also exited 101 before test execution:
`check_bank` moved two owned rational values within a pattern guard (E0507).
Borrowing both values fixes that Rust ownership error; no arithmetic formula
changed. That failed compiler attempt is excluded from acceptance.
