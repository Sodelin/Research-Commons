# One bounded Lean recurrence replay

Lean 4.33.1 and Python are preinstalled. No network, installation, write to Git, dispatch, or scheduling occurs. Keep the worker and runtime in the operator-controlled environment; this is **not** an arbitrary Lean sandbox. Lean code can run metaprograms, so publish/pin only reviewed own source. A job cannot supply commands; never derive the trusted contract hash from a request's own arbitrary sources.

The operator pins the contract hash outside the payload. The contract binds the full Git commit, source tree paths and module order, SHA-256 and Git blob IDs, exact audited declaration, installed Lean binary SHA-256 and reported Lean commit. The receipt reports fresh replay, exact declaration, axioms, timing, and worker hash. It is not an authenticated signature on its own. The independent contract hash provides immutable job identity; provenance of the runtime remains operator-controlled. No blanket mathematical closure follows from an exact declaration.

- `--repo TRUSTED_LOCAL_REPO`: verifies commit type and exact tree path to exact Git blob with Git replacement objects and lazy fetch disabled.
- `--blob-dir TRUSTED_OPERATOR_CACHE`: pass raw GitHub blob contents saved under their literal content-derived Git blob IDs. This verifies bytes by both Git blob ID and SHA-256. It **does not independently verify commit membership**: operator has to obtain the authoritative commit tree/path→blob binding by connector before approving the contract pin. The receipt distinguishes the two modes.
- Lean recompiles in a fresh directory with fixed commands, generated audit file, per-process time/resource limits, and rejected warnings or unapproved axioms. No custom native plugins are registered. Fresh worker error is fail-closed and yields exit code 2, not a success receipt.

```sh
python run_recurrence.py --blob-dir OPERATOR_CACHE --lean PINNED_LEAN \
  --contract contract.json --contract-sha256 INDEPENDENTLY_TRUSTED_CONTRACT_SHA 
```

Before publishing a receipt, the caller must separately verify contract scope, approval, and target destination. A previous receipt is not a fresh run.

## Pilot evidence

The worker accepts exactly `AlexanderZeroRun.arbitrarily_late_run_iff`. It hashes the pinned Lean printer's fully qualified `#check` output (including the terminal newline) and independently elaborates a fixed typed consumer before auditing the declaration's axioms. `EXACT-TYPE.txt` is the expected printer payload. Compile and audit use one Lean thread; all inputs are checked before source evaluation.

For the local proof packet, run `bash replay-local.sh` (replays own staged Git commit and its exact detached blob cache, then blob and contract tamper tests) and `bash test-wrong-type.sh` (the same theorem name with false statement identity is rejected). `contract.remote.json` is anchored to an operator-provided authoritative GitHub commit/path/blob map; it is not an instruction to fetch or certify a remote ref. To feed that remote contract from a connector, independently verify the GitHub tree mapping and put the raw two matching blobs under their expected 40-hex object names in a fresh operator-owned directory.
