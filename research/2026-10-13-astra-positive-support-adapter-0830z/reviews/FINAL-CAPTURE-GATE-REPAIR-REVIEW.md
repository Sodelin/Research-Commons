# Final capture gate repair review

Reviewer: Astra Rust integration lane, 2026-10-13. Read-only source review and
authentication of existing bounded-test receipts. No test, Lean compilation,
complete-state authentication, final Lake target, or export was run by this
review. The actual complete-closure execution remains pending.

The initial review found that a successful command ending in a basename
`lake build adapter` could satisfy the export gate without identifying this
packet, executable or selected state. It also found that the exporter did not
recheck authenticated-reuse origins or bind the full owned receipt ledger;
saved interface source and invocation binding were copied without validation.
A follow-up identified the missing frozen-guard identity and resource-profile
checks. Those findings concerned evidence authentication, not changes to the
accepted theorem statements.

The reviewed repair addresses those findings:

- The expected invocation now fixes the packet cwd, ordered environment
  arguments, exact selected source/state paths and pinned native Lake binary.
  The guarded output must contain exactly one matching interface execution
  binding, including the actual interface receipt hash, Lake configuration,
  argument bindings, compiler identity and owned receipt-ledger hash.
- Interface compilation and final capture both call the existing
  `--authenticate-only` mode. Its zero fresh budget prevents missing modules
  from being compiled by this gate; the full existing source/object/log and
  reuse-origin checks must succeed. The ledger digest binds each indexed owned
  receipt, including its reuse origin. Capture preserves its reauthentication
  command and output separately.
- Saved interface source bytes must match the executed source hash, the saved
  invocation binding must match the result, the actual helper hash must match
  the captured configuration, and artifacts and actual axiom logs are checked.
  Required adapter and separate-interface axiom outputs must agree.
- The final guard receipt and current guard source must match the immutable
  previous-packet manifest pin. The complete declared resource profile must be
  exactly900s wall,600s CPU,5GiB virtual allowance,4GiB monitored physical stop,
  1GiB file cap,8GiB disk floor and1GiB RAM floor. Failed guards, weaker limits,
  unrelated commands and unrelated Lake package directories are rejected.

No further blocking code finding was identified in this narrow review. Partial
exports remain preserved in a fresh directory and are not completion manifests.
The final ledger distinguishes prior authenticated reuse from fresh source
compilation; it explicitly does not claim a fresh full1613 aggregate, physical
representative, universal native-code correctness or remote publication.

The v3 guard and both test-output hashes matched the receipt. Its stdout pins
match the reviewed source bytes below. It records seven passing bounded tests,
exit0, no resource stop, guarded elapsed0.502s and peak RSS21,553,152bytes. These
tests exercise refusal gates and changed ledger identity. They are not the
successful complete-state Lake/interface/export execution, nor a universal
correctness proof of the Python capture implementation.

`FINAL-GATE-REPAIR-PINS.json` at the review cutoff is a preserved v2 record and
still names the older capture/test hashes and v2 test receipt. It must not be
presented as the current v3 manifest; a successor record can pin the tested v3
sources without rewriting that historical record.

| File | Reviewed SHA256 |
| --- | --- |
| `audit_support_interface.py` | `02b2fa1972e14701119e2be515ed0b64336db3bd287857d7f88a788cf6fbf5d7` |
| `capture_final.py` | `29636a8c9e86467d6fddaf0cd01d787cda22b3034264ec60624827d6ab4fedd9` |
| `build_support.py` | `9d9797da3f01c5af31e16e8a622d1e595c2460d590f6306f1ee41118371a0f48` |
| `test_final_gates.py` | `7cc6fc19b4df8c0793c8da8622bddcc6dcc606520fa76941189f07cbe8efbc85` |
| `lakefile.lean` | `2b5c501173fc8fd38046b4289b5678dcb4e81c838a3d02f4f974795b5b906a90` |
| `audits/ProviderInterfaceAudit.lean` | `130006bf4b3f2d0084b75a49e53d93121170f6074a9bfef204079667738e78ef` |
| `serial_compile.py` | `d47f2d50afd4648374d7ca1630dce71f3aa09422fe740d356b2d0d9c8ce8ca28` |
| `evidence/final-gate-tests-v3/RECEIPT.json` | `301cd5e3d77a15f7e82e6ed9fe38a59f73aef2c91fb84ccb5bcf92970e3b3660` |
| Historical `evidence/FINAL-GATE-REPAIR-PINS.json` | `238acfd64ef76457f3f2417d713f2be89e360104f1f56af9ce408ec820e46617` |

The native Lake executable matched the selected pin
`60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3`.
