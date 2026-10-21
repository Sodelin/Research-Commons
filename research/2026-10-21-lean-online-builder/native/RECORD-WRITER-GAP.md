# Native execution and first persistence

The proposed three-module pinned native target has not run. Its Lake entry
refuses before compiler launch while the new worker's record sink is unbound.
Hosted Lean checks use the existing RAM-to-encrypted-record capture path and
remain distinct from native Lake/object acceptance.

The existing frame codec can encrypt for an authenticated X25519 public
recipient without a private identity on Linux. That API does not allocate
owner-supplied domain/stream/operation/sequence/previous-frame bindings,
authenticate the recipient, bind a journal/transport or mediate every first
writer. No identity or recipient export, new key, invented context or plaintext
fallback has substituted for those integration requirements.

The source-pinned guard opens stdout/stderr before child launch. The bridge
can persist incoming request bytes before the guard; the runtime has request
and save JSON sinks, and drivers have nested result/native-loader records.
Encrypting outer stdout cannot mediate earlier writes. The recovered
G6GeneratedChartAudit also explicitly calls Lean IO.FS.writeFile on
AUDIT-OWNED.json. It was read as source, not executed. Its first writer must
be included before any new native aggregate run containing that target.

Earlier Rust hosted tests and exact binaries remain observed with the disclosed
plaintext-runtime-record limitation, without retroactive privacy acceptance.
Their owner disabled new workflows. Held/consumed old jobs are not replayed.

Hosted Mathlib56a005 uses Mathlib.Basic.Real.Basic, absent at pinned0df444.
Checked hosted bytes stay unchanged. Separately hashed pinned-context import
variants require new actual builds; the three original certificate sources
are unaffected.
