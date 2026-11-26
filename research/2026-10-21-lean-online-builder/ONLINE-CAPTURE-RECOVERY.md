# Public runner capture and encrypted recovery

Both public Python runners now use [online_capture.py](online_capture.py).
The shared helper carries the deployed capture/recovery behavior into the
portable packet. The Node proof clients and their protocol/axiom checks are
unchanged. Component checks use the existing report-drain wrapper.

The former public runners could lose partial pipes on a parent timeout and
could accept a status word despite an abnormal child exit. The component
runner also lacked the deployed drain entry. Those older source companions
are retained in immutable Git history; their source-only status is not
retroactively promoted to execution evidence.

The helper verifies the supplied existing codec hash, every manifest-listed
source and all required entry/core/runner/helper/source bodies before capture.
It rechecks the complete inventory afterward. Acceptance requires the exact
source hash/length, ordered audit names, complete audit rows, unchanged hosted
versions and the corresponding normal exit: zero for PASS, two for REJECTED.
The original Node client continues to own diagnostic, sentinel and standard
axiom acceptance. A negative-control runner exits zero only when the expected
normal rejection was observed and encrypted recovery was verified.

Original stdout/stderr bytes, including invalid UTF-8 and timeout partial
pipes, stay in RAM and are recorded as base64 inside the encrypted envelope.
The helper uses the existing codec's `seal-stdin` with OS pipes, then checks
its encrypted-readback state, ciphertext length and SHA256. It initializes
no identity and exports no key. A failed or uncertain codec call has no retry
or plaintext fallback.

The existing lossless `zlib-json-v1` envelope is reused above900,000 codec
input bytes, with a12MiB original-record bound. An oversized capture produces
an encrypted UNKNOWN/tombstone containing stream lengths/digests; full streams
remain memory-only and acceptance is refused. This is bounded recovery, not
a claim that every possible output can be retained in full.

[ONLINE-RUNNER-INTEGRATION.json](ONLINE-RUNNER-INTEGRATION.json) records twelve
offline regressions and three actual hosted launcher checks:

| Public runner | Existing case | Actual disposition |
| --- | --- | --- |
| `check_online_component.py` | `g7-power-domain`, six audits | PASS, normal child exit0 |
| `check_online_component.py` | `reject-false` | REJECTED, normal child exit2 |
| `check_online.py` | `probe` | PASS, normal child exit0 |

All three original captures were encrypted before persistence and independently
read back. Their exact audit submissions were reconstructed. Failure/timeout,
identity-change, packing/resource and record-refusal regressions use mocked
children/codec calls; no actual hosted timeout or oversized result is claimed.
These are launcher integration checks of existing cases. The mathematical
follow-on count stays29 and the uncompiled source context stays776 modules.
The captured inventory hash identifies the packet before the later evidence
and documentation updates; exact tested helper/runner/client hashes are retained.

Run from this packet with Node24, Python3 and the already trusted record CLI:

```sh
python3 -B check_online_component.py --case g7-power-domain \
  --record-codec /absolute/existing/featurectl --codec-sha256 VERIFIED_SHA256
```

Offline regressions use only the Python standard library and mocks:

```sh
python3 -B -m unittest -v test_online_capture
```

The supported hosted service remains Lean4.35/mathlib56a005. This helper is
not native compiler admission or authenticated Linux process-tree capture.
Pinned4.33.1 imports/objects and actual original-owner controller/recipient/
sequence/journal/transport/transitive first-writer hooks remain UNBOUND.
Native/Cargo/Lake/CI execution and old held/consumed jobs remain held.
