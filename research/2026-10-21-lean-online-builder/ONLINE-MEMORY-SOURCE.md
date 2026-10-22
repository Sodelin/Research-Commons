# Proof source from RAM through the existing online client

The checked launcher now accepts caller-owned UTF-8 proof bytes directly.
It encrypts and reads back the exact input request before starting the original
Node client, sends those bytes through stdin, and encrypts the complete output
before reporting a result. It creates no plaintext proof-source or temporary
file. The original file-source runners remain available.

Use [check_online_memory.py](check_online_memory.py) with stdin containing
the selected document and these explicit arguments:

~~~text
python -B check_online_memory.py --source-sha256 EXPECTED_SHA256 --audit DECLARATION --record-codec EXISTING_ABSOLUTE_CODEC --codec-sha256 PINNED_CODEC_SHA256
~~~

Repeat --audit for each selected declaration. The caller must supply the
already verified installed record CLI and existing identity; this launcher
does not create a key or discover/export a recipient. A pipeline must come
from an already authorized source provider. This interface does not permit
a held native producer to run.

An in-process caller can use the same function:

~~~python
run_memory_case(packet_root, source_bytes, expected_sha256, audit_names,
                existing_codec_path, pinned_codec_sha256)
~~~

source_bytes must be immutable bytes, valid UTF-8, at most1MiB, and match the
expected lowercase SHA256. Audit names retain the original client grammar;
their total charged length is at most64KiB. The existing12MiB record and
900000-byte codec-envelope limits remain. An input that cannot be fully
recovered is refused before the proof child, with an encrypted tombstone.
Result exhaustion likewise retains a request-linked tombstone and cannot PASS.

The complete input request contains the exact byte encoding, original audit
order, source and submitted-document hashes, selected authored-source
inventory and process budget. The result links the encrypted request receipt,
retains exact child streams and requires unchanged before/ready/after source
inventories. It checks source bytes/hash, audit order, submitted-document
hash, actual normal exit and the original host/version decision.

The Node core and drain are unchanged. Its all-distinct-diagnostics union,
completion sentinel/final barrier, complete type/axiom audits and pinned
hosted context still decide the check. The new route uses the existing
readFileSync('/dev/stdin') behavior. It adds no proof renderer, native solver,
local Lean/Cargo/Lake process, external backend or automatic retry.

[The verification](ONLINE-MEMORY-SOURCE-VERIFICATION.json) records28 passing
mocked regressions: the existing14 plus14 input/recovery/binding controls.
Tests cover request encryption refusal, exact PIPE input, input and submitted
hash mismatches, source drift, timeout partial streams, result encryption
refusal and request-linked exhaustion tombstones. They exercise mocked
failures; no actual timeout/oversize claim is made.

Two actual checks exercise the changed route. The existing108147-byte
physical sparse-row context passed with0errors/5inherited warnings, all
three complete printed types and clean standard axiom audits. Its source
5b83d950 and submitted document4cd4ef8f are byte-identical to the earlier
file-based proof. The existing125-byte false proof was rejected with normal
exit2, one error and an unclean axiom audit. Both encrypted request sources
were independently unsealed and checked against the exact input bytes;
each result's link and full source inventories were checked.

These are launcher integration controls, not additional mathematical cases.
There remain35 bounded mathematical verifications and778 selected native
modules. Old typed population/epoch/word mathematics and finite executions
remain [reused](PRIOR-TYPED-EXECUTION-REUSE.md), rather than repeated as new
discoveries. The exact input-time authored manifest is retained separately.

This establishes caller-selected proof-byte/request/result binding. The
caller-supplied expected hash does not authenticate a native exporter or its
data origin. No new exporter table ran, no parser/source/action completeness
was established and no pinned native import/object was accepted. The actual
original-owner Linux writer/controller/transitive hooks remain UNBOUND.
Hosted submission is still submission to the existing external proof service;
this route does not conceal that input or encrypt all session stores.

The next existing source action compares the current778-module selection
with retained original complete import/audit/object evidence before selecting
any new build. Every original owner, acceptance criterion and action hold
remains.
