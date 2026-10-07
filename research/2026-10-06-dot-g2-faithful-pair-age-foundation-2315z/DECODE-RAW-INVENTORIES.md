# Decode the exact original raw inventories

These are newly authored, unexecuted portable instructions, not captured original commands or another Lean/DAG verification run. Start at this compact packet's root. The commands create a fresh directory and abort if it already exists, so earlier evidence is not overwritten. A standard gzip decoder and sha256sum are sufficient to recover and authenticate the exact original JSON-lines bytes.

```sh
set -eu
mkdir decoded-raw-inventories
gzip -dc 'phase-17/ordinary/attempt-005/stdout.jsonl.gz' > 'decoded-raw-inventories/attempt-005.jsonl'
gzip -dc 'phase-17/ordinary/attempt-006/stdout.jsonl.gz' > 'decoded-raw-inventories/attempt-006.jsonl'
gzip -dc 'phase-17/ordinary/attempt-009/stdout.jsonl.gz' > 'decoded-raw-inventories/attempt-009.jsonl'
gzip -dc 'phase-17/ordinary/attempt-010/stdout.jsonl.gz' > 'decoded-raw-inventories/attempt-010.jsonl'
sha256sum -c <<'EXPECTED_RAW_HASHES'
63775b3c47f468ba5938d55537d70e0516b6e690911c4b9304e4f4281b7fc20f  decoded-raw-inventories/attempt-005.jsonl
2e9815cc92957e59426bcfd136630e7be71787d3847eb311f7a1c2444fdaaf69  decoded-raw-inventories/attempt-006.jsonl
9219266ad53a62aa1984f62afca5028c4d1224593297cdb0673d08958269ed4d  decoded-raw-inventories/attempt-009.jsonl
52ba6d7cbb39ff2a7c59e8d490335ee88c24e26607612dc6f88162c8d5049099  decoded-raw-inventories/attempt-010.jsonl
EXPECTED_RAW_HASHES
```

COMPRESSION.json records compressed hashes/byte counts, decoded original hashes/byte counts, gzip level9, absent stored filename and mtime0. All four inventories retain their entire original content after decoding, including the two inventories from the earlier failed comparison. The current compact packet changes neither the mathematical sources nor any verification outcome. Successful decompression is not a new proof-body audit, and the omitted verification/dependency tools remain omitted.
