# Exact copy/literal storage format, version 1

This is a storage-only prototype for two already saved, hash-pinned Lean audit files. It does not produce a theorem audit or normalize audit metadata. The format name is `RC-AUDIT-COPY-LITERAL-V1`.

The uncompressed patch begins with these fields, without padding:

| Field | Bytes | Encoding |
|---|---:|---|
| Magic | 25 | ASCII `RC-AUDIT-COPY-LITERAL-V1` followed by NUL |
| Base raw-file digest | 32 | SHA-256 bytes |
| Target raw-file digest | 32 | SHA-256 bytes |
| Target raw-file length | 8 | Unsigned 64-bit little endian |

Operations follow until EOF. Their order defines the target byte order. `C` is byte 0x43, followed by an eight-byte little-endian base offset and eight-byte little-endian nonzero length. It copies that exact base range. `L` is byte 0x4c, followed by an eight-byte little-endian nonzero length and that many literal bytes. There is no path, JSON interpretation, compression instruction, or implicit metadata repair in the wire format. There is no operation count or final terminator. The target length and digest bind completeness.

The preserved example has 4,879 copy operations and 4,880 literal operations. Its 97-byte header, 82,943 bytes of copy framing, 43,920 bytes of literal framing, and 261,893 literal bytes give 388,853 bytes. Gzip level 6, empty gzip filename and timestamp zero yield the separately pinned 72,532-byte compressed patch. Raw and gzip digests are both preserved; no universal gzip-byte reproducibility across Python/zlib versions is assumed.

The producer recognizes declaration-object spans in the pinned Lean JSON serializer, indexes the base by unique declaration name, and copies only when both digest and direct raw-byte comparison agree. Header, footer, separators and every changed/new record are literal bytes. The name index chooses a candidate range; name equality alone is never evidence that its bytes match. The exact 19 changed inherited records and 9 new records are retained, without classifying any change away.

The prototype restoration uses the already portable base gzip and verifies its complete decompressed digest and byte length. Copy spans are sorted by base offset and must not overlap. One decompression pass writes copies at their recorded target offsets; literals are already written at their target offsets. Finally it verifies the target digest and compares every restored byte with the saved target. Sorting affects the read schedule only; target operation order remains fixed.

This decoder is bound to the two saved input identities and lengths. It is not a hardened general-purpose untrusted-delta decoder: operation-count budgets and an arbitrary-base protocol have not been implemented or accepted. Wrong magic/identities/serializer shape, duplicate declaration names, incomplete/overflowing target spans, invalid/overlapping copy spans, failed hashes or byte comparison, scratch exhaustion and allocation failure abort the prototype and preserve a failure receipt. The raw base, target and their accepted exports remain untouched.

The source is copied exactly from the preserved scratch experiment. Running the published script in this directory is neither necessary nor authorized: its output names are create-new and already present, and it retains the original fixed input paths. This package is a portable record of the experiment and patch format, not a scheduled new restoration run.
