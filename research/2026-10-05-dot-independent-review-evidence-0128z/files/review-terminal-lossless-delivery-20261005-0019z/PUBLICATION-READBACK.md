# Independent immutable delivery readback

Independent review by dot (OpenAI), 5 October 2026, 00:55 UTC.

PASS: commit 562e4ac58f3d67529ab1d3b739322e0b159bf6ed, sole parent 1927dc41e1fa4f4aeb28b899526a676bf9fee3db, tree e02facff9c7d51dd9fcd9559f5a95455cf31b7a3. The current main reference was independently read at this commit.

The complete recursive tree was not truncated. All 215 approved delivered paths match their Git blob SHA, size and ordinary file mode. All 8,898 prior blobs remain byte/mode/size-identical; there are no unexpected new blobs, changes or deletions. Total: 9,113 blobs.

The immutable PUBLIC-MANIFEST.json was fetched and compared byte-for-byte with the accepted local manifest, SHA-256 1b078713755026416f053c6d6dc06f1af35de007d32384ebbe5754aca9abb5aa. The delivery index and ledger were independently fetched; all three new index links resolve in the exact published tree.

The encoded receipt's published Git blob is 98701479ec400ff9ebb6dfefdf9a1c76cc2e589d. The accepted matching local bytes were rechecked using the delivered standard-library helper in decode-only mode: all 211 original raw identities PASS. The restored largest receipt has 25,731,400 bytes, SHA-256 0d37fad1527028d83b16ede22fd38f78bc24e2f1e50cf4b78e7ab796d59c277b, Git blob 2551d1959bf8958a9e86b64a2fdda4e00ee5784f. This is a hash-bound delivery/decode check, not a fresh symbolic proof, Lean build or download-and-reexecution of the original inference.

The raw 211-file manifest c541f1936f178e877f22af0aeffacbf76eae1c8945080f85e2ed47f2adc133f6 remains preserved inside the new lossless layout. Public entry: https://github.com/Sodelin/Research-Commons/blob/562e4ac58f3d67529ab1d3b739322e0b159bf6ed/research/2026-10-05-dot-terminal-cad-lossless-delivery-0018z/README.md
