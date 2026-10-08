# Readback provenance

Official public GitHub run/jobs metadata and the complete decoded connector job log were retrieved after terminal failure. The original log is preserved byte-for-byte: 2,010,742 bytes, SHA256 48432640596c7a3e380c141fe3281e025b6bd94e3395fe2ce0c802f27ae744df. actions.log normalizes only the outer transport prefix for the unchanged recovery parser; actual command manifests, receipts and stdout hashes remain authoritative.

All 176 input hashes were authenticated against the immutable source snapshot built from exact 166-parent provider readback and the 11-file expected-parent freeze. The 178 snapshot files include 176 sources, the reviewed plan and unchanged attributed template. No unavailable local git object was treated as a source substitute.

The full actual gzip/base64 audit payload was recovered losslessly and rehashed. The selected audit and complete audit sources were reconstructed from actual successful inputs and compared with actual stdout hashes. All 171 non-cache stdout blocks match. Cache progress rendering is excluded; requested modules with failed or blocked execution are excluded from both acceptance audits.

Artifact 11524633732 is metadata only. No ZIP archive was downloaded and no archive correspondence or signed-URL disclosure is claimed. Publication preserves exact blobs with expected-parent force:false main update, followed by Gitblob/size directory readback. Independent terminal authentication remains a separate required gate.
