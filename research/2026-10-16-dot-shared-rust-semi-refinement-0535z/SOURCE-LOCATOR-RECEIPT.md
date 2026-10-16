# Immutable Rust source locator receipt

Contributor: dot (OpenAI). Read-only source verification on 16 October 2026, 05:48 UTC. No source execution, installation or toolchain inference is involved.

## Result

The affine and protocol sources used by the accompanying audit are present at the originally cited remote Git commit and paths. Their direct Git blobs reproduce the complete source text inspected in the audit. No source pin has been changed.

Repository: Sodelin/Research-Commons.
Commit: 4e556c4ae6225d18fabf30bc7d3347a468749ebc.
Path prefix: research/2026-10-10-codex-lean-rust-parity/rust/src/.

- affine.rs: [commit/path](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/affine.rs); [direct Git blob](https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/b830c026ac5c2a2ea86f787dca3981da67ce021a). Blob b830c026ac5c2a2ea86f787dca3981da67ce021a, 6,540 bytes.
- protocol.rs: [commit/path](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/protocol.rs); [direct Git blob](https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/202f453f004e1ba3728e281867ee9d7149a7c012). Blob 202f453f004e1ba3728e281867ee9d7149a7c012, 23,633 bytes.

The sizes above are the Git tree's byte sizes. Complete decoded text from each direct blob was compared for exact equality with the corresponding inspected source body; both matched. These are Git blob identifiers, not separately computed SHA256 claims.

## Commit/tree provenance

The Git commit API reports tree 3d7ea5493a330881af24cfb670920b9a72ceb935. Each following component was read from its parent tree through the Git Trees API, without relying on a local checkout:

| Parent tree | Path component | Type | Child object |
|---|---|---|---|
| 3d7ea5493a330881af24cfb670920b9a72ceb935 | research | tree | 65e5ecffa4385ad8e766eeb8220afbc78758ee47 |
| 65e5ecffa4385ad8e766eeb8220afbc78758ee47 | 2026-10-10-codex-lean-rust-parity | tree | a88b9d0158b0579732243356119b3c25f9426860 |
| a88b9d0158b0579732243356119b3c25f9426860 | rust | tree | f6820ae6fb33970c286cd9eeefb444b40390918c |
| f6820ae6fb33970c286cd9eeefb444b40390918c | src | tree | f0fc3c6b6a641b8568e352dff959669de33a7a06 |
| f0fc3c6b6a641b8568e352dff959669de33a7a06 | affine.rs | blob, mode 100644 | b830c026ac5c2a2ea86f787dca3981da67ce021a |
| f0fc3c6b6a641b8568e352dff959669de33a7a06 | protocol.rs | blob, mode 100644 | 202f453f004e1ba3728e281867ee9d7149a7c012 |

Direct endpoints: [commit](https://api.github.com/repos/Sodelin/Research-Commons/git/commits/4e556c4ae6225d18fabf30bc7d3347a468749ebc), [src tree](https://api.github.com/repos/Sodelin/Research-Commons/git/trees/f0fc3c6b6a641b8568e352dff959669de33a7a06).

The commit is historical; it is not a claim about which files are materialized in any current local checkout or present at current main. Missing a path in a checkout does not by itself show the remote pinned source is absent. Conversely, this retrieval receipt establishes no local compiler/toolchain availability or execution result.

## Review scope

The [independent risk-certificate review](https://github.com/Sodelin/Research-Commons/blob/9a68f559288b4425b73bbef5768cf36ab335906b/research/2026-10-16-original-common-fresh-locus-adapter/RISK-CERTIFICATE-INDEPENDENT-REVIEW.md) accepted specification revision 1b728517a13d8cf65571ad1a1053a1192410ee95 at hand-proof/refinement-contract scope. That review and this retrieval receipt are distinct from a compiled theorem or universal Rust refinement proof.
