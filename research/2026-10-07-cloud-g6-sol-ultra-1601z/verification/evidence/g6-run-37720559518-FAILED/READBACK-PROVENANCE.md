# Recovery transport

Official run, job and artifact metadata were retrieved through the authenticated GitHub connector. The original decoded connector job-log bytes are preserved without newline conversion: 2030560 bytes, SHA256 `fa071f92fed546cadd46de449cb68195297dd454248855f8bd86ebb9b8e18823`. `actions.log` normalizes only outer transport prefixes for the static recovery parser. All 176 frozen custom source hashes, all 176 command receipts and all 175 non-cache stdout hashes authenticate. Cache-progress transport is excluded from stdout reconstruction.

The terminal complete inventory was recovered losslessly from gzip/base64: 6,101,553 bytes, SHA256 `d61141f5293ad0b341657f5876c06810b7dad96b2dbb715850d57cfab677ab95`. Both reconstructed audit sources and their actual stdout hashes authenticate. Artifact 11526630412 is metadata only; no ZIP was downloaded and no archive equality is claimed.

Publication uses expected-parent non-force Git Data API. Each published file is checked by immutable Git blob identity and byte length. This identity check is not described as a literal second download of every large file. Independent official-terminal and author correspondence acceptance is separate.
