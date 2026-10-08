# Public packet provenance

The mathematical proof body is unchanged. The public copy has one nonmathematical edit: a single process-related item was removed from the initial status header. No other proof-file bytes changed. The original frozen file remains preserved separately; the unchanged independent review binds that original hash.

- Original reviewed `EXACT-PROJECTIVE-LAYER-AND-REPAIR-COST-CANDIDATE.md`: SHA256 `12bcba96d3f4c01732d818314c26537acbedcd3ef43475faeebbb813c31be1e2`.
- Published header-edited `EXACT-PROJECTIVE-LAYER-AND-REPAIR-COST-CANDIDATE.md`: SHA256 `94ef11739182863cfaa481d76d7fc19a07a3b0bd11f040e11330da594b856d76`.

The independent review contains no preparation-local paths and is reproduced without any textual sanitization or mathematical edits, under the delivery filename:

- `INDEPENDENT-HAND-REVIEW.md`: original and delivered SHA256 both `d8a807da75de7fa326f77aaef1a167d7ecec1c2e788aa089ff595db03198fa73`.

The source ledger cited in the frozen review had SHA256 `bb02e2c3a51b0f80fa74494165c592d44f827a4d251401dac58983bc7461bd64`. The delivered `SOURCE-PINS.json` is a public provenance derivative: it uses immutable publicly resolvable repository links and omits preparation-local copies and coordination-only context. Its own exact hash is in `MANIFEST.sha256`. This change is confined to provenance presentation; it does not alter the proof or its accepted hypotheses.

Referenced provider bodies remain at their immutable public source locations. Their publication status, scope and authorship are not changed by this packet. No compiler certificate, parameter extraction, scientific execution, or original G4 closure is added.

The `proof_sha256` field in SOURCE-PINS.json and the candidate hash in the unchanged review identify the original frozen reviewed file. The published-copy hash above and MANIFEST.sha256 identify the header-edited delivery file. The review verdict is not represented as an independent review of newly changed mathematics.
