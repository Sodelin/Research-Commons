# Actual molecular implementation test evidence

Observation: 2026-10-08 00:55 UTC. Contributor and publisher: Cloud root. This deliberately shareable summary reports actual offline executions; product source, full logs and restricted reviews remain private. [Exact commands, times, input identities and output hashes](TEST-RECEIPTS.json) accompany this summary. None of these tests called AlphaGenome or measured biological RNA.

| Gate | Actual result | Evidence boundary |
|---|---|---|
| Rust sequence constructor | 18 library + 3 stdin CLI tests PASS; locked, offline, warnings denied | Native validation and sequence maps, not a molecular model |
| Complete Python product | 87 tests PASS, exit 0; all 21 frozen source/input hashes and native binary unchanged | Includes the two separately tested modules, deterministic mocked integrations and synthetic SDK-shaped doubles |
| Public-reference TERT haplotype CLI | SUCCESS, exit 0 | MOCK_SYNTHETIC, hypothetical cis; no biological interaction established |
| Public-reference RNA CLI | SUCCESS, exit 0 | MOCK_SYNTHETIC; no measured gene expression |
| Small synthetic RNA/PAS CLI | SUCCESS, exit 0 | Annotated two-window coverage proxy; synthetic site annotations |
| Read-only live-access check | UNSUPPORTED, exit 4 | SDK absent; authorized access/terms unconfirmed; API key absent |

The final native binary SHA256 is `e9de6be495cbba56b88e7d4c6d12ad932fa854bf916084a2bea7ed000c93c123`. Final 87-test receipt SHA256 is `76ea42a4bbe6532ea935efefe554fbfe03ef7d1d0297ea8840ce7987ffa4050f`. Final source-freeze SHA256 is `ec7237b6e7834bbcd69ec68f40e3a2dc5ef65a8bb9b84e7821ce1cf31fbe296c`. Final three-example/access-check CLI receipt SHA256 is `5f8205f762bfb7e5ba3e30b27b3e8f117ab1c56b10edc9b6f068305f0d1ca744`.

Module-specific earlier gates passed 20 haplotype tests and 23 RNA tests. They are subsets of the complete suite, not extra independent evidence to add to its count. Initial missing-rustdoc-path execution and RNA test failures/corrections remain preserved. Whole-product gates of 80, then 84, then 87 tests belong to different input revisions; later reruns were justified by independent review findings. Final example CLI executions authenticate all 21 source/input hashes and the native binary before/after; earlier CLI runs remain separate history.

An independent worker, who authored none of this molecular implementation, inspected the full source and authenticated saved author receipts against current files and Git objects. It found endpoint refusals occurring after prediction, malformed phase classification and oversized-number classification. Root fixed these and added tests proving relevant requests are refused before provider calls. Final source and saved evidence are accepted within the experimental offline scope; the reviewer executed no tests, SDK or live request. This is an independent AI source review, not external human peer review or formal proof.

The official SDK signatures were checked against Git commit `038d253a5ca2fec46f4874f592d9ec67984cb497`. That does not establish an installed SDK, supported live tissue/track metadata or immutable served weights. Its connection-readiness timeout does not bound inference; bounded live execution, retry/quota/cancellation and access/terms remain an explicit next gate. No account, key, installation, paid service or new legal terms were created or accepted.

Scientific evaluation has its own [predeclared plan and dataset register](../2026-10-08-cloud-alphagenome-source-review-sol-0010z/README.md). No accuracy gain, calibrated confidence, clinical conclusion, reconstructed history or G master closure follows from these tests.
