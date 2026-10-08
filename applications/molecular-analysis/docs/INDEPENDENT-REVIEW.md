# Independent private molecular source and saved-receipt review

Reviewer and author: Cloud / Sol, `/root/source_backend_review_sol`. Root owns the implementation, tests, fixes and private publication. The reviewer authored none of this molecular implementation. Written 2026-10-08 after the final source repair; these findings and code stay in the private project.

**SOURCE/CODE ACCEPT for the experimental offline prototype at private source commit `eea390f70f7497f86200695d9de81666a8540eed`. SAVED AUTHOR-TEST RECEIPT AUTHENTICATION PASS: 87 tests.** No blocking defect remains among the scoped findings below. Acceptance is source inspection and static saved-evidence authentication, not independent execution, formal verification, live SDK integration or biological validation.

No reviewer build, test, native probe, project import, SDK installation, credential access or model API request occurred. Read-only inspection covered all Rust core/CLI bodies, Python contract/provider/CLI/module bodies and all four Python test files plus native tests. The only network operation retrieved official SDK source at its pinned public Git commit. Only these review documents were written; no implementation, workflow or Git mutation was made by the reviewer.

## Exact scientific and computational scope

The Rust core is an offline, bounded sequence constructor. It uses one-based VCF anchors converted once to original reference coordinates, checks the complete REF span, chromosome/assembly, distinct IDs, nonoverlap, explicit phase and authenticated caller-supplied adjacent guard bases. Equal-length substitutions and prefix-anchored insertions/deletions are supported; complex delins are refused. Constructing all REF/A/B/AB conditions from the same original reference, rather than applying B at shifted coordinates, is correct. Bounds and ASCII validation make the slicing and checked-coordinate argument coherent by source inspection. Crop refusal preserves every edited allele and retained declared endpoint ROI; deletion of biological reference bases is distinguished from cropping.

The Python native bridge records the actual binary/request identities, checks the returned window/phase/scenario schema, validates coordinate-map tiling and monotone reference segments, and accepts no silent Python fallback. Its normal native execution has a 30-second subprocess timeout. This does not authenticate arbitrary external executables to this source or prove hostile-host immutability; the inspected author's saved test binary is separately pinned.

Indel tracks map retained bases into reference coordinates, exclude inserted bases and zero-fill deleted bases. The original endpoint denominator remains fixed. Guard bases outside the original window are excluded from its endpoint values. Ambiguous coarse indel tracks are refused, and the original edited sequence digest survives alignment. This is an explicit comparison policy, not a claim that it matches the SDK variant scorer's insertion policy or measured transcript abundance.

Phase handling retains cis/trans evidence, labels non-cis AB as counterfactual, returns UNKNOWN for unknown phase even when the conditional calculation succeeds, and implements no diploid aggregation. Nonadditivity is `yAB-yA-yB+yREF` on the predeclared scale. Signed changes, per-scenario maxima and positional maximum-change diagnostics remain distinct; AVI/percentile scales cannot be added.

RNA expression masks are the supplied transcript exons clipped to the endpoint, not the union of all gene exons. Splice sites and site usage are distinct direct model modalities whose scalar aggregation is derived. Junctions and PSI remain explicitly unavailable. The PAS calculation requires two annotated, disjoint windows ordered along the transcript strand, and reports a smoothed distal/proximal coverage ratio. It is a declared proxy, not direct isoform usage or the official multisplit PAS scorer. Stable log and ratio arithmetic and finite-range refusals are consistent with those definitions; finite software tests do not establish universal numerical accuracy.

Settings, sequence, exact track name, origin/resolution, tissue, strand and annotation identifiers are matched across conditions. Forward-reference sequence remains in forward genomic orientation even for a minus-strand transcript; the requested returned track strand and PAS window order provide the strand-specific selection. TISSUE_AGNOSTIC is allowed only for declared splice-site metadata. Annotation IDs are supplied identities, not inferred model annotation.

Every inspected result boundary retains `biological_conclusion_established:false`. Synthetic provider outputs are labelled MOCK_SYNTHETIC. The injected SDK-shaped doubles produce the adapter's production-labelled Python object only within unit tests; those objects are not published as live evidence. No observed assay law, empirical calibration, causal biological interaction, disease/clinical result, confidence interval or original G1–G7/RNA-E8 applicability follows. The project applicability note states those missing bridges explicitly.

## Independent findings and root repairs

The original source allowed deterministic endpoint refusals to occur only after prediction. For example, a valid SNP request with expression aggregation `max` would make all four predictions before returning EXPRESSION_AGGREGATION/UNSUPPORTED. Root's `preflight_endpoints` now checks family/output pairing, supported aggregation, nonempty annotation masks, unavailable junctions and PAS count/window/order before any provider call. The CLI calls it before dispatch, and the direct haplotype service calls it before native construction/provider access. Existing scorer checks remain. Requests containing unsupported endpoints are refused as a whole; the independent scorer for already-computed predictions still supports explicit mixed availability. Four new integration tests verify relevant zero-call refusals and malformed phase handling.

The original phase membership check could raise TypeError for JSON list/dict values and turn malformed input into EXECUTION_FAILURE. The final string guard yields INVALID_INPUT for list, dict, null and Boolean kinds before prediction.

A further source finding was the unchecked `math.isfinite` conversion of arbitrarily large integer pseudocounts/track values. The final `_finite_number` rejects overflow safely and excludes Booleans; three new tests cover huge pseudocounts, huge track values and a nested JSON `1e999` float. The parser's iterative finite-float check prevents such decoded infinities from passing its finite-JSON boundary. This is scoped validation evidence, not an exhaustive parser robustness proof.

The synthetic PAS CLI input was missing from the original 20-entry freeze. The final 21-entry freeze includes its exact bytes. Earlier source/receipts are preserved independently; they are not silently relabelled as the repaired source.

## Official SDK source comparison

Official SDK repository Git commit: `038d253a5ca2fec46f4874f592d9ec67984cb497` (a Git commit, not a file SHA). Local `/tmp/ag-v1-dna_client.py` bytes exactly match the pinned raw URL. Source-only comparison confirms `create(api_key, model_version=..., timeout=...)`, `output_metadata(organism)`, and `predict_sequence(sequence, organism=..., requested_outputs=..., ontology_terms=..., interval=...)`. The actual ModelVersion enums ALL_FOLDS/FOLD_0..3, human Organism, OutputType enums, and Output/OutputMetadata `.get` methods match the adapter.

| Official source at that commit | SHA256 | Bytes |
|---|---|---:|
| dna_client.py | `e2ffb5cb6fefbe4ab619db1c679241030c03202430ba9a2ec3e3bfe102c53f6f` | 32705 |
| dna_model.py | `6296148c50bcd247e2aa96e8a863d4fd55cbe6665d84d92f7b0e04ce2e778fee` | 18040 |
| dna_output.py | `7983b13f8e74b4f9828ab7784bb6446697dce71f5c749c709d47248b363e2669` | 14890 |

The wrapper lazily imports the official SDK and preselects one exact track by name/tissue/strand, refusing missing or ambiguous metadata before inference. Model enums/SDK versions do not pin immutable server weights. The actual SDK `create(timeout=30)` bounds channel readiness; its prediction RPC does not receive a per-call deadline here. Root documents that bounded live execution, quota/retry/cancellation and authorized access/terms remain prerequisites to any live smoke test. No installed-SDK, server metadata or tissue-support acceptance is supplied by these doubles or this source comparison.

## Saved evidence authentication

The reviewer authenticated every final source pin against the final private Git object and current bytes, and checked it equals the author's before/after snapshots. Final receipt/log hashes and the actual binary bytes were checked without execution. Final gate: [attempt3 receipt](../reports/whole-product-attempt3/RECEIPT.json), source freeze, empty stdout and verbose stderr ending `Ran 87 tests` / `OK`, return code 0, no source/binary changes. The 120-second supervisor limit is an offline gate bound, not a live RPC bound.

Final receipt SHA `76ea42a4bbe6532ea935efefe554fbfe03ef7d1d0297ea8840ce7987ffa4050f`; freeze SHA `ec7237b6e7834bbcd69ec68f40e3a2dc5ef65a8bb9b84e7821ce1cf31fbe296c`; stderr SHA `a2482c9304fd1700d839863583f7b5f8b2e992119484435bf0b3088efa817136`. Native binary before/after/current SHA `e9de6be495cbba56b88e7d4c6d12ad932fa854bf916084a2bea7ed000c93c123`. Full exact mapping and static-review scope are in [INDEPENDENT-REVIEW.json](INDEPENDENT-REVIEW.json).

Historical evidence was authenticated separately: 18 Rust unit + 3 native CLI tests; 20 haplotype Python tests; RNA's initial failed fixture attempt followed by 23 passing tests; original whole-product 80 PASS; preflight-repair 84 PASS; three synthetic CLI demonstrations and an access check returning UNSUPPORTED/exit4 with live smoke PENDING. Those CLI demonstrations belong to their original saved source stage; no reviewer rerun of them or of any repaired tests occurred. The RNA standalone receipt pins source post-run only; the whole-product gates provide the before/after source checks. All are author execution evidence, not independent replay or biological evidence.

## Final source identities

| Private project path | SHA256 |
|---|---|
| core/Cargo.lock | `73ebb94de6906fb6c240aadf64a6de48e2f6e2809d6908f088b1ba58aff5f013` |
| core/Cargo.toml | `0ea30509a726f506f133066242c16f4ef51b4f01cb3456496c4621ec174e4fe1` |
| core/src/lib.rs | `82ff358661faa9f1d8ab858ec921f3392d566574f6b82c74a5edd681c39d89be` |
| core/src/main.rs | `67c71918807c3761407d2c425571533ce105318fc56978f01016c403b60c2ee2` |
| core/tests/cli.rs | `70e691a2ec473589f6246686e758474b82e78da7e7dd76ff14398e8b7bfab001` |
| examples/PUBLIC-REFERENCE-PROVENANCE.json | `cbae379681840aa965c6a7860757e13a27e83e7bdbbc1cb444451a840282f516` |
| examples/synthetic-rna-processing.json | `96b0f8c616d6e7f8fcd993aaba30bd5898356361960f760a19f8b2a4774b9625` |
| examples/tert-public-reference-mock.json | `37d20f4c5e252c0cc100333fc1d2fcb96a2b02a4395cad44e8035aa4a5ff2e1d` |
| examples/tert-rna-public-reference-mock.json | `8a72cbd5c348ee30798cdcf0bda2869e25274c507aa2a16f2a57498deaaa6163` |
| molecular_apps/__init__.py | `6ae150753184c2b8046c4394110ee07d9e98b5634f207344cc6cebf5a2c2ab67` |
| molecular_apps/__main__.py | `935a1c1166b0c1ea35a82256345000bf2c73ded718d77773bc27a71ecce28f7d` |
| molecular_apps/cli.py | `cddeec13db9194f5d3f59842e8e2531de3bd7fa6d295fad356d63199138f3449` |
| molecular_apps/contracts.py | `32d6b69ce48412de21e5160aac287415500c79a95aa306b29a6ea90ce3d71e67` |
| molecular_apps/haplotype.py | `a65f3d4cec728c9931763378218e242c6192980e7c58455fe624fe07edce9a70` |
| molecular_apps/providers.py | `a1494dd5de42dd77afed22396c6b45f41c8ebf1eaab596a819f95f7ad4befe01` |
| molecular_apps/rna_processing.py | `f0f46b37cefca4d232eb01f37be1c3aa0d5cec84da635e3b603c238711c2d68a` |
| tests/__init__.py | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| tests/test_contracts_and_cli.py | `b142751d88479af41074b2d6c520fa5191910d2b09a23cbf49254bd832045aec` |
| tests/test_haplotype.py | `48e9c415a1a53efd397f957cbb7810ed47cf0003381f8aa871b2919c16055b02` |
| tests/test_rna_processing.py | `69631d94db6aff9bdfe0da991216473c456114b122caec8cf596df9405cd5324` |
| tests/test_sdk_adapter_offline.py | `443913149d36534080f51d3f41d4e441235747d4de803f615288860eb0d1ed29` |

## Verdict and next gate

The scoped experimental offline implementation and the saved author receipts are accepted by this independent source review after the root repairs. This does not close the full scientific application or any G master. Live SDK integration, bounded execution/quota handling, real metadata/tissue coverage, empirical or held-out validation, calibrated observation/confidence and the original programme correspondence remain OPEN.

Next action: root privately publishes this review and the exact final source/receipt packet, and may publish only an intentionally shareable scope/evidence summary. Any live model request needs its separate access and bounded-execution gate; none is authorized or performed by this review.

## Dated final CLI and annotation-provenance addendum (2026-10-08 00:52 UTC)

The reviewer statically authenticated root's separate final-source CLI receipt `reports/cli-smoke-final/RECEIPT.json`, SHA `5f8205f762bfb7e5ba3e30b27b3e8f117ab1c56b10edc9b6f068305f0d1ca744`. All 21 source/input before/after hashes match the final 87-test freeze, the earlier independent review mapping and current file bytes. Actual native binary bytes match both recorded snapshots and the accepted `e9de6be495cbba56b88e7d4c6d12ad932fa854bf916084a2bea7ed000c93c123` identity. The four stdout and four stderr hashes were checked against saved files; stderr is empty in every row.

Root's new final-source executions completed 2026-10-08 00:51:15–00:51:17 UTC: TERT haplotype, TERT RNA and synthetic RNA/PAS each returned SUCCESS/exit0, MOCK_SYNTHETIC and `biological_conclusion_established:false`. The access check returned UNSUPPORTED/exit4 with the SDK/access-terms/key blockers and live smoke PENDING. This is actual new author execution evidence on the final repaired source. The prior CLI results retain their historical stage and were not relabelled. The reviewer did not execute any CLI, native binary, test, SDK or model request. The source/code acceptance at `eea390f70f7497f86200695d9de81666a8540eed` and all live/scientific scope limits are unchanged. Exact final row/output identities are appended to the review JSON.

Root identified a separate nonblocking annotation-provenance clarification: the frozen examples' `annotation_response_sha256` value `efa95c8560b2f506d259dcbc5a1eb46407b121cca99a2ec42650a877cd85946a` denotes the normalized, pretty-printed JSON artifact `/tmp/ag-tert-annotation.json`, not the raw HTTP response bytes. The reviewer authenticated those artifact bytes, their SHA and their exact indent-2 JSON-plus-newline form. No raw HTTP payload identity was authenticated or is claimed. Root will preserve the normalized public-annotation artifact and an additive correction privately; the frozen 21 inputs remain unchanged. This qualification does not weaken the inspected software/mock scope into a claim of measured biological validation.
