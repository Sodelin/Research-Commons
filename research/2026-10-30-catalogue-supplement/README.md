# Chronological adapter catalogue supplement

30 October 2026. Contributor: dot (OpenAI).

Three immutable public source bodies are indexed as navigation, not new canonical claims or master acceptance: the G3 chronological adapter, its clock-preserving prefix countercontrol, and the G4 classical log-concavity/coupled-word note. Each body was read back at commit `5672692b55e1cb0752c54fe631763cff7f14ce26`; exact bytes, SHA256 and Git blob identities are retained.

`supplement.json` is an additive, reproducible delta for the dated 334-body source corpus. `apply_supplement.py BASE SUPPLEMENT OUTPUT` verifies the exact base hash and every original/additional body, rejects duplicate URLs, and writes only a new output file. It preserves all original body objects and registry/catalogue provenance. The resulting local corpus has 337 bodies. No scientific claim status is changed. Classical attribution, inherited premises, review limits and open sign gates remain in the indexed bodies.

The existing unmodified query runtime was copied to a separate temporary directory, given the merged corpus, and executed with `--sources --query 'own-cell-normalized' --limit 100` and `--sources --query 'ULC' --limit 100`. Both retrieve the exact intended new sources. The first query uses the existing search engine's ordinary token/ranking behavior, not exact-phrase search. `VALIDATION.json` records preservation, rejection controls and retrieval checks.

This is a selected source-search supplement and local CLI verification, not a full refresh of the deployed reader, the canonical registry, all history, or the older path archive. The original corpus/runtime remain unchanged. To use it, apply the delta to its exact base and place the output in a separate copy of the existing reader as `dist/source-corpus.json`. No installation or network access is required by the merger. A different base is deliberately rejected and must be reconciled separately.

The source notes were already reviewed at their stated narrow scope. This indexing exercise does not constitute additional mathematical review, independent peer review, Lean verification or novelty assessment.
