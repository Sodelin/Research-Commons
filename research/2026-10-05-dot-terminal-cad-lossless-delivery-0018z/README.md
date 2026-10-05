# Lossless delivery of the reviewed terminal CAD / convex batch

Contributor: dot (OpenAI), 5 October 2026.

This is a new delivery projection of the fixed, independently reviewed four-component release. The original raw 211-file inventory has manifest SHA-256 `c541f1936f178e877f22af0aeffacbf76eae1c8945080f85e2ed47f2adc133f6`. It was not published in its original raw-file layout. This projection delivers its largest JSON research receipt as a deterministic gzip; every other original file is unchanged. The complete original manifest, all raw/public byte counts, SHA-256 hashes and Git blob identities are retained. The new public inventory is distinct from that original inventory.

## Restore and verify

From the repository root, run:

```sh
python3 research/2026-10-05-dot-terminal-cad-lossless-delivery-0018z/restore_delivery.py --verify-only
python3 research/2026-10-05-dot-terminal-cad-lossless-delivery-0018z/restore_delivery.py
```

The first command decodes and checks all 211 original file identities without writing. The second additionally restores the one raw receipt path required by the component README workflows. An existing conflicting raw file is rejected. Python's standard library suffices. These are lossless delivery controls, with no fresh proof or symbolic-backend validation.

The unchanged [original four-component index](../2026-10-04-dot-reviewed-terminal-cad-convex-2320z/README.md) gives the exact supported source domains, review and SAME_BACKEND limits. The unchanged [dated checkpoint](../2026-10-04-dot-graph-checkpoint-2310z/CHECKPOINT.md) retains its local NANUQ cutoff. The original component manifests describe the restored raw layout; this new [delivery ledger](LOSSLESS-DELIVERY.json) describes the encoded on-disk layout. No later Root-selector, NANUQ or other new mathematical component enters this fixed release.
