# Same-device exact rule audit

17 October 2026. dot (OpenAI), working with Nolan.

**PASS: derived exact-Fraction consistency check of two previously certified declared-model controls.** Both satisfy Q >= 1-g and Q >= g-3. The smallest certified slack is approximately 0.000019545688886918565 (plus device, low edge). Full exact rational margins are in [the result](SAVED-PAIR-RULE-AUDIT.json); assumptions and limitations are in [the receipt](RECEIPT.md).

This reuses prior 1024-bit outward-enclosed intervals. It is not a fresh scattering solve, Lean verification, learned-model audit, experimental result, new master theorem or novelty claim. The plus device's g certifies positive Q; the minus device's g alone permits either sign. Known-model determinant computation is distinct from recovering an unknown determinant from one conductance value.

## Reproduction with Python standard library

1. Create a work directory with a `same-device-rule-audit` child containing the unchanged `check_saved_pair.py` from this packet.
2. Obtain the two immutable published inputs listed in [INPUT-MANIFEST.json](INPUT-MANIFEST.json), verify their SHA256 values, and save them at the listed `reproduction_path` relative to the work directory. The historical local directory names differ from the public source directory names; the manifest specifies both.
3. Run `python same-device-rule-audit/check_saved_pair.py` without optimization flags. It reads these inputs, uses `fractions.Fraction` for every accepting comparison, and writes `same-device-rule-audit/SAVED-PAIR-RULE-AUDIT.json`.
4. Compare the output bytes with the archived result. Expected SHA256: `8947f8f42734b35bd461e8aa7000b7617ad613da16eafd85e53f325004b56277`.

The script reports hashes but does not itself enforce pinned input hashes: perform step 2 before treating its output as this reproduced check. Display decimals do not decide acceptance. No solver or third-party packages are needed for this post-check.

The applicable [all-channel theorem packet](../all-channel/README.md) gives an admissible range in general; N=1 is the special exact identity Q=1-g. Prior unitary bounds and novelty limitations remain applicable.
