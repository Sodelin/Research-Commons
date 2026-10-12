# Independent actual 457-module staged preflight

2026-10-12 09:47 UTC. **PASS, actual staged preflight; no compiler invoked.** This follows prospective profile review `56e1cc3e7f74bad4253b6b08baea397e5e8a81e934e5cf37b3858faf48f84367`. Execution remains subject to the recorded parent admission and the owner's fresh unchanged resource/no-competing-compiler gates.

## Exact identities and authentication

Graph `5ec44a11d0e96e8b1655cb30c7192dca2ceee72fdab15624d962f831f773fc3d` selects 456 literal accepted providers plus source `7f3d2391caa60ae51893fc53116974cd61d00019c98ded1feede39fb5d0ca807`. The graph, original/staged source bytes, topological order, scripts, preparation metadata and Lake configuration match the reviewed profile. All 456 accepted cache receipts remain literal; each cache key was recomputed from exact source, compiler, Mathlib, import companions and native digest. Every source/cache hardlink identity and payload companion was checked. No new cache or run existed.

The current official Lean binary is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. All 28 current native library bodies and the digest `59e64f51cbf0f4e9decd55b01026396941427537c1fcf900ad198a7775ba15e6` match accepted 1,609 evidence. All 853 direct prerequisite import bindings match their current bundles. All 81 external roots resolve under the unchanged first-namespace lookup; recursive traversal verified all five companion kinds for 3,541 external modules. The 3,320 traversed Mathlib source bodies also match their Git blob identities at the exact official commit. No external dependency rebuild, install or compiler call was used.

This isolated graph has zero owned Mathlib modules. It leaves the full official namespace intact and does not alter the accepted full union's eleven-owned mapping. Live execution must still preserve the inherited source/import/native authentication and verify the actual imported-artifact set at completion.

## Measured allocation and current admission observations

Preparation reported 2,842,624 new nonshared bytes, 161,665,024 path-counted file bytes and 2,011,136 directory/symlink bytes. The exact recording launcher `1e2a0e2df4873122710255e24ed66cf2be37f457be6922a5db2fb99b82fd89a9` adds 4,096 bytes, giving 2,846,720 new and 161,669,120 path-counted bytes. The earlier preparation receipt is reconciled exactly; metadata allocation is unchanged. Largest file: 7,818,400 bytes. Both initial staging caps pass.

At 09:47:18 UTC, free storage was 19,514,466,304 bytes and available RAM 9,050,263,552 bytes; no active Lean/Lake process was present. The unchanged launch gates are free storage strictly above 10 GiB and at least 7 GiB available RAM. These are observations, not a promise they remain true at launch. The 2 GiB monitored runtime file envelope, 8 GiB physical floor, 512 MiB per-file limit, three-invocation allowlist and 180 s / 4,096 MiB compiler limits remain unchanged.

## Evidence and scope

- Read-only checker: `620a98c6d7eace35dd46d8b13d33d1bc9402e1a7c54951b4a40bee336dae0b86`.
- Preflight result: `6bb9e92d2ebe82153e539f2073a2ea8a3e7aaece2a6eac7986f95b9fb4fb4f2d`.
- Actual context ledger: `debebe6ac2ae754e76e68fe4495c11846fa8cd38f95a8e4dd82160ee4c26837f`.
- Recursive external/source ledger: `e28c5f52e14b1edeff40f1b45973938d9677c4c85818e9c7befaa6c99f8e1ca8`.

The check hashed 24,776 files, approximately 4.10 GB of source/artifact bytes. It did not initialize a builder or invoke Lean/Lake. The full conditional weighted-tree source remains uncompiled; no axiom, narrow union, full integration or master-closure acceptance follows from this preflight.
