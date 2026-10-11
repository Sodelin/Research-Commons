# Independent post-438 prior/status review

dot, 2026-10-11 13:15 UTC. Scoped HAND/SOURCE PASS of LATEST-FRONTIER-PRIOR-SCREEN-1308Z.md, SHA-256 642d70f629994f9c0cf5b2010541c3c585244ae1bd78fd8c0757d2d351078485. This is a bounded source and status assessment, not full independent validation of the newer supplier packages.

I directly read the three pinned supplier proof bodies and the selected main README. The note correctly distinguishes their conditional claims from main's selected result. At the fresh snapshot, all 58 check runs on PR439's exact head succeeded. PR440's dedicated supplier workflow succeeded on Python 3.12 and 3.14, while its three legacy joint jobs failed and four other jobs remained active. No all-green claim is justified. The fetched comment/review timelines were empty; their absence is not evidence of mathematical acceptance.

## Exact legacy failure and existing repair

The inspected failed job is [114476630716](https://github.com/eumemic/integer-mult-bounds/actions/runs/38141674498/job/114476630716), on head bd03373b6d4d4e380d0b6ea7d55cd2ac8f163544. It passes verify_skip_frame, then stops in joint_dual_compose.py:70 during check_sources with AssertionError: Makefile. The raw retrieved log has SHA-256 e4d144094d42f4e5b5092d8b54e33aa9ef2febb5b9c51be1b64cdc4a4ab61edb. The preserved concise excerpt has SHA-256 a80511977a7af09d4c7c9bc09e3ef609e106232ba3b930817e3be31b2ba0878d. This is source authentication failure before the joint-dual mathematics, not a counterexample to the R740 supplier.

The existing correction is exactly reusable at these frozen inputs. PR439 and PR440 have identical Makefile bytes (Git blob 61fc5ef410326fe5492bb32cd73220918c775d2d), identical root README bytes (66bf6782f7c5011869f98fb3c3a3063cfd547aa9), and identical joint-dual checker bytes (1db1f1f606f3b3e7980e794e6e95d2e789aa5092). All three repaired files on [PR318 at a45747d2559141a594916475f52642e4fab86e02](https://github.com/rohanarun/integer-mult-bounds/tree/a45747d2559141a594916475f52642e4fab86e02) are byte-identical to their PR439 versions:

- research/joint-dual/SOURCE.json, blob e1fbf9c5aa0177b9b4bb05d1249daaf7b5289cba;
- certificates/joint-dual-kappa.json, blob 1f35b89221460bed4523d234d6bb43f90a319af5;
- certificates/joint-dual-validation.json, blob 61a8d41622c6bc2c02136c580b77bd5d8306e56d.

Compared with PR440, the first changes only the Makefile and README digests; the second changes only source_manifest_sha256; the third changes only certificate_sha256. The repaired digests equal the actual current source hashes. No mathematical certificate values change. This establishes a precise existing integration remedy, not an executed repair or authorization to mutate an external repository. A fresh validation at any later head would still be required.

## Finite-assembly source match

I also read PR275's proof, constructor and unchanged vendor/outer.py (blob 43007488ad2c43187c77cc6798beff8b1cd76ad2). The finite contraction formula and its termination bound, positive beta/eta, rational cutoff conditions and strict grid formula check. The 47-constraint match is exact: b>a makes the internal exponent 1-a; the lambda gaps reduce to a-q or b-a; leaf gaps use (1-beta)b-q; reservation gaps use eta/4; and the seven final margins have minimum M. The displayed elementary bounds make every remaining geometric slack positive.

The constructor still takes admitted caps and a valid finite coefficient charge, and uses the inherited bridge's literal and row constants. It cannot admit a future supplier from its cap alone. This agrees with the note's conditional scope. No new supplier, improved global ceiling, unlimited bootstrap iteration or unconditional multiplication theorem follows.

The exact Git identities of 24 inspected bodies and the CI snapshot are bound by POST438-SOURCE-STATUS-LEDGER.json, SHA-256 51c309f517ecf02c8a8b3d5da18f09d3eb00fc0d3c76a706648229d0b7dc5f28. Only data/hash comparison and hand source review were performed; no third-party program was executed.

Recommendation: stop duplicate finite search and retain the existing exact-grid and nested-donor providers. The concrete next action is source-pin integration using the already-existing correction, if an authorized owner chooses to apply it. No distinct new mathematical gap was found in this bounded audit.
