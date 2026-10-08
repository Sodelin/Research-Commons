# Actual179 cache-count correction

This additive note corrects one documentary description in [the dated 181 selection review](FINITE-OBSERVATION-ACTUAL179-181-SOURCE-SELECTION-REVIEW.md), immutable `b6776d019c813066458f9f292f5307ae4545016e`, SHA256 `385c4666de34722ddf91c6c074e35de81f8cd93dd534cf3204f5a6c3f9a4ce15`. Its sentence distinguishing the 3,584-module broader header graph from “the prior actual cache's 3,302 modules” incorrectly carried forward an earlier run's cache count. That number does not describe actual run 37738512508.

Independent read-only inspection of the preserved actual179 logs confirms that this run reports **3,584 downloaded and decompressed files**. In author receipt `cdf4c4c0f9e0f6de59a7701b14656565a84cc481`, the original connector log has 2,116,655 bytes and SHA256 `b65c176521e7797dd71ad91d4d4a6b318d3a6954c802ada6ed68d56e801850a5`. Its lines 5200–5202 say:

```text
2026-10-08T06:37:31.0846349Z Downloaded: 3584 file(s) [attempted 3584/3584 = 100%, 185 KB/s], Decompressed: 276
2026-10-08T06:37:31.0846741Z Decompressed 3584 file(s)
2026-10-08T06:37:31.0846989Z Already decompressed 3584 file(s)
```

The corrected timestamp-normalized actions.log has 1,763,754 bytes, SHA256 `7c2f67a89276e38cce1bc3f010de3432fe676ec0cf4b1754002c8b824de8b2ec`, and the same text at the corresponding lines. The preserved receipts-recovered.json has 97,749 bytes, SHA256 `4d1a2060b857453f516812b29adeccd92d5b508cba6e9c392e795994ee13eba2`; its actual lake exe cache get command exits 0, from `2026-10-08T06:36:55.486845+00:00` to `2026-10-08T06:37:31.080677+00:00`, and records output SHA256 `ce1cca4bcb18bcb2738a8334c1b4c3210ad3a9d12e60577a4e22056931bf42a0`.

The broader header dependency inventory separately contains 3,320 Mathlib modules plus 264 package-source modules, totaling 3,584. Its equality in size with the actual cache count does not itself authenticate cache contents or identify each source pin with a cache output. The complete external source-pin checks and cache-command transport remain distinct evidence scopes. The number 3,302 remains historical information from earlier runs, with no claim that it is the actual179 or current181 cache size.

This correction changes no source, import, target, runtime control, static selection or compiler input. It changes no accepted module, declaration, axiom or exact prior-row comparison. The actual179 review still authenticates all 181 noncache output hashes and the 4,209-owned/2,766-theorem inventory; its explicit exclusion of a cache-output hash reconstruction remains in force. No cache, compiler, Actions poll or archive operation was repeated. The dated review is retained byte-identically and this note supersedes only its erroneous attribution of the historical 3,302 count to actual179.
