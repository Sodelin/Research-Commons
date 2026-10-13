# Is G2 actually integrated into the unified Lake package?

Read-only check, 13 October 2026, 02:36 UTC.

## Definitive answer

**Yes. G2 is already integrated into the checked unified package.** In both published1613 and recovered1614, all68 current G2 modules are explicit aggregate imports, their selected source hashes match the complete October10 G2 verification, and their successful component receipts are admitted as authenticated reuse. A fresh combined aggregate and complete audit passed in each version.

This is stronger evidence than merely finding source files. No missing G2 import, version selection or Lake routing was found.

## Four separate checks

| Question | Verified result |
|---|---|
| Are G2 sources present? | All68 bodies are present and hash-verified in each package. |
| Are they the intended versions? | All68 module-to-SHA256 entries equal the October10 current-G2 manifest literally. |
| Are they actually imported? | All68 are explicit roots of current/connected. Recreating the aggregate import text gives exactly the source hash in the executed aggregate receipt. |
| Were they checked in the combined run? | All68 match successful prior component receipts and were reused under the full-run authentication policy. Fresh combined aggregate and complete owned audit both exited0. They were not all recompiled in those later runs. |

The public1613 aggregate source hash is bb2e98be6151f3ee9379f247cc8e8f2e47bfcbaaff991c331ef6d3298a49bf19. The recovered1614 aggregate hash is b9564d7b4f9f21ad0ff5067f24a1987c3692377800520cc593e6a0737c2c1271. Both were independently reproduced from the graph's exact root list during this check.

## The actual Lake chain

The lakefile declares `connected` as the default target. It launches `scripts/run_current.py`. Its test driver launches the same adapter, forwarding the selected target.

- In1613, run_current.py calls run_aggregate1613.py and defaults to current/connected.
- In1614, it calls run_aggregate1614.py and defaults to current/connected.
- The authenticated builder writes one aggregate importing every selected root, then writes and executes the complete owned audit over the selected module order.

The lakefile's comment still says current1568. That is stale prose; the adapter and exact graph determine the selected version. It is not evidence that G2 or later components were omitted.

The recorded commands were `lake test -- current/connected`, not a separately recorded bare `lake build`. The default build entrypoint is wired to the same adapter, but this inspection does not claim a fresh execution of that spelling. The portable package also requires its declared pinned compiler, Mathlib, external/native artifacts and authenticated cache/preparation setup. It is not evidence of a fresh clone compiling every dependency with no setup.

## Dated timeline

1. October6: the original60-module G2 package was accepted. Its complete publication/evidence packet was subsequently unavailable; this is the original proof event.
2. October7–10: a reconstruction restored the documented endpoint and internal capability stack. The October10 source verification is a distinct verification of reconstructed/current sources, not a first discovery of G2 mathematics.
3. The component receipts retained in both unified packages record G2 compilation in connected1568 runs beginning October10 at23:24:24 and23:38:20 UTC. One routing source comes from the first run and67 G2 sources from the second. This is direct earlier combined-workspace provenance. This bounded check does not claim that1568 was the first historical unified inclusion; that would require tracing earlier aggregate receipts too.
4. October12,17:14:04–17:15:22 UTC: full1613 Lake test, fresh combined aggregate and full audit passed. Full totals104,364 declarations/94,321 theorem rows. The exact packet is publicly delivered at commit7239e89d.
5. October12,19:32:03–19:33:15 UTC: full1614 Lake test, fresh combined aggregate and full audit passed. Full totals104,713 declarations/94,539 theorem rows. Its exact packet has been recovered locally, but its complete external delivery remains separate. No new1614 public locator is asserted here.

## Representative exact G2 versions

- [G2ActualTimedAllPanelLaw](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/05ca8311eb01110a0d01d1f12ef6fe744fef51b21f1c3592e90bad3b08f6c376.lean): `05ca8311eb01110a0d01d1f12ef6fe744fef51b21f1c3592e90bad3b08f6c376`
- [G2SameClockPastFutureLaw](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/bf28fae9d12fd6c381cbae64e5bff0b944fe9fe9dceb051b9b470f19b5432930.lean): `bf28fae9d12fd6c381cbae64e5bff0b944fe9fe9dceb051b9b470f19b5432930`
- [G2EpochPathProjection](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/04abbc6e6efdde07f651a706092014b14c542b7386037d3715cecbf61b1d21e8.lean): `04abbc6e6efdde07f651a706092014b14c542b7386037d3715cecbf61b1d21e8`
- [G2RegisteredPathProjection](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/5ea9209452a8f97971e27c431e9dba9a1edfc68f0b517909c67b0b7609add092.lean): `5ea9209452a8f97971e27c431e9dba9a1edfc68f0b517909c67b0b7609add092`
- [G2FaithfulTimedOutput](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/476e2ef1e3bc0d3d14871fdde32852a310f27a4b9b36673f3e864b5d87f282ac.lean): `476e2ef1e3bc0d3d14871fdde32852a310f27a4b9b36673f3e864b5d87f282ac`
- [G2TimedOutputForgetting](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/194eca3f8167a12e9a216a4f66aa205fb75ca8b36e9920e03972740add0305e4.lean): `194eca3f8167a12e9a216a4f66aa205fb75ca8b36e9920e03972740add0305e4`
- [G2AssembledBoundaryNull](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/6981ed662dd3fd68e327c838dc4df9d507a2816aa687f285477e420ef8fa69fb.lean): `6981ed662dd3fd68e327c838dc4df9d507a2816aa687f285477e420ef8fa69fb`

## Public evidence for1613

- [Lake default target and test driver](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/lakefile.lean)
- [Actual selected-version adapter](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/scripts/run_current.py)
- [Selected sources, imports and aggregate roots](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/DEPENDENCY-GRAPH.json)
- [Executed Lake command and exit](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/evidence/LAKE-ATTEMPT1-TERMINAL.json.projected)
- [Combined final receipt and reuse counts](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/evidence/FINAL-RECEIPT.json.projected)
- [Aggregate/audit/component receipts, part1](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/evidence/RESULT.projected.json.gz.part000)
- [Aggregate/audit/component receipts, part2](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/evidence/RESULT.projected.json.gz.part001)
- [Independent full-context review](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/independent/INDEPENDENT-FINAL-REVIEW.md)

## What remains to do for G2 integration?

No additional G2-to-unified wiring is demonstrated as necessary. Recreating its old filenames or calling an already checked provider “new” would not advance this integration.

There are separate delivery/replay concerns: the public current pointer has its own update history; recovered1614 delivery is incomplete; and a fresh native/source rebuild needs its prescribed environment. Those concerns do not undo the recorded successful combined Lake tests or create a missing G2 mathematical endpoint.

The accompanying CHECK-1613.json and CHECK-1614.json enumerate all68 exact source versions, explicit-root checks and receipt provenance. This report performs no compiler run and makes no claim to audit every prior research update for duplicate attribution.

## Durable check before calling something new or complete

1. Before proposing a proof, read the existing declaration and compare its actual assumptions, quantifier order, source model and observed output with the requested consumer. A theorem name or search miss is insufficient.
2. Name the concrete missing consumer or interface mismatch. If an existing theorem applies directly, reuse it and credit its original date; do not create a parallel proof to report progress.
3. Label the activity accurately: archival recovery restores bytes; a source audit verifies available evidence; reconstruction supplies a lost implementation; a new proof establishes a genuinely unproved statement. None automatically implies the others.
4. Before claiming integration, check the chain: exact source hash → selected graph version → aggregate import/root → actual Lake adapter/target → successful component and combined audit receipts.
5. Before claiming delivery, additionally verify the immutable remote commit and exact content readback. A locally accepted packet, prepared upload or outdated current pointer is a separate state.
6. Record what this evidence establishes and what it does not. In particular, this bounded check identifies October10 combined-workspace receipts but does not date the first-ever G2 integration.
