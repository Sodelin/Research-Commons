# Root review of the deletion-only endpoint-history repair

Contributor: CLOUD-G6-SOL-ULTRA-20261007, root integration lane. Reviewed 8 October 2026, 01:41 UTC; preserved after the resumed general-proof priority. **SOURCE ACCEPTED; compiler result pending at this gate.**

The previous actual run [37713030087](https://github.com/Sodelin/Research-Commons/actions/runs/37713030087), frozen at `9caec2d7309fb8c5bc249b213e76f43eee5fc738`, failed in ActualCalendarEndpointHistory with “No goals to be solved” at line 143. The preceding `rw [PMF.map_comp]` and `congr 1` had already closed that goal. The failed module and its recovery reports remain excluded; the unchanged accepted inventory is 163 modules, 344 named reports, 3,965 owned declarations and 2,589 theorems.

I inspected the complete frozen failed source, candidate and literal diff from [preparation d187843](https://github.com/Sodelin/Research-Commons/tree/d187843abedd2542a96b3aab52e8ffed7d631acf/research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/preparation/endpoint-history-redundant-tactic). Removing exactly the unique `funext z` line and following `simp only [Function.comp_def, endpointHistoryReadout, Fin.cons_zero, Fin.tail_cons]` reconstructs the entire candidate byte for byte. Every other byte remains unchanged.

| Identity | SHA |
|---|---|
| Failed source SHA256 | `d6a2be33078a71362f0b86bf052185d84d66f2da17bc008a852a28dfd17ed257` |
| Candidate SHA256 | `e420a827bad976a4fc026bcc704e4e760cd41a5664169da7750d32c09d6c382a` |
| Literal diff SHA256 | `da6ad2b758ab15acc0d6de262942adb967b22818dee040d19d1f593610d0ae0d` |
| Failed Git blob | `101a7f55b4219ed5b57192acfe1361defebbfe43` |
| Candidate Git blob | `4e4c12c009e790bdd0e176b87eb815f8e1e34e39` |

This gate changes no import, statement, premise, initial Code/matrix, source bank, probability definition, physical operation, or full-history readout. The earlier [root proof/API review](ENDPOINT-HISTORY-ACTUAL-REPAIR-ROOT-REVIEW.md) applies to the inherited contract. The [primary deletion-only source review](../2026-10-07-cloud-independent-auditor-1616z/ENDPOINT-HISTORY-REDUNDANT-TACTIC-SOURCE-REVIEW.md) independently accepts the same exact change, while its [failed-run review](../2026-10-07-cloud-independent-auditor-1616z/ENDPOINT-HISTORY-REDUNDANT-TACTIC-FAILED-REVIEW.md) authenticates the unchanged accepted inventory.

The sole successor [37714595388](https://github.com/Sodelin/Research-Commons/actions/runs/37714595388), frozen at `410c21faae9e3e16c100f22daeaa384ea8ae3702`, preserves the same 165-module/358-report selection and every other source hash. Observation remains unchanged; the future CompleteObservationPrefix consumer is excluded. At publication this job is active, not accepted. One compiler owner runs and recovers it; this review ran no compiler or duplicate watcher.

Full physical-past initialization, actual menu/source admission, effective numerical extraction and the complete G6 master remain separate obligations. AlphaGenome/API work is deferred under the latest user instruction.
