# Accepted named decoder: independent transport-repair review

Contributor: Codex Rust implementation role, 10 October 2026, **10:42 PDT (17:42 UTC)**.
Status: sourced semantic/source-identity review of a separately kernel-accepted named proof adapter. No compiler, Lean evaluator or native solver invocation.

The accepted [G7NamedCalendarSourceAdmission.lean](../../reuse/sources/G7NamedCalendarSourceAdmission.lean), SHA256 `7c365d3d7d7c75a7b592443fb82d68a89a8df7000347dcbb8352b988b47f780e`, preserves the exact N2/NP graph, taxon, hybrid and original parent-occurrence data reviewed in the [17:34 static note](NAMED-CALENDAR-ADMISSION-STATIC-REVIEW-20261010T1734Z.md). No semantic weakening or actionable mismatch was found. This supplement records the accepted derivative; it does not alter the old source, its failed elaboration evidence or the original pending-kernel review.

The [fresh review receipt](../evidence/named-calendar-adapter-repair-review-1/RECEIPT.json), SHA256 `1b48934659c1e94049c50f431fbe1e0ff860fdf6ba327ecee2e5e7dc705d55bf`, authenticates 41 current/preserved text artifacts. It rechecks all 11 original source bodies, three unchanged raw request pairs and the two original code-input projections. Of the original static review's 33 watched artifacts, 32 are unchanged; the sole intentional derivative is the adapter source, whose original SHA256 `51e5c021be62995959abadc8b0f6d9c065ea1bc7495ce60292654db6be059534` is still authenticated at its [preserved failed-source path](../../reuse/failed-sources/51e5c021be62995959abadc8b0f6d9c065ea1bc7495ce60292654db6be059534.lean). All artifacts watched during this new review remained stable. Only text source/capture/diff files were copied; zero ELF files were copied.

## Exact cast change

The entire accepted file equals the preserved original after replacing one dependent registry transport expression. The [saved diff](../evidence/named-calendar-adapter-repair-review-1/TRANSPORT-DIFF.txt) changes contextual substitution by `fork_decodedSource_eq_N2` to:

```lean
Eq.mp
  (congrArg
    (fun N : RootedBinary (Fin 3) (Fin 2) (Fin 2) => OriginalParentRegistry N)
    fork_decodedSource_eq_N2)
  (decodedRegistry forkCode fork_binaryValid fork_registryValid)
```

This explicitly gives the type family through which the decoded registry moves from the decoded fork source to unchanged N2. The destination remains `OriginalWordFixture.registry2`, and the proof body remains `registry2_unique _`. No premise is removed, no new source or registry is selected, and no label/parent map changes. Imports, graph literals and the other proof bodies are identical. The earlier failure was dependent elaboration at this expression; the earlier review had deliberately left kernel acceptance pending.

N2 still has original edges 0/1 from root 0 to taxon leaves 1/2 and no hybrid IDs. Its `BinaryValid` consumer uses every accepted N2 `RootedBinary` field, including reachability and least-stable root; the empty registry and cut-child clauses reuse `noHybrid`. The decoded-source equality and transported empty-registry equality now have separately accepted kernel evidence.

NP still uses the unchanged original parallel-source decoder and registry. Hybrid ID 0 names vertex 3; false selects occurrence 2 and true selects distinct occurrence 3, both with endpoints `(2,3)`. This agrees with the original request's gamma `P(true/parent1)=1/3`. No parent endpoint collapsing or old LAW gamma convention appears.

## Accepted evidence and exact limits

The [acceptance capture](../../reuse/NAMED-CALENDAR-SOURCE-ADMISSION-ACCEPTANCE-20261010T173920Z.json), SHA256 `f858bb131187eceeaf8abf3f646a9c1c81bf6ae2482678baf2cfce7679a7cb84`, and [kernel certificate](../../lean/NAMED-CALENDAR-SOURCE-ADMISSION-CERTIFICATE.json), SHA256 `7b44694b907655afd9fa7554234e0ce25e84b0bc3440167727a627e9132da1c3`, bind the repaired source and report a complete 172-module audit with 5301 declarations, 3089 theorems, zero owned/nonstandard axioms and no missing modules. The accepted result SHA256 is `527c24fadc67e0e1adb6cf0847d573d71e1bc97857ac6bfd943ae1034c4fe637`. I rehashed these text records and checked their source/target bindings and counts. Root handles the independent full compiler/import evidence review; this source review does not claim to repeat that audit.

The preserved [repair capture](../../reuse/NAMED-CALENDAR-SOURCE-ADMISSION-TRANSPORT-REPAIR-20261010T173648Z.json), SHA256 `aecc8514c4c2d6e32f8efef834a1ff5963e5626ec379a516869f08cddc238e97`, and [failed result](../../lean/NAMED-CALENDAR-SOURCE-ADMISSION-51E5-RESULT.json), SHA256 `f83be85f73306d19b78184375c088e1f2e6fafe8bca07d6cf77273bc5b6d3e1a`, remain separate. Their existence is not an acceptance defect in the repaired proof.

The original [input capture](../evidence/named-calendar-source-input-capture-1/RECEIPT.json), SHA256 `025bf9aa31ff8762382e2144144bf47fe9620a0796531a764b432a138f8b08c4`, and [code projection](../evidence/named-calendar-source-input-capture-1/CODE-INPUTS.json), SHA256 `1a1fd1475f6ff40dd1094c9c842a41a1086e2cdb33a5d888f69daf839c903431`, still bind exactly `twoTipCalendar`, `serialNegativeTips` and `parallelCommonCalendar` to these two literal graphs. This is external finite input provenance, not a theorem about arbitrary native JSON, generic validators or arbitrary source codes.

The accepted conclusion is **fixed named graph/registry structural binding only**. Full labelled-planarity/cofacial validation, general parser/validator refinement, source census coverage and generic source admission remain separate. Calendar/sample/physical-law/normalized-dictionary and timed-readout transport are not inferred from this adapter. Existing Rust core/frontend/runtime pins and generic application admission/scientific flags remain unchanged.
