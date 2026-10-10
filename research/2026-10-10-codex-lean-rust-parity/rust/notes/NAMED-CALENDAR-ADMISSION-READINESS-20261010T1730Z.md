# Named calendar sources already have exact admission codes

Contributor: Codex Rust implementation role, 10 October 2026, 17:30 UTC.
Status: sourced read-only feasibility review and input capture; proposed proof consumer, not a new checked theorem. No native, Lean, compiler or git invocation; no accepted source/runtime/map edits.

Both original graphs behind the three frozen completed-calendar inputs already have exact `G7OriginalAdmission` code literals. The parallel source is already defined by the accepted decoder. The two-tip literal is present in an older coefficient-smoke candidate, but that package has a preserved incomplete result; it must not be imported as if it were accepted. A tiny proof-only consumer can reuse its exact literal body under the already accepted admission and two-tip-source imports.

The fresh [input/source capture](../evidence/named-calendar-source-input-capture-1/RECEIPT.json), SHA256 `025bf9aa31ff8762382e2144144bf47fe9620a0796531a764b432a138f8b08c4`, preserves 11 original source bodies and three unchanged request files. [CODE-INPUTS.json](../evidence/named-calendar-source-input-capture-1/CODE-INPUTS.json), SHA256 `1a1fd1475f6ff40dd1094c9c842a41a1086e2cdb33a5d888f69daf839c903431`, contains only their original source/target/root/taxon/hybrid/parent input projections. No tables, computed admission answers or compiled executables are included.

## Exact input correspondence

| Original source | Code input, in original occurrence/label order | Completed-calendar input |
| --- | --- | --- |
| `N2` | `Code (Fin 2) (Fin 0)`; vertices 3, edges 2; source `[0,0]`, target `[1,2]`, root 0, taxon leaves `[1,2]`; no hybrid sites or parent maps | `twoTipCalendar` and `serialNegativeTips` |
| `NP` | `Code (Fin 2) (Fin 1)`; vertices 5, edges 5; source `[0,0,2,2,3]`, target `[1,2,3,3,4]`, root 0, taxon leaves `[1,4]`, hybrid site `[3]`; false parent `[2]`, true parent `[3]` | `parallelCommonCalendar` |

The two incoming parallel occurrences are different original edge IDs 2 and 3, although their endpoint pairs coincide. Original gamma is `P(true/parent1) = 1/3` for the parallel calendar. The two N2 requests have the same structural graph but different sample maps and ages, including unequal negative tip ages in `serialNegativeTips`; structural binding does not replace those separate calendar/sample premises.

All three request bytes exactly match the original input-only freeze:

| Fixture | Bytes | SHA256 |
| --- | --- | --- |
| `twoTipCalendar` | 1169 | `42eb6a95c160825cb19da7945bd025cb2e31e8a2d43aaab4fe1c87a0d4c64dbf` |
| `serialNegativeTips` | 1189 | `435c41549a96c529ce7545480d2f52bef9e2280ce01b64523e5f0a62944a11db` |
| `parallelCommonCalendar` | 1434 | `f4c9784938ede6f83c294b037018dac38392e80b91d33d2544b5c9660f334076` |

Their original [inventory](../../design/evidence/calendar-original-input-freeze-1/INVENTORY.json) SHA256 is `4d39a2d825686e135dc727dd9a705320af0c5b54c4c65d7251c28f42ddb5c2ba`. The new capture copies only those request origins, rather than deriving a new fixture or using expected rows.

## Existing named providers

[G7OriginalParallelEpochFixture.lean](../../reuse/sources/G7OriginalParallelEpochFixture.lean), SHA256 `eb5db3412042ce9d991c0eb970c7ddd32ecc88e005ec36610dbd56e281274432`, already supplies:

- `graphCode` with the exact NP arrays above.
- `graphCode_valid`, `graphCode_registryValid` and `graphCode_cutChild`, proved by the existing finite decisions.
- `source := sourceOfValid graphCode graphCode_valid`.
- `registry := decodedRegistry graphCode graphCode_valid graphCode_registryValid` and `ids := decodedIDs ...`.
- `parentOccurrence_exact`, preserving the supplied false/true occurrence map.

`NP` in the completed-calendar fixture is an abbreviation chain through `OriginalWordFixture.NP` and `OriginalBoundaryFixture.NP` to that exact decoded source. No second graph or registry reconstruction is needed. The code also matches `G7AdmissionChecks.parallelBigon` in the old admission package, SHA256 `7834bc20dab2b73af5d397c67cf02eb12f5c1cda89a5a7828eba9f67d91631e3`; the current NP fixture is preferable because it contains kernel theorems and is imported by the accepted completed-calendar closure.

[G7EffectiveCoefficientSmoke.lean](../../reuse/sources/G7EffectiveCoefficientSmoke.lean), SHA256 `7137442eab121c30a486abe70efddbf401135b2a3a9cd0c051232a63ea207ff4`, contains `forkCode` with the exact N2 arrays, plus source-level `fork_valid`/`fork_cut_child` declarations. The package's [result](../../lean/COEFFICIENT-SMOKE-RESULT.json) is `INCOMPLETE_TARGET_FAILURES_PRESERVED`, and the module is absent from the accepted completed-calendar closure. Its literal is a reuse candidate, not a claimed accepted proof import.

The actual `N2` abbreviation chain terminates at [G6TwoTipChartFixture.source](../../reuse/sources/G6TwoTipChartFixture.lean), SHA256 `1d7e4d7509022405182bd8c98e98e59d73d013899b4cecd29d55a854a2972bfb`. That source has exactly the same incidence/root/taxon data, already proved `RootedBinary`, and `noHybrid`. The completed-word fixture's `registry2` is the unique empty-hybrid registry on this source.

The [accepted parallel fixture certificate](../../lean/ORIGINAL-PARALLEL-EPOCH-FIXTURE-CERTIFICATE.json) covers 144/145-module overlapping closures. The [accepted completed-calendar certificate](../../lean/ORIGINAL-CALENDAR-FIXTURE-CERTIFICATE.json), SHA256 `7dfecc253e3d382497b9d67cb5b50c7721744406bdfc5ca49358e1a239dee4d2`, binds the current admission, reachability, N2, NP, epoch, boundary, word and completed-calendar source hashes in its 199/200-module closures. The new capture authenticates that membership and preserves the exact sources; it does not repeat the audits.

## Minimal proof-consumer plan for root review

The proposed module imports accepted `G7OriginalAdmission`, `G6TwoTipChartFixture` and the existing named word fixture. It avoids importing the failed coefficient-smoke package or introducing a graph algorithm.

1. Define the exact two-tip `Code (Fin 2) (Fin 0)` using the existing `forkCode` body, with explicit empty-site/parent functions. Attribute the body and its pinned smoke predecessor.
2. Obtain `BinaryValid` directly from unchanged N2's accepted `RootedBinary` field proofs after reducing the identical graph/root/leaf data. Use `noHybrid` for registry completeness and vacuous cut-child/empty-ID clauses. Reuse advised this smaller route; it avoids recomputing reachability and least-stable facts already proved for N2. The existing finite decisions remain available as an alternative on the exact code. These new consumer proofs remain uncompiled until the sole scheduler checks them.
3. Construct `sourceOfValid`/`decodedRegistry` from those proofs. Prove the decoded source equals unchanged `N2`, preserving source/target/root/taxon functions pointwise. Their data constructors match; unfolding followed by reflexivity/proof irrelevance is the first proposed proof strategy, not an accepted result. If needed, use structure/function extensionality over these same literal fields.
4. Transport the decoded empty registry across that source equality and prove equality to unchanged `registry2`. Use `noHybrid` and function extensionality; no arbitrary parent choice is introduced.
5. State direct equalities for NP's existing `graphCode`, source, registry, IDs and false/true parent map. Its decoded-source definition is already the named NP provider; the new consumer only exposes the relation to the captured original arrays and abbreviation chain.
6. Bind the two literal structural inputs to the three frozen request contexts in a finite fixture theorem or source-field equality list. Keep raw JSON/request SHA authentication in the external capture; this is not a theorem about the generic JSON parser.

The proposed theorem scope is precisely two named finite graph/registry carriers, preserving original occurrence and taxon/hybrid labels. Full original labelled-planarity/cofacial admission, arbitrary native validator/parser refinement, source census coverage and generic source-to-law admission remain open. Structural equality alone does not identify arbitrary native polynomial dictionaries or prove timed readouts. The existing generic calendar-law admission flags stay false.

The source/input capture and this plan precede any new module. Root review and the sole Lean scheduler control subsequent proof checking; no new runtime or native test is needed for these unchanged structural inputs.
