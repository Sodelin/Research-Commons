# Original admission predicates and the supplied calendar

Contributor: Codex Rust implementation role, 10 October 2026, 17:20 UTC.
Status: sourced static comparison, with one explicitly hand-derived count argument. No compiler, native execution, runtime edits or admission-flag changes.

This expands the [16:13 readiness review](ORIGINAL-SOURCE-ADMISSION-READINESS-20261010T1613Z.md). The existing finite-code decoder is the smallest reusable structural consumer. The current Rust calendar already checks its binary/rooted/LSA and complete-registry conditions algorithmically. A general binding of those exact native arrays and validator results to the typed code is still missing. The existing Lean provider decides cut-child bridges; the documented outer-labelled planarity/cofacial-taxon test is absent. There is consequently no current generic consumer that warrants `source_admission_verified: true` for `calendar-law`.

## Exact code and predicates

[G7OriginalFiniteEncoding.lean](../../../2026-10-09-dot-g7-original-registry-admission-1908z/sources/G7OriginalFiniteEncoding.lean) defines `Code X ID` with separate source/target coordinates for every original edge occurrence, a root, the original taxon map, the hybrid-site map and an `ID → Bool → edge` parent map. For `X = Fin l` and `ID = Fin h`, its vertex/edge carriers have sizes `2*l + 2*h - 1` and `2*l + 3*h - 2`. Parallel endpoints retain different edge coordinates; taxon and hybrid IDs retain the supplied array order.

The following comparison is against the actual bodies of [G7OriginalAdmission.lean](../../../2026-10-09-dot-g7-original-registry-admission-1908z/sources/G7OriginalAdmission.lean), lines 55 and 113, and [natural_cell.rs](../src/natural_cell.rs), lines 73–124. A matching static algorithm is not a machine-checked native refinement theorem.

| Typed predicate field | Existing Rust check | Remaining binding |
| --- | --- | --- |
| `BinaryValid`: injective taxon leaf map | `leaf_set` rejects repeated leaf vertices | Preserve the original taxon-index map in the exact `Code`. |
| At least two taxa | `SOURCE_SIZE` requires `leaves.len() >= 2` | Cast the actual array length to the finite carrier cardinality. |
| Root indegree 0, outdegree 2 | `ROOT_DEGREES` | Degree counting over original occurrence IDs. |
| Every declared leaf has indegree 1, outdegree 0 | `LEAF_DEGREES` | Same occurrence-counting correspondence. |
| Every other vertex has degrees `(1,2)` or `(2,1)` | `INTERNAL_DEGREES` | Complete bounded vertex enumeration. |
| Directed acyclicity | Kahn traversal must remove every vertex | Relate traversal success to absence of positive `TransGen DStep` cycles. |
| Root reaches every vertex | `reachable(None)` must visit every vertex | Relate directed DFS to reflexive `DReach`; root reaches itself. |
| Any vertex dominating all taxon leaves equals root | For each nonroot vertex, `reachable(Some(vertex))` must still reach at least one taxon leaf | Relate blocked-vertex DFS to the exact `AvoidReach` definition, including endpoint exclusion. |
| `RegistryValid`: hybrid-site map injective | `hybrid_set` rejects repeated sites | Preserve supplied hybrid indices. |
| Every registry site is an actual degree-`(2,1)` hybrid | `HYBRID_REGISTRY` | Exact degree predicate correspondence. |
| Every actual hybrid has an ID | `INTERNAL_DEGREES` requires the hybrid degree flag to equal registry membership | The complete registry is a bijection, rather than a chosen subset. |
| Both parent occurrences target that site | `HYBRID_REGISTRY` checks the two indexed targets | Preserve the false/true incoming order. |
| False and true parents are distinct edge occurrences | `incoming[0] != incoming[1]` | Parallel endpoints are allowed; occurrence IDs cannot be collapsed. |

The code carrier is not a modulo conversion of arbitrary native indices. A hand-derived count check from the successful degree/registry conditions gives the required sizes: if `t` is the number of ordinary internal nonroot vertices, counting edges at both ends yields `2 + 2*t + h = l + t + 2*h`, hence `t = l+h-2`, `v = 2*l+2*h-1` and `e = 2*l+3*h-2`. The existing `original_registry_sizes` theorem supplies this census for an already typed `RootedBinary`; using native arrays needs a corresponding bounded-carrier/count witness. No accepted native-to-code witness is asserted here.

## Reuse without another graph engine

`decidableBinaryValid`, `decidableRegistryValid` and `decidableCutChild` are executable instances on one supplied finite `Code`. They do not require enumerating `allCodes`. [G7FiniteReachability.lean](../../../2026-10-09-dot-g7-original-registry-admission-1908z/sources/G7FiniteReachability.lean) supplies `decideReach`, whose saturation bound is the actual finite vertex count and whose result is proved equivalent to reflexive transitive reachability.

The missing cut-child check is exactly `∀ f, IsHybrid(source f) → IsBridge f`. `decidableBridge` decides **undirected** reachability between the endpoints after deleting only that original edge occurrence. The Rust `reachable` helper is directed, begins at the root and optionally deletes a vertex; it must not be reused unchanged as an edge-bridge check. The accepted Lean edge-deletion predicate/decision is already the intended provider.

With typed `hb : BinaryValid c` and `hr : RegistryValid c`, the existing APIs are:

1. `sourceOfValid c hb`, which constructs the actual inherited `RootedBinary`.
2. `decodedIDs c hb hr`, an executable bijection onto all actual hybrid vertices.
3. `decodedRegistry c hb hr`, the inherited `OriginalParentRegistry`.
4. `decoded_parent_exact`, preserving each original ID and false/true parent occurrence.

The code-to-source direction avoids the abstract `encode` function's noncomputable numbering equivalences. A consumer still needs exact request/parser-to-code correspondence and authenticated binding of the resulting source/registry to the calendar law. A successful Rust Boolean does not itself supply `hb` or `hr`.

The original [README](../../../2026-10-09-dot-g7-original-registry-admission-1908z/README.md) and source explicitly say that `registeredBinaryCutChildCodes` is a **superset** of full original G7 admission because outer-labelled planarity/cofacial taxa are not tested. No eligible complete generic planarity/cofacial routine was found in the inspected admission provider or existing practical-solver graph utilities. This inventory does not substitute all-vertices outerplanarity, level-one constraints or an invented graph restriction. [CURRENT-SCOPE](../../../2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md) separately preserves the accepted nonplanar G6 child-bridge extension: that G6 use must not acquire an unnecessary G7 planarity filter.

## Physical and sample premises already checked

[Context::validate](../src/source_population.rs), lines 105–113, bounds graph counts and shared bank dimension before `Source::validate` allocates its graph arrays. It also limits this executable Copy carrier to four, checks every sampled original taxon ID, and requires equal sample/global-label lengths and an injective global-label embedding. Repeated sampling of a taxon and unsampled declared taxa are allowed. These are operational/representation bounds, not new mathematical source impossibility statements.

[source_calendar.rs](../src/source_calendar.rs), lines 103–142, then checks:

| Supplied-calendar field | Actual inherited typed target | Remaining consumer premise |
| --- | --- | --- |
| One canonical rational age per original vertex; every edge has strictly older source | `Calendar.age` and `Calendar.edge_older` in [G5CalendarRoutes.lean](../../../2026-10-04-dot-complete-original-g1-1549z/src/G5CalendarRoutes.lean) | Exact rational-to-real cast on the same decoded graph. Generic Calendar does not require leaf age zero, equal tip ages or nonnegative absolute ages. |
| One positive inverse rate per original edge, plus one ancestral coordinate | `PositivePairRates` in [NativePairClockLaw.lean](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/NativePairClockLaw.lean) | Set `rate = 1/u`, prove positivity, retain each original occurrence and the single ancestral population. |
| One interior original gamma per hybrid | `HybridProbabilities` in [NativeIndependentPairMixture.lean](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/NativeIndependentPairMixture.lean) | Transport through the exact hybrid bijection. Gamma is `P(true/parent1)`, not the old LAW-v1 incoming-zero coordinate. |
| One fixed Boolean COMMON mode per registry hybrid | Original fixed mode function | Preserve ID order and once-only natural register draw; no per-visit mechanism change. |
| Nonempty Copy for `ANCESTRAL_COMPLETE` | Existing actual ancestral-completion nonempty premise | Root support and completion/word/agenda correspondence remain separate from graph admission. |

The producer retains one bank across slots via the exact symbolic substitution `X(slot,e) = exp(-duration(slot)/u[e])`. Its sorted-date, exit-before-entry agenda is independently checked, but general native encoding, normalized polynomial dictionaries and the original chronological phase/word correspondence still require their specific typed bindings. Graph admission does not prove those law identities or timed readouts. The contemporaneous-tip `NaturalCellAffineCompiler.BankConditions` wrapper is therefore not the generic calendar parameter constructor.

## Frozen source identities and acceptance limits

| File | SHA256 |
| --- | --- |
| `G7OriginalAdmission.lean` | `16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c` |
| `G7OriginalFiniteEncoding.lean` | `30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078` |
| `G7FiniteReachability.lean` | `25673c4d0a0ec0891ff204ff79c018d8e9ad1971962183e0a7332b6d709d2a35` |
| `natural_cell.rs` | `774a26a70f99bdc760fa15835267c6fc0753bb2db0419844d65895b29f1ecf9e` |
| `source_population.rs` | `6afebffe8bb727a1c92bd113d479f01f0b2877bbf527c79866247805bc21da7c` |
| `source_calendar.rs` | `d993e8808a4f227001a393db123b1be00f70a5c940388586d909772bbb3ff3a8` |
| `calendar-cli/src/request.rs` | `1bb2b9569f47c101705e63b011cc4c8b4a58f6e8702bb404813d7659702f462a` |
| `G5CalendarRoutes.lean` | `db0e9421d59009e4119ac42e7e86517ada50f5007a314fd430f4b0937f6c80fd` |
| `NativePairClockLaw.lean` | `470738f7397f640a76374f791c485d757d1e2ac38769a11f05d0abc03c8aa9ae` |
| `NativeIndependentPairMixture.lean` | `4e1107890e0e36967898c06251a1a7ed3305721860534b902a87b04d434e4c31` |

The preserved [98-explicit-declaration audit](../../../2026-10-09-dot-g7-original-registry-admission-1908z/evidence/DECLARATION-AXIOM-AUDIT.json), SHA256 `f60960008fe9b30055bf8fde02e7863413af74ea6fb4cbeab7fd597020b4cc02`, covers the provider's stated original review scope; it is not 98 modules or a new execution. This note reread source and rehashed current files only. The completed original G1/G2/G5 theorem status is unchanged. Full source census coverage, actual observation/readout admission, empirical confidence and G7 policy assembly remain distinct from this structural decoder.

Next compatible integration is an exact supplied-code consumer of the existing decidable predicates and decoder, with native/parser representation and positive-bank cast bindings. Full G7 source admission additionally needs the absent original labelled-planarity/cofacial component. No new engine or admission promotion is authorized by this inventory.
