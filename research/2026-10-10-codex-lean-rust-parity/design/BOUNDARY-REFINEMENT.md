# Conditional original source boundary: internal extraction contract

Contributor: Codex solver_design role, 10 October 2026. Status: concrete contract for the parent-authorized internal port; implementation and fixture acceptance are separate. No public RC1 operation, binary promotion or source-admission claim is added. The full G1–G7 solver remains the objective.

## Target and carrier

The target is the actual [SourceBoundaryKernels.boundaryKernel](../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceBoundaryKernels.lean), with polynomial rows supplied by [G7OriginalBoundaryPolynomial](../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7OriginalBoundaryPolynomial.lean). Reuse the exact providers and already proved source projectivity/ordered and unranked row independence in the [Rust source inventory](../rust/notes/BOUNDARY-REFINEMENT-PROVIDERS-20261010T1157Z.md). Their mathematical conclusions are not new native extraction claims.

Use the unchanged `source_population::Context` and canonical live-only `Snapshot`. Its structural graph validator implements the finite RootedBinary conditions; the native validator-to-typed constructor theorem remains open. The internal context bounds remain four copies, original graph registries at most32 each and existing age/rate/coin bank dimension at most32. These are operational restrictions, not a bound on an original scientific source. No additional cut-child or planarity premise is needed for these actual boundary bodies.

Every live owner belongs to its disjoint ordered tree fibre, every copy names one live ancestor, source-descendant validity uses literal original locations and sample taxa, dead fields are `None`, and the register has one bit per original vertex. Nonmonotone injective `global_labels` embeddings remain allowed. A valid conditional state need not be reachable from natural singleton initialization.

The internal API is:

```text
boundary_row(context, entering_snapshot, action, limits)
  -> Result<Table(full ordered selected rows with literal witnesses, work),
            InvalidInput | Unknown(exceeded_limit, required, cap)>

Action = Exit(original_edge)
       | Ordinary(original_edge)
       | Root
       | Common(original_hybrid_id)
       | Independent(original_hybrid_id)
```

Do not accept an independent caller-supplied parent pair. Resolve hybrid IDs through the same original registry. The pair must consist of distinct genuine original edge occurrences, both targeting its actual hybrid site, in the supplied registry order. This instantiates [OriginalHybridParents](../../2026-10-04-dot-complete-original-g1-1549z/src/G2LiveLineageRouting.lean)'s `isHybrid`, `target0`, `target1` and `different` fields. Parallel endpoints remain legal and do not merge edge occurrences. `Ordinary(e)` requires indegree of `target(e)` exactly1. `Root` names the context's original root. Reject invalid input before publishing any row.

## Literal operation and polynomial bank

| Action | Location change for an affected live owner | Weight |
|---|---|---|
| Exit(e) | `E:e → V:source(e)` | 1 |
| Ordinary(e) | `V:target(e) → E:e` | 1 |
| Root | `V:root → A:root` | 1 |
| Common(h) | Every owner at `V:site(h)` goes to parent0 when the entering site bit is false, and parent1 when true | 1, conditional on that fixed register |
| Independent(h) | Each current owner at the site draws one fresh bit, false→parent0 and true→parent1 | `gamma_h^true_count * (1-gamma_h)^false_count` |

All other owners remain in their exact original population. Every action preserves live IDs, ancestor map, complete ordered genealogy and **every entering register bit**. The primitive does not append a timed event history to the finite snapshot or secretly reinitialize natural coins. At an empty site the independent row is identity with weight1.

Use one symbolic coordinate per original hybrid in ascending hybrid ID order, named `ORIGINAL_GAMMA:hid` in the internal probe. The dimension is the full registry size even when an action uses no coin. Normalize sparse exact rational coefficients by lexicographic full exponent vector, delete exact zeros and use canonical `p/q`. No numeric gamma input is needed for this symbolic operation. Source evaluation later uses one shared original gamma bank. It is probability of true/parent1, as proved by the initialization/pulse providers. Frozen LAW-v1 instead uses probability of supplied occurrence0; a matching-order composition requires the [explicit complement transport](SOURCE-PARENT-ORIENTATION.md). COMMON's conditional row must never be replaced by LAW's marginal two-route mixture.

Generate the current site owners in ascending local Copy ID order; generate their assignments lexicographically, false before true. For each assignment change each complete owner fibre together, validate its canonical destination, and push it forward to `source_epoch::SelectedView`: complete ordered ancestor tree and original location for every outer local copy, plus the full register. Sum equal full selected keys and retain one validated literal destination witness. This is a new executable enumeration convention; original Finset order is not a wire order.

## Operational limits

Default limits are16 raw assignments,16 output destinations and128 raw polynomial term contributions. For a deterministic action, or INDEPENDENT with no current site owner, each requirement is1. For an independent site with `k>0` current owners, the assignment and destination requirements are `2^k`. Distinct original parents and disjoint owner fibres make all those full selected destinations distinct. Each assignment's compact weight is expanded with the exact binomial formula for `(1-gamma)^false_count`; it contributes `false_count+1` normalized binomial monomials before cross-assignment collection. The total term requirement is `2^k + k*2^(k-1)` (48 for four site owners).

Precheck **assignment, destination, then term** requirements, in that order, before assignment generation or polynomial expansion. Record `owners`, `assignments`, `destinations`, `term_contributions`; `owners` counts affected live owners for every action (the named edge for Exit, target node for Ordinary, original root for Root, hybrid site for either pulse). Deterministic requirements remain1 even with no affected owner. Check again that produced rows/terms satisfy the predicted identities; an internal mismatch is an execution error, not UNKNOWN or a source answer. Exact arbitrary-precision arithmetic has no hidden derived rational cap in this component. External process limits are recorded separately. UNKNOWN carries no partial table. Limits with exact required counts accept; one-below and zero limits return the first named exceeded requirement.

This contract covers one conditional boundary row. A future supplied finite word embeds epoch variables into `(interval_slot × Option E) ⊕ original_hybrid`, with one shared gamma bank and a common physical rate/duration evaluation. Its slot count, variable dimension, word length and cumulative row/term budgets require a separate contract; neither the current32-dimensional context bound nor RC1 LAW limits silently authorize an unbounded expanded word.

At an actual calendar date, reuse [boundaryOperations](../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCalendarCompiler.lean): all outgoing edge exits precede all original node entries. A new ascending edge/vertex ID ordering needs its finite-set permutation/commutation correspondence. In particular an exit cannot be exchanged with its own source-node entry. No generated-calendar admission or forced-ID actuator is added by this primitive.

## Fixture schema and acceptance

The fixed internal probe schema is `source_boundary_probe_v1`, with `fixture`, unchanged full `context`/`start`, `action`, `variables`, `rows`, `work`, and `source_admission_verified:false`. Context and snapshot records use the existing population/epoch private JSON conventions. Variables are `["ORIGINAL_GAMMA",hid]`; every row has the existing full ordered `view`, a canonical literal `witness`, and sorted `coefficients` pairs `[full_exponent_vector,"p/q"]`. Action tags are `["EXIT",e]`, `["ORDINARY",e]`, `["ROOT"]`, `["COMMON",hid]`, `["INDEPENDENT",hid]`. Outer local labels appear in the ordered views; global embeddings are only used by a separate declared unranked reader. Exact JSON validation retains multiplicities and rejects duplicate/nonfinite fields.

Use the existing two-tip source N2 and parallel-occurrence source NP from the epoch fixtures. Freeze12 valid boundary cases: `emptyCommon`, `emptyIndependent`, `commonFalse`, `commonTrue`, `independentTwo`, `carriedOwnerOutside`, `noOwnerAtSite`, `parallelExit`, `ordinaryEntry`, `rootEntry`, `registerRepeat`, `permutedIndependent`. Their exact JSON contexts will be supplied by the independent design oracle before a candidate build. Unit controls additionally cover wrong/duplicate parent registries, wrong degree/targets/IDs, all zero limits and exact/one-below limits. A composition control checks both parallel exits followed by ordinary entry at V2, and rejects the reversed entry/exits order; root entry followed by an ancestral epoch reuses the already tested epoch carrier. A later second-hybrid fixture should check distinct register-site/variable indexing before extending word compilation.

The independent oracle enumerates coins on the **whole Copy carrier**, then marginalizes all bits not used by current site owners. It compares every literal/full selected polynomial, source-valid witness, genealogy/ancestor preservation, full register and original population; mass and unranked readout alone are insufficient. This deliberately differs from the native current-owner enumeration. Original gamma1/3 controls require false/true weights2/3 and1/3; two current owners give FF,FT,TF,TT weights4/9,2/9,2/9,1/9. Natural mixing of the two fixed COMMON rows agrees with LAW only after `G=2/3`; direct `G=1/3` binding must fail. A carried three-copy tree gets one coin, not three.

Acceptance requires a separately attributed typed Lean finite-action baseline exercised against the actual inherited pulse/deterministic boundary providers, or a proved executable refinement of them, in addition to the independent oracle and Rust checks. Source PMFs and `nodePolynomial` have noncomputable definitions; their existence alone is not a serializer. The existing original8-population and internal9-epoch evidence is reused without claiming it already covers boundaries. Candidate builds stay separate from accepted public runtime237e; a library/probe acceptance adds no public endpoint or scientific admission.
