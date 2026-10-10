# Original boundary provider inventory and internal refinement proposal

Contributor: Codex Rust implementation role, 10 October 2026, 11:57 UTC.
Assignment received from root: inspect oldest accepted and current original
boundary/routing providers, coordinate with design and reuse, and preserve this
notes-only contribution. Status: **sourced findings and proposed finite controls**;
no new implementation, Lean compilation, mathematical theorem or runtime
acceptance is claimed. Current Rust sources, builders, adapters and pins stay
frozen at [the epoch inventory](../EPOCH-INVENTORY-20261010T1149Z.json).
The full solver remains in progress under the
[original master statements](../../../2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md)
and [completion standard](../../../../docs/RESEARCH-COMPLETION-STANDARD.md).

The next useful component is the **conditional original finite-code boundary
row**, retaining its entire entering register. It is a consumer of the same
canonical snapshot carrier as [source_epoch](../src/source_epoch.rs), followed
by an explicit full ordered selected-view pushforward. It is not a reuse of
LAW's marginal COMMON two-route mixture inside a fixed-register row. Source
class admission, calendar scheduling, complete observations, source census,
fitting and G3/G4 stopping remain separate.

## Exact inherited semantics

`GProgram.G2.OriginalHybridParents` carries the actual hybrid, both incoming
original edge occurrences, their target proofs and distinctness. Its `parent`
maps false to parent0 and true to parent1. This permits parallel occurrences
with the same endpoints; an endpoint pair is not an edge ID. Current
`Source.hybrids[hid].incoming=[e0,e1]` would be transported to this explicitly
ordered pair, without sorting away the supplied order.

The actual boundaries have the following bodies. Every location test is against
the same original IDs, and all movements apply to a whole current genealogy.

| Operation | Exact source body | Required legal input | Change at an active owner |
|---|---|---|---|
| Exit original e | `exitEdge`, `exitCode`, `.exit e` | Genuine original edge e | `E:e → V:source[e]`; every other location stays |
| Ordinary entry e | `enterEdge`, `ordinaryCode`, `.ordinary e degree` | `inDegree(target[e])=1` | `V:target[e] → E:e`; every other location stays |
| Root entry | `enterRoot`, `rootCode`, `.root` | The same original root | `V:root → A:root`; every other location stays |
| COMMON at h | `commonPulse`, `boundaryKernel (.common H)` | Exact original parent registry | Every current owner at `V:h` uses **the entering `register[h]`** |
| INDEPENDENT at h | `pulse`, `independentPulseKernel` | Exact registry and one same-source gamma for h | Each current owner at `V:h` draws one fresh bit and enters the selected original parent edge |

`AtNode s h` is `{a // a∈s.live ∧ s.location a=.node h}`. A dead original copy,
a copy inside another owner's genealogy, or an owner outside this node is not
another pulse coin. Each copy's location is its ancestor's location. Consequently
already merged copies cannot split, even when their representative is not their
smallest original label. Pulses preserve the ordered genealogy and ancestor map.

**There is no register update in these boundaries.** `transport` changes
locations and appends one named source event, while retaining live roots,
ancestors, genealogy and register. `pulse_register_retained` and
`step_register_retained` prove preservation. The finite original `Code` snapshot
omits source event history and decodes dead fields to inert defaults; canonical
`encodeActual` stores live genealogy/population as `some` and dead fields as
`none`. The existing Rust carrier therefore targets finite-code selected state,
not an unrecorded timed event trace. A future timed readout must reuse the actual
registered path providers separately.

The once-drawn natural register is constructed by `originalRegisterPMF`:
one independent original-site bit per hybrid, nonhybrid slots false. Every
subsequent boundary and epoch keeps that same full register. Arbitrary valid
entered-state fixtures may retain nonhybrid bits or previously carried trees;
that does not prove reachability from natural singleton initialization.

## Parameter orientation that must be transported

The actual probability provider is
`bitMeasure gamma = bernoulliMeasure true false gamma`. The initialization and
node polynomial providers prove true mass gamma and false mass `1−gamma`.
Thus the original shared parameter is **P(parent1)**. The older rational
illustration `SourceLabelledForest.bitWeight p false=p` uses p as false mass;
it must not be mistaken for the actual original unitInterval gamma.

Frozen LAW-v1 instead declares `G=P(incoming occurrence0)` and uses G for the
first supplied occurrence, `1−G` for the second. Its original Python provider
and both native implementations agree on this formal convention. With
wire occurrence0=source parent0 and occurrence1=source parent1, the required
relation is **`G_LAW = 1−gamma_original`**. A parent-order swap is an alternative
only with explicit original registry and register-bit relabelling. These
conventions cannot be equated merely because both name a hybrid coordinate.

The new conditional source-boundary proposal uses the original convention:
one current-owner assignment c has weight
`gamma_h^(#true) * (1−gamma_h)^(#false)`; true routes to incoming1. COMMON has
one deterministic destination with polynomial 1, independent of gamma when the
entering register is fixed. If a literal CHART coin realizes the inherited
`HybridProbabilities` gamma, a later LAW consumer must perform the complement
transport before substituting that coin into its G coordinate.

## Providers to reuse

The primitive G2 source was already checked in the October 1 package; the full
labelled forest was checked on October 2. Both exact source hashes are unchanged
in the accepted October 4 original G1 package and the newest October 10
coefficient recovery. A fresh byte comparison of fourteen oldest/current
provider pairs against
[the delivered coefficient graph](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/latest/coefficients/DEPENDENCY-GRAPH.json)
matched. This is byte/provenance verification, not another kernel compilation.

Reuse these exact conclusions rather than add them to the unresolved list:

- `coalesced_copies_cannot_split`, `pulse_routes_current_ancestor`,
  `pulse_cannot_split_copies`, boundary source-validity and register preservation
  from the original G2/labelled-forest providers.
- `original_pulse_selected_view`, `actual_original_hybrid_pulse_projectivity`
  and `actual_common_pulse_pruning`: current-owner coins transport to whole
  selected blocks, with hidden owners marginalized and the COMMON register kept.
- `actual_population_transport_view`, `exitCode_view`, `ordinaryCode_view`,
  `rootCode_view`, `pulseCode_view`, `independent_pulse_kernel_view_measure` and
  `common_boundary_kernel_view`: derived actual finite source laws.
- `actual_boundary_projection` and `actual_cross_carrier_boundary_law`: full
  ordered selected-row independence and full/small carrier agreement, preserving
  original populations/registers.
- `G1UnrankedActualBoundary.actual_unranked_boundary_row_independent`: the
  source-side unranked boundary lumpability already covers all five operations.
  Native encoding, label/normal-form and coefficient correspondence remain gaps.
- `actual_source_program_projection`, `compiled_original_program_projection`,
  `actual_calendar_tail_support` and
  `initialized_original_calendar_ancestral_support`: source program composition
  and physical initialized calendar support are existing results.
- `actual_natural_complete_timed_all_panel_projectivity` and
  `actual_controlled_complete_timed_all_panel_projectivity`: the later actual
  timed, naturally registered and original-ID controlled source endpoints. The
  October 10 current G2 certificate supplies their reconstructed source scope;
  it does not certify generated executable runtime companions.

The newer `G7OriginalBoundaryPolynomial.pulsePolynomial` explicitly sums
current-owner assignments; `nodePolynomial` chooses deterministic COMMON or
this INDEPENDENT row. `G7OriginalInitializationPolynomial.initialPolynomial`
draws the register once, and `G7SymbolicProgramPolynomial` composes the supplied
original-ID word. Their word bank is `(J×Option E)⊕Hybrid N`: every interval slot
uses `exp(−pairRate(r,i)*dur[j])` with the **same** original positive rate bank;
every use of a hybrid uses the same original gamma. The older
`SelectedKernelPolynomial.epochTable` uses `Classical.choose` and is not an
already extracted native table. Source existence and computable extraction
remain distinct.

`G7GlobalOwnerCoins.independent_pulse_fixed_carrier` proves that one may enumerate
bits on the whole Copy carrier and marginalize unused bits. `G7NodeActions`
gives actual fixed-carrier destinations, register preservation, canonical
output and distinct-node commutation. `G7BoundaryRelabelling.boundary_kernel`
transports all actual boundary laws through vertex/edge bijections. These newer
source bodies are inventoried below; the whole-edge candidate's recovered graph
is not an accepted full extraction chain merely because its dependencies exist.
In particular `G7OriginalEdgeGathering` is retained as a failed/incomplete
candidate, not as a proved permission to commute every exposure past boundaries.

For the repaired coefficient chain, the current
[118-module kernel certificate](../../lean/COEFFICIENT-RECOVERY-CERTIFICATE.json)
also records the separately accepted 119-module explicit audit; the codegen
smoke remains unaccepted. No new full original boundary evaluator was executed
by this inventory.

## Required native carrier and composition

Proposed next internal API, pending design/root review:
`boundary_row(Context, canonical Snapshot, OriginalOperation, shared gamma bank,
limits)` returning a full exact row or UNKNOWN with no partial row. Mode is
attached to its original hybrid action; the source compiler permits different
modes at different hybrids. No public endpoint or arbitrary admission bit is
proposed.

The carrier should retain the current four-copy/source graph bounds and original
vertex/edge/taxon/hybrid occurrence registries. Every live representative belongs
to its own disjoint ordered genealogy leaf fibre; every copy has exactly one
live ancestor; original samples descend from that ancestor's original location.
The global label embedding is injective but need not be monotone. Dead
genealogy/population remain none. Every register has exactly one bit per original
vertex, and its complete value is preserved. Ordinary entry checks its degree
premise; hybrid entries check the exact registry's two distinct incoming
occurrences and actual hybrid target. RootPopulation uses the original root.

Generate INDEPENDENT assignments in ascending current-owner ID order, false
before true; there are at most `2^4` raw assignments. COMMON, exit, ordinary and
root have one destination. Keep a canonical literal destination witness while
summing equal full ordered selected-view keys. Check raw assignment count and
expanded term-product requirements before generation, and cumulative product
budgets before word multiplication; do not normalize away a failed budget.
Exact limits and test schema remain proposed until reviewed by design.

For one row of `source_epoch`, boundary composition takes its actual snapshot
witness, applies the original action, validates its canonical destination and
maps it back to the full selected key. The inherited ordered boundary
representative-independence theorem is the semantic reason a selected row may
keep one admitted witness; a Rust hash or finite fixture alone is not that proof.
The same common entering register must serve every factor. Population boundaries
do not merge trees; subsequent epochs merge only owners then sharing a genuine
edge/ancestral population. Node owners stay exterior during an epoch.

For a supplied finite word, embed `source_epoch`'s edge-plus-ancestral bank into
each original interval slot, and boundary gamma variables into the shared
hybrid bank. Slot survivals are formal coordinates with a common physical
evaluation, not independently chosen calendars or per-row rates. Repeated uses
of the same slot/gamma share one variable. Its prospective dimension/resource
cap must be declared independently of accepted public RC1 caps. Actual generated
calendar admission and infinite ancestral completion remain later consumers.

At one calendar date, the actual `boundaryOperations` performs **all outgoing
edge exits first, then original node entries**. Distinct-node entry actions may
commute under their proved premises; an exit cannot generally cross its own
node entry. Use original edge IDs and vertex IDs for any new canonical ordering,
and prove it agrees with the inherited finite-set enumeration rather than claim
the old Finset has that byte order.

The inherited legal fixed-ID forcing mask is a later explicit action extension:
a forced original hybrid compiles to INDEPENDENT gamma=0/1, routes every current
owner to the selected original parent and retains the natural initial register
mixture. It does not overwrite registers, refit the natural gamma bank, or grant
a per-copy actuator. No forcing input is added to frozen LAW-v1 by this proposal.

## Proposed finite fixtures and independent checks

These are proposed controls, not executed acceptance. `N2` is the already used
two-tip source: root0, edges0:(0→1),1:(0→2), taxa leaves[1,2]. `NP` is the existing
parallel source: root0, edges0:(0→1),1:(0→2),2:(2→3),3:(2→3),4:(3→4), leaves[1,4],
hybrid0 at vertex3, parent order[2,3]. Each entering snapshot must independently
pass the existing canonical/source-descendant invariants.

| Fixture | Entering state/action | Required exact result |
|---|---|---|
| EmptyHybrid | NP, no copies, pulse hybrid0 in both modes | Identity, coefficient1, unchanged full register; no ghost coin or partial row |
| CommonFalse / CommonTrue | NP, two singleton owners at V3, register3 false/true | One destination: both on E2/E3 respectively; polynomial1; every register unchanged |
| IndependentTwo | Same two owners, original gamma1/3 | Four distinct destination assignments with weights4/9,2/9,2/9,1/9 for FF,FT,TF,TT |
| CarriedOwnerOutside | NP, copies0,1,2 sample taxon1 share representative2/tree((0,1),2) at V3; copy3 sample taxon0 at V1 | Two outputs with weights1−gamma,gamma; first three always move together; outside owner and complete tree/register untouched |
| NoOwnerAtSite | NP, owners at E2 and V1, pulse V3 | Exact identity even though copies exist; other original populations unchanged |
| ParallelExit | NP, owners at E2,E3,V1, exit edge2 | Only E2 moves to V2; E3 occurrence remains distinct; second exit3 then moves its own owner |
| OrdinaryThenExit | N2, owners at V1,V2, ordinary edge0 then exit0 | V1→E0→V0; V2 unchanged; no genealogy/ancestor/register changes |
| RootThenEpoch | N2, two owners at V0, root entry then ancestral epoch | Both move to A0, then exact ordered half-rate population coefficients; ancestral bank retained |
| InvalidRegistryOrDegree | Duplicate parents[2,2], wrong targets/site, out-of-range IDs, or ordinary edge2 into indegree2 hybrid | Refuse before producing a row; no fake source-admission result |
| RegisterRepeat | NP, first pulse fixed COMMON, retain another owner outside site; compare changed unrelated bits and another hybrid in a later serial fixture | Only the named original stored bit controls COMMON; full registers persist across boundaries/epochs; no redraw |
| OriginalGammaToLaw | Asymmetric original gamma1/3, same supplied parallel parent order | Natural original parent0 mass2/3, parent1 mass1/3 equals frozen LAW only after G=2/3; a direct G=1/3 binding must fail the comparison |
| ExitBeforeEntry | NP, owners on E2 and E3, exits2/3 then ordinary entry at V2 | Both reach V2 then E1; reversing the node entry and exits leaves them at V2 and must not be silently identified |

Additional controls should cover nonmonotone global embeddings, a current owner
whose representative lies outside a selected-copy panel, two different hybrid
IDs/register sites, forced false/true endpoints under the existing original
mask contract, and exact budget acceptance/one-below refusal. For a selected
panel that omits the owner ID, compare the induced whole-block law through the
existing cross-carrier transport, not a newly re-coined selected original tip.

The independent mathematical oracle can enumerate finite current-owner bit
assignments directly with Fraction weights and literal original parent targets,
checking all full ordered view coefficients, destination range witnesses,
genealogy/ancestor preservation, complete registers and populations. Full-view
or literal destination comparison precedes a separate unranked readout.
In parallel, a computable Lean finite-action derivative must be connected to
the original `pulsePolynomial`/`boundaryKernel` semantics and exercised on these
typed fixtures; the providers' noncomputable PMF/choice definitions do not by
themselves promise a runnable serializer.

## Actual verification and next action

This role read the named original bodies, current polynomial consumers and
leading G2 verification scope, rehashed the provider bytes and checked the
oldest/current coefficient-graph matches. It coordinated directly with design
and reuse. No Rust or Lean compiler, git command, protocol mutation, binary
replacement, pin update or new source-admission claim was made for this note.
The source registry below records exact identities rather than a build proof.

Next action: design reviews the original conditional boundary row convention,
including gamma orientation and register lifetime, then aligns a computable
typed finite-action baseline with the agreed fixture contexts. Whole-epoch
support-selected/range/normalization proofs continue in their existing lanes.
Only after this contract is concrete and reviewed should a separate internal
Rust module or candidate build change. The frozen accepted public237e runtime
and separate2d3e epoch candidate retain their prior evidence scopes.

## Exact source registry

The following table is generated from the actual files read above. Module names
starting `UnifiedLean.Source` resolve to their relative path under the linked
October 4 `src` directory. For the fourteen current coefficient providers, the
latest recovery graph and `source-store/<SHA>.lean` have matching source bytes.
The registry distinguishes later polynomial/timed/whole-edge consumers instead
of silently replacing the oldest accepted providers.


| Provider | Source SHA256 | Definitions or scope |
|---|---|---|
| [G2LiveLineageRouting](../../../2026-10-04-dot-complete-original-g1-1549z/src/G2LiveLineageRouting.lean) | `bf33f6be93e61960aa637df34d1197316669d6f2ddde6d743ac405a010cb05af` | OriginalHybridParents,parent,coalesced_copies_cannot_split |
| [SourceLabelledForest](../../../2026-10-04-dot-complete-original-g1-1549z/src/SourceLabelledForest.lean) | `d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d` | transport,exitEdge,enterEdge,enterRoot,AtNode,pulse,commonPulse,SourceValid |
| [UnifiedLean.Source.NativeParentRouting](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/NativeParentRouting.lean) | `300d7216193e945ca26161535c1bc2ba75a128fe5c075b6a3567bbda66bfe0b6` | OriginalParentRegistry,registry_parent_target,compiledRoute_source_spec |
| [UnifiedLean.Source.SourceForestPulseTransport](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceForestPulseTransport.lean) | `8e1a3d62afab25247dd3a281d30f7dc20db1949ea1b589c2d77980b3b48874f1` | visibleOwnerEquiv,projectedPulse,original_pulse_selected_view |
| [UnifiedLean.Source.SourceForestPulseMeasure](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceForestPulseMeasure.lean) | `04a3a1c1f027903e62b77f966639c80da77aaa776871a0d9bd0657eac35b9e4f` | bitMeasure,independentCoinMeasure,actual_original_hybrid_pulse_projectivity |
| [UnifiedLean.Source.SourceForestCommonPulse](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceForestCommonPulse.lean) | `cac1082f66a84b943dbc8ba9f2e8082ce12bbb42a4b1503e31722597b0faa138` | selectedCommonPulse,actual_common_pulse_pruning |
| [UnifiedLean.Source.SourceBoundaryKernels](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceBoundaryKernels.lean) | `994b25e798e39889a56084b267c3e896580cd21e902764c3c6922d9bfdd6070d` | BoundaryOperation,pulseCode,independentPulseKernel,boundaryKernel,Code/view lemmas |
| [UnifiedLean.Source.SourceBoundaryLocations](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceBoundaryLocations.lean) | `f7c050056e121c7e0e12eb071383cb1369e8fe9de887d7ad875a76904d48de5b` | actual_pulse_code_location,actual_original_node_kernel_movement |
| [UnifiedLean.Source.SourceBoundaryProjection](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceBoundaryProjection.lean) | `f1cb1e557b5f08cba2d37465bc4386bc6adc2f19fd12a132f7d6f835b1e24f0f` | actual_boundary_projection,projected_boundary_eq_of_same_view |
| [UnifiedLean.Source.SourceCrossCarrierBoundary](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCrossCarrierBoundary.lean) | `c3d453eb58dcf0a21f06acc4513428cb9d6ff31093a73e9a284b992531514308` | actual_cross_carrier_boundary_law |
| [UnifiedLean.Source.SourceProgramTransport](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceProgramTransport.lean) | `d009fdfc510bfcaffaeea3bc241401eaf2996178ff4b82376eb22f1e49387831` | ProgramStep,sourceProgram,actual_source_program_projection |
| [UnifiedLean.Source.SourceCalendarCompiler](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceCalendarCompiler.lean) | `9974446d99fa344593d294e315e349ab71fdbe7574e932bb8b1a16ee1b2369fd` | originalNodeOperation,boundaryOperations,compiledCalendarProgram |
| [UnifiedLean.Source.SourceInitializedCalendar](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceInitializedCalendar.lean) | `47ea73231fbfa732495e4fc5f42f1374e2ef505bfe3d4073b6cc2bed3fcc5535` | initialCode,actual_calendar_tail_support,initialized_original_calendar_ancestral_support |
| [UnifiedLean.Source.SourceNaturalInitialization](../../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceNaturalInitialization.lean) | `18050e86ebeb2d11ced94d0e3a2199f0c58b7ae4d7029288c28b0c893ec159e1` | originalGamma,originalRegisterPMF,naturalCalendarLaw,actual_natural_calendar_projection |
| [Oldest checked routing](../../../2026-10-01-sol61-g-program-lean-2152z/program/G2LiveLineageRouting.lean) | `bf33f6be93e61960aa637df34d1197316669d6f2ddde6d743ac405a010cb05af` | Same bf33 source; original compile_exit_code0 receipt retained |
| [Oldest checked labelled forest](../../../2026-10-02-dot-source-labelled-forest/SourceLabelledForest.lean) | `d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d` | Same d6e5 source; October2 local compiler receipt retained |
| [G1UnrankedActualBoundary](../../../2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedActualBoundary.lean) | `4c4dafb446c321625a32159a4d8819148f9b5e715ec9c64594a8d289b5197b8f` | actual_unranked_boundary_row_independent,actual_unranked_source_boundary |
| [G2ActualTimedAllPanelLaw](../../../2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/G2ActualTimedAllPanelLaw.lean) | `05ca8311eb01110a0d01d1f12ef6fe744fef51b21f1c3592e90bad3b08f6c376` | actual_natural_complete_timed_all_panel_projectivity,actual_controlled_complete_timed_all_panel_projectivity |
| [G7OriginalBoundaryPolynomial](../../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7OriginalBoundaryPolynomial.lean) | `f447e7ad6c52ab2a16781fb4671e33eadf508309789f2f0046f2765237efcf4c` | coinPolynomial,pulsePolynomial,nodePolynomial,actual_original_node_polynomial |
| [G7OriginalInitializationPolynomial](../../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7OriginalInitializationPolynomial.lean) | `b8654be54432ee28f616ea9140d9522a43d8484594f865b7aeb8c2e77e26d0e2` | actual_original_coin_mass,registerPolynomial,initialPolynomial |
| [G7SelectedKernelPolynomial](../../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SelectedKernelPolynomial.lean) | `2333a9c93d5e24c9722a4337b6d83315119dbe79d52eb10e73941a3a903638ba` | epochTable(Classical.choose),nodeTable,exitTable |
| [G7SymbolicProgramPolynomial](../../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SymbolicProgramPolynomial.lean) | `17619976e462ada4686ab1d018d67c712c69defbf20e1d9a8a97299f7dbb7230` | WordVariable,instantiateGamma,wordVariables,stepPolynomial,naturalWordPolynomial |
| [G7GlobalOwnerCoins](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/a8ce7af87d48354493a9a5b6ce283fcfb0116f3a51ef8ecc10fc872784edca1a.lean) | `a8ce7af87d48354493a9a5b6ce283fcfb0116f3a51ef8ecc10fc872784edca1a` | restrictOwners,restricted_pmf,independent_pulse_fixed_carrier; recovered whole-edge dependency |
| [G7NodeActions](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/478d9505249525e3710c5ed1bf4e1c3d8b107c217b88d8f86d9863fd959c0967.lean) | `478d9505249525e3710c5ed1bf4e1c3d8b107c217b88d8f86d9863fd959c0967` | Action,destination,Canonical,destination_register,kernels_commute(distinct sites); recovered dependency |
| [G7BoundaryRelabelling](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/d10eb8af3f73675bd8567801bfc3133bced8fa180b913f6ffa24c2726042e00f.lean) | `d10eb8af3f73675bd8567801bfc3133bced8fa180b913f6ffa24c2726042e00f` | operation,owners,independent_kernel,boundary_kernel; recovered dependency |
| [OriginalFixedIDControls](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/5b32ee2edff84d6ef7c75549b55e7368380fcff9dbb3b0cd4397584746bb224d.lean) | `5b32ee2edff84d6ef7c75549b55e7368380fcff9dbb3b0cd4397584746bb224d` | OriginalMask,forcedParameter,controlledMode,actual_forced_hybrid_kernel |
| [G7OriginalEdgeGathering](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/ee32fdfb063d46e1720cfdfe549c6349d7c6032cbcf38d981514290c7de16c44.lean) | `ee32fdfb063d46e1720cfdfe549c6349d7c6032cbcf38d981514290c7de16c44` | Event,gather,exit_drop_bank,node_flush_bank; historical failed/incomplete candidate |
| [Original joint-frontier Python](../../../2026-10-01-g7-continuous-design/law_compiler.py) | `eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7` | compile_law: first incoming occurrence has G mass; inherited LAW provider |
| [Frozen LAW contract](../../../2026-10-10-codex-lean-rust-parity/design/LAW-CONTRACT.md) | `1a9b0941ea7b17950155b4d885497e1d19ae88ab47f010b6edf6a73b94032afa` | G=P(incoming0); current byte identity, not original-gamma equivalence |
| [Internal Rust source_epoch](../../../2026-10-10-codex-lean-rust-parity/rust/src/source_epoch.rs) | `c46a498ac2b5a0f3bc3ea246cc4f6d012ff58871292b8af84cfebe3d45b40354` | selected_view,restrict_panel,join_panel,epoch_row; separately pinned candidate |

Evidence/manifest byte identities observed for this review:

- [Delivered coefficient graph](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/latest/coefficients/DEPENDENCY-GRAPH.json): `1be463cd138b5f7c3bbc14112bbd12bea370824bc59b1f6eb3c57d627d6fbbd2`.
- [Repaired coefficient certificate](../../../2026-10-10-codex-lean-rust-parity/lean/COEFFICIENT-RECOVERY-CERTIFICATE.json): `55c654b47ccffb998dfb6043dc06d45b1e1433ca55f2a205dc8b1ab65ac5532a`.
- [Independent coefficient review](../../../2026-10-10-codex-lean-rust-parity/quality/COEFFICIENT-RECOVERY-REVIEW.json): `d9b3a51ab52a1834ceada8386e305be4cca58196d7c1d33e9a504819456ee619`.
- [Current G2 certificate](../../../2026-10-10-dot-g2-current-source-verification-0042z/CERTIFICATE.json): `e7bfa79b0b53d35afd464b3eca56e08f5325273126eba76f07662b3e0ad411a8`.
- [Latest candidate historical status](../../../2026-10-10-dot-g7-pending-codex-recovery-0952z/LATEST-CANDIDATE-STATUS.json): `0b982eb70bbcfa0f064821d3de78ace9211ef35be23ff804be267f75a2b8ec7e`.

Registry checked at 2026-10-10 12:01:09 UTC. All fourteen oldest/current source pairs match the delivered coefficient graph and source-store bytes. No fresh kernel or runtime execution is inferred from that equality.
