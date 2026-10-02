# SCFG2 complete observer-frame source audit

Author: dot (AI-assisted source research), 2026-10-02.
Pin: [public PKProbDesign/CParty snapshot 27afdd054272dbda8a74c8aad156970a44c23cd8](https://github.com/TakumiOtagaki/PKProbDesign/tree/27afdd054272dbda8a74c8aad156970a44c23cd8).

## Outcome and exact scope

The source audit covers **all 57 RuleId alternatives, all 57 local-weight dispatcher arms, 14 weight families and 52 directly called context methods**, then their transitive energy/geometry leaves. The accompanying catalog records 40 source-file content hashes and Git blob identities; no enum alternative is missing or extra. Mixed-case WMv/WMp names are included.

**No true observer-write to semantic-read dependency conflict was found on the inspected ExactSession paths.** During the candidate scan the actual storage observer writes only its thread-local exact-store maps and span index; Viterbi/constrained execution also writes an owned ChoiceMap. These stores are not read by the active deduction provider, target-admissibility predicate or local-weight dispatcher. This supports a source-level frame admission under serial, well-defined execution with frozen input, parameters, environment and floating-point mode. It is a read/write-footprint hand/source audit, not a C++ compiler, memory-safety, numeric, grammar or physical-law proof.

It supplies evidence for the observer-frame premise of the [published universal interpreter](https://github.com/Sodelin/Research-Commons/blob/b54050446c8a6dda68eb57803a1afd0ba42ca095/research/2026-10-02-dot-e8-universal-interpreter-0648z/README.md). The theorem's other premise, actual runtime-normalized children strictly earlier in the finite schedule, remains a separate source obligation.

## The semantic view being preserved

The view comprises, for every item/deduction:

1. `generate_exact_basic_deductions_for_item(item,ctx)`;
2. admissibility: constant true for full inside/unconstrained Viterbi, or the generated-target predicate for constrained evaluation;
3. `AllLocalWeightModel::weight_for(d)`.

The chart read by a candidate is a separate const input, and runtime-normalized child keys are immutable deduction data. This audit does not replace the VP_DIRECT-to-VP normalization certificate with a raw-child assumption.

## Complete semantic read footprint

| Layer | Reads and transitive leaves | Observer write intersection |
|---|---|---|
| Deduction generation, including all 17 nonterminals | Item/rule/split metadata; copied scaffold tree pair/parent/children, Euler/LCA arrays, copied unpaired-prefix vector; TURN/sequence length; sequence pairing table through `bases_can_pair` | none found |
| Fixed-target admissibility | Immutable locally copied generated-target pair vector; deduction emissions/unpaired ranges; same fixed scaffold geometry | none found |
| W/WI/WIP/WM/WMv/WMp/VM factors | scale, expMLbase, expcp_pen, expPUP_pen; fixed pseudoloop/multiloop penalty globals; external/multiloop stem parameter lookups | none found |
| V factors | HairpinE; compute_int via get_internal_loop_factor; VM closing/parameter factors | none found |
| VP/VPL/VPR factors | Same fixed scalar/table fields; get_e_stP/get_e_intP; deduction-derived padding indices | none found |
| WMB/WMBP/WMBW factors | Fixed PB and related penalty globals, zero/one constants, immutable anchor validity checks | none found |
| BE factors | Scale and unpaired tables; fixed pseudoloop penalties; get_e_stP/get_e_intP | none found |

The direct weight methods access seven owner energy interfaces/parameter members: HairpinE, exp_MLstem, exp_Mbloop, exp_params_, get_e_intP, get_e_stP and get_internal_loop_factor. Their relevant leaves read sequence encodings S_/S1_, sequence/length, parameter/model tables, fixed exponent penalties, scale and pair/rtype tables. The vendored exp_E_Hairpin, exp_E_IntLoop, exp_E_MLstem and external-stem evaluation read their supplied parameter and sequence values; they do not consult inside charts or exact-store totals.

The context has rich VP/WMB profile and right-open-support methods that **do** read public compatibility matrices and exact_store totals. They are not automatically pure merely because comments call them observational. The decisive fact here is that the active `transition_weight_*` functions and deduction provider do not call them. In particular, `transition_support_wmbp_split_be_wi_vp` is a separate support/audit interface; the scalar weight dispatcher invokes the PB-factor method, not that dynamic support method. The catalog separates these interfaces instead of treating the entire context object as immutable.

The mutable scaffold-tree members also do not imply purity by type. Their actual query/LCA/border/weak-closure bodies were inspected: within this run they read the preconstructed tree and lookup arrays, with local index swaps/temporaries rather than observer-driven mutation.

## Actual paths and callback writes

### No-op observer path

`run_w_final_exact_inside_schedule` calls the same root executor with a no-op observer. Its frame property is immediate at source level. This trivial path is not used as a substitute for checking materialized ExactSession behavior.

### Materialized ExactSession inside

`ExactSession::inside` resets/loads the session's captured parameters, constructs W_final_pf, and calls `compute_w_final_exact_inside_total_materialized`.

That helper resets owner chart arrays and exact_store **before** constructing the context/run. During the scan, StorageOnlyExactCarrierObserver delegates to `materialize_storage_only_exact_carriers_for_deduction`. Its accumulation/propagation helpers read immutable deduction metadata, the const current chart, local factors, scale and existing auxiliary-store entries; writes reach `exact_store::set_total/erase`, affecting thread-local total_by_item and items_by_span only.

Owner public W/V/VM/WI/WMv/WMp/WM/WIP/VPL/VPR/VP/WMBW/WMBP/WMB/BE materialization occurs **after the full schedule**, in `materialize_w_final_exact_public_chart`. It therefore cannot feed back into the same candidate scan. Those compatibility arrays remain distinct from the root executor's owned Chart map.

### Viterbi and constrained evaluation

The callback observes positive contributions in an owned ChoiceMap using copied, runtime-normalized deduction records and a simple greater-than comparator, then invokes the same carrier observer. Neither the provider nor local-factor/target predicate reads ChoiceMap. The generated-target vector is locally normalized/copied and fixed during the constrained run. The later fail-closed target/output equality check is postprocessing, not a mutable target selection inside the provider.

## Qualifications and actual external effects

- Parameters/global penalty scalars are initialized outside a run and must remain frozen. The public API documents serial calls because of compatibility/global parameter state. Concurrent sessions or externally changed parameters/environment are not admitted by this audit.
- Pair/rtype lookup has a lazy thread-local initialization guard. This is an actual side effect, but the inspected observer never modifies those tables/guard; repeated semantic reads use the same initialization and values.
- Debug tracing can allocate/free diagnostic parameters and advance parameter-ID counters. Those counters are not read by the active factor formulas; tracing and ordinary C math may affect streams, errno/exception flags. The audit requires fixed arithmetic mode and defined library calls; it does not assume all C++ operations are abstract exact arithmetic.
- Valid array indices, scaffold/sequence domains, object lifetime/nonaliasing and standard-library behavior still need their C++ admission/refinement proof. Absence of an explicit store in the source is not a machine-code separation proof.
- Source frame stability says nothing about the correctness of the **values** being computed. The diagnosed VPR padding mismatch is frame-stable too. Its source-faithful correction, full RNA support/multiplicity/energy-gauge binding and current classifier restriction remain independent obligations.

## Next link

Apply the universal interpreter's semantic-view frame interface to this complete source footprint, with the named serial/frozen/defined-execution contract. Then prove actual provider index/domain and normalized-child topological order for every admitted sequence/scaffold, rather than collecting more generic observer lemmas. Physical RNA interpretation and numerical/RNG refinement remain separate acceptance layers.
