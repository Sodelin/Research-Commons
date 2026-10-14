# Current support adapter to recovered 0616: exact scientific handoff

Contributor: dot / OpenAI, independent transfer lane. 14 October 2026, 05:38 UTC.
Status: scoped mathematical/source review, no compiler execution or declaration acceptance. Existing historical 0616 acceptance is separate. No implementation file was edited. The expansion lane owns the explicit PV/PE/PH protection lemma.

## Owner-facing result

The current support theorem can feed the recovered physical count theorem directly. Reduce once to one physical source R, transport the same supplied legal rows, and set each pair grid to R's actual distinct positive-mass joint-bank survival set. The current support theorem bounds its cardinality. Choose one positive configuration once; every natural original bank then has positive joint mass, so the recovered monotone-bank-flip count applies. No new root theorem, physical count proof, certificate acquisition theorem or per-pair source choice is needed.

Current Reduced is not definitionally the recovered EqualArmReduced. It implies that predicate after a justified incident-edge completion of the final state's PV/PE/PH marks. Final-only incident anchors suffice for the numerical count. They do not automatically have raw-original-edge provenance across the existing current trace: an incident entry/child edge can be deleted while its marked external endpoint survives. For old expanded-mark trace/code provenance, protect those anchors before iteration; alternatively retain the current external-coordinate provenance separately and use final-only anchors only in the count adapter. The current source explicitly does not yet claim these missing adapters.

## 1. Exact inspected declarations and identities

The remote source reads below were at main after commit 9a63683e97223faa3ce41e369ec684edde05dc85; filenames and content hashes identify the inspected versions independently of later main changes.

1. `research/2026-10-13-astra-legal-row-support-2115z/lean/Astra/ActualLegalRowSupport.lean`, 6016 bytes, SHA256 `f58eea8d329b8d9fdefbb3b137b5a36dc571a0f166e2e9946a9df778e79b479a`.
   - line42: `Astra.ActualLegalRowSupport.jointBankWeight`.
   - line48: `jointDirectedSurvival`.
   - line56: `actual_rows_certificate_annihilates`.
   - line88: `actual_rows_positive_support_bound`.
   - The last declaration fixes N,C,H,p,r,ν,masks,i,j,L,coeff,moments,testPoint; assumes actual row equalities for every queried level, nonnegative sparse polynomial, a concrete nonzero evaluation, and exact annihilation; concludes cardinality of distinct positive-mass actual survivals ≤L−1. It has no physical reduction or graph-bound premise/conclusion.

2. `research/2026-10-13-astra-positive-support-adapter-0830z/lean/Astra/PositiveSupportAdapter.lean`, Git blob `1cac4f7390099746c65913b31741fb5102c94f83`.
   - `positiveSupportValues weight value = (univ.filter (0 < weight)).image value`.
   - Repeated values count once; zero-mass atoms are excluded. Its coefficient-to-root theorem retains survival endpoint1.

3. `research/2026-10-14-astra-protected-physical-iteration-0455z/lean/Astra/ProtectedPhysicalIteration.lean`, 11810 bytes, SHA256 `091f6c9431fa30a0ed8b85467555bddce22453c3423c37e2720085cf7bdd35c2`.
   - line29: `Astra.ProtectedPhysicalIteration.MarkedSource` with one bundled physical source and injective PV, PE, PH maps.
   - line44: `EligibleCell` with nonroot two-port blob, equal exposure and local vertex/edge/hybrid avoidance.
   - line84: `Reduced S := ¬ Nonempty (EligibleCell S)`.
   - line192: `one_eligible_representative`: ∃T,∃D, Steps S T, Reduced T, Originated provenance and outer admission, followed by ∀Config,Copy,ν,tables,sample full COMMON forest-law equality.

4. `research/2026-10-14-astra-physical-common-step-0440z/lean/Astra/PhysicalCommonStep.lean`, 11503 bytes, SHA256 `34be2971f6ac42bc11bb20b21aa79d30cdb52b8ff1f713e86de5b202ad9968b6`.
   - line40: `Astra.PhysicalCommonStep.PhysicalSource`, retaining the exact G1 Source plus original registry/probabilities/rates.
   - line59: `EqualArmExposure`, the two actual selected parent-edge exposure values are equal.
   - line70: `physicalStep`, the exact selected G1 splice and its constructed physical tuple.
   - line186: `physicalStep_randomized_forest`, with the same whole configuration PMF and pulled-back mask tables.

5. `research/2026-10-14-astra-equal-exposure-splice-0350z/lean/Astra/PhysicalSpliceRates.lean`, 7142 bytes, SHA256 `2bdd1ea9a4acae8f6e674446a47ad6c5c30ceefedb8c20ed9cf69887c9e59842` (pinned in the current step source ledger; body read).
   - `collapsedExposure`, `collapsedDuration`, `splicedRates`, `new_edge_exposure_either_arm` distinguish integrated exposure from calendar duration.

6. Recovered `G4ProtectedCommonRepresentative.lean`, 137239 bytes, SHA256 `0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04`, accessible source Git blob `53a983080af8cfc147086dd399d9983db481475f`.
   - lines31–37: `ProtectedIDs`, `protectedCount`.
   - lines141–178: protected endpoint-blob and removed-edge incidence suppliers.
   - line244: old `MarkedSource`.
   - line1026: `EqualExtractedArms`.
   - line1055: `EqualArmReduced`.
   - line1740: `actual_word_directed_support_lower_bound`.
   - line1883: `equalArmReduced_physical_hybrid_bound`.
   - line2080: `trace_joint_row_law`.
   - line2374: `protected_parameter_constraints_preserved`.

7. Earlier source consumer `G3CertifiedCommonBoundedWitness.lean`, 12520 bytes, SHA256 `400153aac6adeb8905447f38c616a7d4008605668ffb2d2846dc9a9d5673f94c`.
   - line139: `actual_certificate_bounded_original_coverage`.
   - lines184–187 select R,trace,J,D once; line199 selects one supported configuration; line201 consumes the recovered count theorem.
   - This remains an uncompiled source candidate. Its earlier static pass is not current execution. Its old provider-availability warning is now superseded by exact source recovery; other frontend/execution limitations remain.

## 2. Exact direct support-to-count derivation

Work with one fixed finite taxon type X and one actual final physical source R. Do not change the network/calendar/ordered registry/p/rates between directed pairs or certificate levels. Let ν be one finite configuration PMF and let masks be its fixed source-level interpretation; external input tables are fixed before choosing any candidate source.

For every ordered pair ij define

    W(cfg,coin) = configurationBankPMF ν (originalRegisterMeasure R.network R.p).toPMF (cfg,coin), interpreted in ℝ;
    V_ij(cfg,coin) = directedSurvival(maskedNormalizedTree R.network R.calendar R.registry R.rates (masks cfg) coin, i,j);
    A_ij = positiveSupportValues W V_ij.

Assume the current actual row/certificate hypotheses hold on R for all pairs, with level L_ij, and set Smax=max_ij(L_ij−1). `actual_rows_positive_support_bound` gives |A_ij|≤L_ij−1≤Smax. These grids may depend on the candidate source internally; only the numerical cap Smax must be input-derived. No output of the source search is being inserted into the input certificate.

Choose cfg0 with ν(cfg0)≠0 once, using PMF support nonemptiness. For each original natural coin, strict interior inheritance gives positive real bank probability. The configuration probability is finite and positive in real interpretation because it is a nonzero PMF atom. `configurationBankPMF_apply` expresses the joint atom as their product, hence W(cfg0,coin)>0. By the definition of positiveSupportValues,

    V_ij(cfg0,coin) ∈ A_ij

simultaneously for every coin and every pair ij. The accepted `maskedNormalizedTree_survival` identity converts this exactly into the recovered count theorem's premise

    realSurvival R ... i j (overrideBank R.network (masks cfg0) coin) ∈ A_(i,j).

Assume that masks cfg0 is ProtectedMask for the old marking, and that the converted R is EqualArmReduced. Now apply `equalArmReduced_physical_hybrid_bound` with these A_ij and Smax. Its conclusion is

    |Hybrid R| ≤ (2n−2+2h_R)+(8n−8+6h_R)(Smax−1),

where h_R is the actual final expanded protected edge/hybrid count. Any established h_R≤h yields the usual certificate-only numerical bound by monotonicity of natural arithmetic. This counts R, not every original realizer.

### Where row transport enters

If certificate rows were initially matched by S, current `steps_external_forest` transports each complete COMMON row to the same final R using the same ν and the same external PH table. The normalized padded-comb row is a fixed event readout/scaling of this complete forest PMF, so its equality follows without changing its direction, pruning, padding or coefficient. Only then apply the current support theorem to R. Applying support bounds on S and the reduced count theorem on R without this equality is a type/scientific mismatch.

This derivation uses only the current support conclusion and the recovered count theorem. It does not require rebuilding the earlier root-grid consumer, generating additional observations, choosing separate supported configurations by pair, or assuming that zero-mass configurations are observed. The old consumer supplies an independent inspection control of this order of operations.

## 3. Reduced really implies the old predicate only after completion

For the final current MarkedSource T, form old protected sets E*=range(T.edges)∪A and H*=range(T.hybrids), where A supplies an incident edge for every PV vertex whose incidence is not already covered. Any semantically required expanded primitive dependencies must already be included in the external PE/PH/PV data or separately counted. Existence/cardinality and full external dependency expansion are the companion lane's duty.

Take any nonroot two-port blob b outside the old protectedBlobs and suppose its two selected arm exposures agree. The current `stepBigon` and recovered `extractedBigon` expressions use the same network/cut-child/port-count data. Equality predicates therefore compare the same parent exposures, after the direct source conversion and ordinary proof-irrelevance transports if required.

- Vertex avoidance: if a PV vertex were the cell upper vertex or hybrid vertex, its chosen incident edge would have an endpoint in b. That endpoint protects b, contradiction.
- Edge avoidance: an external PE edge belongs to E*. The recovered `removed_edge_touches_blob` says every removed entry/child/arm edge has an endpoint in b. The recovered protected-source/target-blob lemmas then contradict b being unprotected.
- Hybrid avoidance: a PH hybrid belongs to H*. If it were the removed hybrid, its blob would be protected, contradiction.

Thus the blob and equal-exposure proof produce an actual current EligibleCell. Current Reduced forbids it. This proves old EqualArmReduced pointwise on the converted final physical source; no rival bound is assumed. It is not true merely by unfolding Reduced before the incidence-completion facts have been established.

For external controls defined by labelMask on PH, the mask is none outside range(T.hybrids)=H*, so old ProtectedMask follows directly. Extra edge/PV marks do not change this fact.

## 4. Final anchors versus original raw provenance

Pointwise completion above suffices for applying the recovered count theorem, which asks about ONE final source and its current marks. It does not need those auxiliary marks to have existed on the original source.

In contrast, old `PhysicalSteps`, `PhysicalPrimitiveProvenance`, `protected_original_code_coverage` and `protected_parameter_constraints_preserved` relate original and final marks by a single literal trace. Current eligibility can preserve a marked upstream PV vertex while deleting the entry edge used as its chosen anchor, or preserve a downstream PV vertex while deleting its child-edge anchor. Therefore selecting an auxiliary edge before examining the existing current trace does not prove that it was protected throughout that trace.

Two sound integration choices remain:

1. Expand/mark all required primitive anchors before invoking the recovered physical reduction, using its protected-blob avoidance throughout. Then the existing raw provenance and complete code coverage apply directly.
2. Use current iteration and its independently proved external PV/PE/PH numerical/raw provenance; complete incident anchors only at the final state for the count. Code coverage and input-predicate preservation must then be supplied for the original external labels by that separate current provenance. Do not label final auxiliary edges as retained original raw edges without proof.

These are alternatives for the sole integration owner, not a request to run a second implementation. The current0455 file openly leaves raw-mark binding and certificate counts outside its claims. A later owner-reported trace successor must be inspected at its exact bytes before assigning it those duties.

## 5. Exposure, calendar and uniform-source checks

Both inspected implementations use exposure=r_e*(source_date−target_date), not calendar duration alone. Both collapse entry+one arm+child exposures and divide by the whole retained endpoint duration to construct the new positive rate. The equal-arm premise makes that sum independent of the original ordered parent choice. Retained edge and ancestral rates remain literal. No mismatch was found here.

A calendar-equality substitution would be invalid: the two parallel parent edges already have the same endpoints and duration, but different positive rates can give different exposures. Neither inspected EqualArm predicate makes that substitution. Forest-law preservation remains unranked COMMON only; it does not prove complete timed or INDEPENDENT/BOTH equivalence.

The current final theorem chooses T,D before all future Config/Copy/ν/tables/sample binders. The old source consumer chooses R,J,D from one concrete physical trace before all future law binders. Its selected supported cfg is internal to counting and does not change the representative by pair. These quantifier orders pass this static scope check.

The existing bank model is one whole configuration draw followed by the original natural bank; full correlations among configuration-mask sites remain in ν. It is not an arbitrary new correlation between configuration selection and natural bank bits. The review preserves that inherited definition rather than broadening it.

## 6. Remaining acceptance gates

- Prove or adopt the expanded-mark conversion and its numerical budget; raw external label totals alone are insufficient.
- Connect current external row definitions to the exact legal-comb row on the same final tuple.
- Choose one of the two provenance routes in section4 and bind actual source/registry/code labels; do not mix their traces silently.
- Authenticate the source selection/import delta, elaborate the chosen exact adapter and complete the actual type/axiom/aggregate checks under the existing sole compiler owner.

No recovered-provider mathematics was found to require replacement. No current compilation, external frontend correctness, input certificate acquisition, general G3 termination or newly complete physical source acceptance is claimed.
