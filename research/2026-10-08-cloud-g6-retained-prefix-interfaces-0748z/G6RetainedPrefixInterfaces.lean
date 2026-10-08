import G6MergerPhaseSquare
import PrivateSeedFactorization
import G1SpliceDegrees
import Mathlib.Data.List.Perm.Basic

/-!
Actual retained hybrid orientation and naturally initialized second carrier.
Cloud Sol delegated original G6 structural/source lane, 8 October 2026.
Original G1 graph/degrees/parent/source initializer and seed providers: Dot;
private-product consumer: existing Cloud. Compiler UNCHECKED, outside181/179.

The actual incoming occurrence bijection CONSTRUCTS the second registry.
Its natural register law is a proved marginal of the SAME original product;
no equal initializer/prefix kernel or target law is a supplied field.
The synthetic edge's youngest old-child rate has no later scalar span licence.
Full tied batch/prefix recurrence is a separate consumer, not asserted here.
-/

namespace UnifiedLean.G6.RetainedPrefixInterfaces
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest MeasureTheory ProbabilityTheory
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceForestPulseMeasure
open CloudG6.PrivateSeedFactorization
open UnifiedLean.G6.OriginalSpliceAdapter UnifiedLean.G6.SpineBoundaryCarrier
open UnifiedLean.G6.ProtectedChildCarrier UnifiedLean.G6.BoundaryPhaseRelation
open G1BigonFootprint G1BigonSpliceGraph G1SplicedSourceAdmission G1SpliceDegrees
open scoped Classical
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable (N : RootedBinary V E X)
variable (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
variable (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
variable (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)

noncomputable def removedVertices : Finset V :=
  {(derivedBigon N hcut b hb hp).fragment.upper,
    (derivedBigon N hcut b hb hp).fragment.parents.hybrid}

theorem retained_not_removed (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) :
    v.val ∉ removedVertices N hcut b hb hp := by
  simpa only [removedVertices, Finset.mem_insert, Finset.mem_singleton, not_or] using v.property

theorem retained_hybrid_iff (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) :
    (suppressedNetwork N hcut b hb hp).graph.IsHybrid v ↔ N.graph.IsHybrid v.val :=
  actual_splice_hybrid_iff N hcut b (derivedBigon N hcut b hb hp) v

noncomputable def originalHybrid (v : Hybrid (suppressedNetwork N hcut b hb hp)) :
    Hybrid N := ⟨v.val.val, (retained_hybrid_iff N hcut b hb hp v.val).mp v.property⟩

noncomputable def outsideHybridEquiv :
    OutsideHybrid N (removedVertices N hcut b hb hp) ≃
      Hybrid (suppressedNetwork N hcut b hb hp) where
  toFun v :=
    let w : SplicedVertex N b (derivedBigon N hcut b hb hp) := ⟨v.val.val, by
      simpa only [removedVertices, Finset.mem_insert, Finset.mem_singleton, not_or] using v.property⟩
    ⟨w, (retained_hybrid_iff N hcut b hb hp w).mpr v.val.property⟩
  invFun v := ⟨originalHybrid N hcut b hb hp v, retained_not_removed N hcut b hb hp v.val⟩
  left_inv v := Subtype.ext (Subtype.ext rfl)
  right_inv v := Subtype.ext (Subtype.ext rfl)

noncomputable def retainedProbabilities (p : HybridProbabilities N) :
    HybridProbabilities (suppressedNetwork N hcut b hb hp) where
  gamma v := p.gamma (originalHybrid N hcut b hb hp v)
  positive v := p.positive _
  below_one v := p.below_one _

noncomputable def retainedCommon (common : Hybrid N → Bool) :
    Hybrid (suppressedNetwork N hcut b hb hp) → Bool :=
  fun v => common (originalHybrid N hcut b hb hp v)

/-- BOTH actual incoming edge IDs are mapped by G1's proved occurrence
bijection. An old child parent maps to the youngest new edge; all other
retained parents keep their old ID. No arbitrary parent reordering is used. -/
noncomputable def retainedParents (H : OriginalParentRegistry N)
    (v : Hybrid (suppressedNetwork N hcut b hb hp)) :
    GProgram.G2.OriginalHybridParents (suppressedNetwork N hcut b hb hp) := by
  let a := originalHybrid N hcut b hb hp v
  let e0 : {e : E // N.graph.target e = v.val.val} :=
    ⟨(H.parents a).parent0, (H.parents a).target0.trans (H.original_site a)⟩
  let e1 : {e : E // N.graph.target e = v.val.val} :=
    ⟨(H.parents a).parent1, (H.parents a).target1.trans (H.original_site a)⟩
  let f := actualInEdgeEquiv N hcut b (derivedBigon N hcut b hb hp) v.val
  exact {
    hybrid := v.val
    isHybrid := v.property
    parent0 := (f e0).val
    parent1 := (f e1).val
    target0 := (f e0).property
    target1 := (f e1).property
    different := by
      intro he
      have he' : e0 = e1 := f.injective (Subtype.ext he)
      exact (H.parents a).different (congrArg Subtype.val he') }

noncomputable def retainedRegistry (H : OriginalParentRegistry N) :
    OriginalParentRegistry (suppressedNetwork N hcut b hb hp) where
  parents := retainedParents N hcut b hb hp H
  original_site _ := rfl

/-- Boolean parent orientation is literal; true remains original parent1. -/
theorem retained_parent_orientation (H : OriginalParentRegistry N)
    (v : Hybrid (suppressedNetwork N hcut b hb hp)) (bit : Bool) :
    ((retainedRegistry N hcut b hb hp H).parents v).parent bit =
      (actualInEdgeEquiv N hcut b (derivedBigon N hcut b hb hp) v.val
        ⟨(H.parents (originalHybrid N hcut b hb hp v)).parent bit,
          registry_parent_target N H (originalHybrid N hcut b hb hp v) bit⟩).val := by
  cases bit <;> rfl

noncomputable def restrictHybridCoins (coin : Hybrid N → Bool) :
    Hybrid (suppressedNetwork N hcut b hb hp) → Bool :=
  fun v => coin (originalHybrid N hcut b hb hp v)

noncomputable def restrictRegister (register : V → Bool) :
    SplicedVertex N b (derivedBigon N hcut b hb hp) → Bool := fun v => register v.val

/-- No new latent bit is drawn. Every retained original slot, including the
inert false convention at ordinary/root/leaf vertices, stays the SAME slot. -/
theorem original_register_restriction (coin : Hybrid N → Bool) :
    restrictRegister N hcut b hb hp (originalRegister N coin) =
      originalRegister (suppressedNetwork N hcut b hb hp)
        (restrictHybridCoins N hcut b hb hp coin) := by
  funext v
  by_cases hh : N.graph.IsHybrid v.val
  · have hn := (retained_hybrid_iff N hcut b hb hp v).mpr hh
    simp only [restrictRegister, originalRegister, dif_pos hh, dif_pos hn,
      restrictHybridCoins, originalHybrid]
  · have hn : ¬(suppressedNetwork N hcut b hb hp).graph.IsHybrid v :=
      fun hv => hh ((retained_hybrid_iff N hcut b hb hp v).mp hv)
    simp only [restrictRegister, originalRegister, dif_neg hh, dif_neg hn]

/-- Concrete original product marginal on exactly the retained original sites.
The once-drawn private seed remains original auxiliary, never a new draw. -/
theorem actual_outside_coin_marginal (p : HybridProbabilities N) :
    (originalRegisterMeasure N p).map
      (fun c : Hybrid N → Bool => fun v : OutsideHybrid N (removedVertices N hcut b hb hp) => c v.val) =
      outsideCoinMeasure N (removedVertices N hcut b hb hp) p := by
  calc
    _ = ((originalRegisterMeasure N p).map
        (splitOriginalCoins N (removedVertices N hcut b hb hp))).map Prod.snd := by
      rw [Measure.map_map measurable_snd (splitOriginalCoins N _).measurable]
      rfl
    _ = ((privateCoinMeasure N (removedVertices N hcut b hb hp) p).prod
        (outsideCoinMeasure N (removedVertices N hcut b hb hp) p)).map Prod.snd := by
      rw [actual_original_coin_split]
    _ = _ := (measurePreserving_snd
      (μ := privateCoinMeasure N (removedVertices N hcut b hb hp) p)
      (ν := outsideCoinMeasure N (removedVertices N hcut b hb hp) p)).map_eq

/-- The second graph's OWN natural original-hybrid product is derived from
the same original seed product, using the exact retained hybrid equivalence. -/
theorem actual_retained_seed_product (p : HybridProbabilities N) :
    (originalRegisterMeasure N p).map (restrictHybridCoins N hcut b hb hp) =
      originalRegisterMeasure (suppressedNetwork N hcut b hb hp)
        (retainedProbabilities N hcut b hb hp p) := by
  let e := outsideHybridEquiv N hcut b hb hp
  let mu := fun v : Hybrid (suppressedNetwork N hcut b hb hp) =>
    bitMeasure (originalGamma (retainedProbabilities N hcut b hb hp p) v)
  let pi := MeasurableEquiv.piCongrLeft
    (fun _ : Hybrid (suppressedNetwork N hcut b hb hp) => Bool) e
  have hfun : restrictHybridCoins N hcut b hb hp =
      pi ∘ (fun c : Hybrid N → Bool => fun v : OutsideHybrid N (removedVertices N hcut b hb hp) =>
        c v.val) := by
    funext c v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  have hm : outsideCoinMeasure N (removedVertices N hcut b hb hp) p =
      Measure.pi (fun w => mu (e w)) := rfl
  rw [hfun, ← Measure.map_map pi.measurable (measurable_of_countable _),
    actual_outside_coin_marginal, hm]
  exact Measure.pi_map_piCongrLeft e mu

/-- The natural full register PMF is restricted to retained original vertices;
this is a proved initializer marginal, not an equal-marginal assumption. -/
theorem actual_retained_register_pmf (p : HybridProbabilities N) :
    (originalRegisterPMF N p).map (restrictRegister N hcut b hb hp) =
      originalRegisterPMF (suppressedNetwork N hcut b hb hp)
        (retainedProbabilities N hcut b hb hp p) := by
  unfold originalRegisterPMF
  rw [PMF.map_comp]
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
    ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    Measure.toPMF_toMeasure, Measure.toPMF_toMeasure]
  have hfun : restrictRegister N hcut b hb hp ∘ originalRegister N =
      originalRegister (suppressedNetwork N hcut b hb hp) ∘
        restrictHybridCoins N hcut b hb hp := by
    funext coin
    exact original_register_restriction N hcut b hb hp coin
  rw [hfun, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    actual_retained_seed_product]

/-- Actual original-tip initializations are related for EVERY old register;
this keeps the full original register in the joint coupling, not just a
selected erased/unranked row. The second register is literal restriction. -/
theorem initial_codes_related (sample : Copy → X) (register : V → Bool) :
    Related N hcut b hb hp (initialCode N sample register)
      (initialCode (suppressedNetwork N hcut b hb hp) sample
        (restrictRegister N hcut b hb hp register)) := by
  refine ⟨rfl, rfl, ?_, fun _ => rfl, ?_⟩
  · intro l hl
    rw [show (state (initialCode (suppressedNetwork N hcut b hb hp) sample
        (restrictRegister N hcut b hb hp register))).genealogy l = .leaf l from
      decode_encode_live_genealogy _ _ (initial_valid _ _ _) hl,
      show (state (initialCode N sample register)).genealogy l = .leaf l from
        decode_encode_live_genealogy _ _ (initial_valid _ _ _) hl]
  · intro x
    let v := (suppressedNetwork N hcut b hb hp).leaf (sample x)
    refine ⟨.node v, ?_, ?_⟩
    · rw [show copyLocation (state (initialCode N sample register)) x =
        .node (N.leaf (sample x)) from decode_encode_copyLocation _ _ (initial_valid _ _ _) x]
      rfl
    · rw [show copyLocation (state (initialCode (suppressedNetwork N hcut b hb hp) sample
          (restrictRegister N hcut b hb hp register))) x = .node v from
        decode_encode_copyLocation _ _ (initial_valid _ _ _) x]
      rfl

noncomputable def pairedNaturalInitialization (sample : Copy → X) (p : HybridProbabilities N) :
    PMF (Code N sample × Code (suppressedNetwork N hcut b hb hp) sample) :=
  (originalRegisterPMF N p).map (fun register =>
    (initialCode N sample register,
      initialCode (suppressedNetwork N hcut b hb hp) sample
        (restrictRegister N hcut b hb hp register)))

theorem natural_initial_original_marginal (sample : Copy → X) (p : HybridProbabilities N) :
    (pairedNaturalInitialization N hcut b hb hp sample p).map Prod.fst =
      naturalInitialCodeLaw N sample p := by
  rw [pairedNaturalInitialization, PMF.map_comp]
  rfl

/-- The second marginal is its ACTUAL natural initialization; no boundary
snapshot is substituted for a second prefix law. Later recurrence is separate. -/
theorem natural_initial_constructed_marginal (sample : Copy → X) (p : HybridProbabilities N) :
    (pairedNaturalInitialization N hcut b hb hp sample p).map Prod.snd =
      naturalInitialCodeLaw (suppressedNetwork N hcut b hb hp) sample
        (retainedProbabilities N hcut b hb hp p) := by
  calc
    _ = ((originalRegisterPMF N p).map (restrictRegister N hcut b hb hp)).map
        (initialCode (suppressedNetwork N hcut b hb hp) sample) := by
      rw [pairedNaturalInitialization, PMF.map_comp, PMF.map_comp]
      rfl
    _ = _ := by rw [actual_retained_register_pmf]; rfl

theorem natural_initial_pair_related (sample : Copy → X) (p : HybridProbabilities N)
    {z : Code N sample × Code (suppressedNetwork N hcut b hb hp) sample}
    (hz : z ∈ (pairedNaturalInitialization N hcut b hb hp sample p).support) :
    Related N hcut b hb hp z.1 z.2 := by
  obtain ⟨register, _, hz⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  rw [← hz]
  exact initial_codes_related N hcut b hb hp sample register

/-- Exact physical destination of one actual node patch, conditional on a
FULL-Copy fresh row. The row is read at current owner l, never independently
at every descendant copy. COMMON reads the unchanged original register.
Restriction of the product row to AtNode is the inherited actual coin law. -/
noncomputable def nodeDestination (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : V) (l : Copy) : Location V E :=
  if hr : v = N.root then .rootPopulation N.root
  else if hh : N.graph.IsHybrid v then
    .edge ((H.parents ⟨v,hh⟩).parent (if common ⟨v,hh⟩ then register v else fresh l))
  else .edge ((defaultSelector N).edge ⟨v,hr⟩)

noncomputable def nodeFreshParameter (gamma : Hybrid N → unitInterval) (v : V) : unitInterval :=
  if hh : N.graph.IsHybrid v then gamma ⟨v,hh⟩ else 0

/-- Actual node code, conditional on a full-Copy row. The row is restricted
to the true current AtNode owners, whose index remains the original Copy ID.
COMMON uses the actual old register, not the fresh independent row. -/
noncomputable def nodeCodeWithFresh (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (fresh : Copy → Bool) (v : V) {sample : Copy → X}
    (s : Code N sample) : Code N sample :=
  if hr : v = N.root then rootCode N s
  else if hh : N.graph.IsHybrid v then
    pulseCode (H.parents ⟨v,hh⟩) s (fun l =>
      if common ⟨v,hh⟩ then (state s).register v else fresh l.val)
  else ordinaryCode N s ((defaultSelector N).edge ⟨v,hr⟩)

/-- Marginalizing unused FULL-Copy bits is exactly the existing CURRENT-owner
product PMF, proved from the inherited finite product restriction theorem. -/
theorem full_coin_current_owner_pmf {sample : Copy → X} (gamma : unitInterval)
    (s : Code N sample) (v : V) :
    (currentCoinPMF Copy gamma).map
      (fun c : Copy → Bool => fun l : AtNode (state s) v => c l.val) =
      currentCoinPMF (AtNode (state s) v) gamma := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), currentCoinPMF,
    currentCoinPMF, Measure.toPMF_toMeasure, Measure.toPMF_toMeasure]
  exact (coin_restriction_measurePreserving gamma
    (fun l : Copy => l ∈ (state s).live ∧ (state s).location l = .node v)).map_eq

/-- This is a DERIVED equality with the actual original boundary kernel.
No full-Copy product or fitted node law replaces the current-root model: its
unused coordinates are integrated out by full_coin_current_owner_pmf. -/
theorem node_fresh_row_actual_kernel (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) {sample : Copy → X} (s : Code N sample) :
    (currentCoinPMF Copy (nodeFreshParameter N gamma v)).map
      (fun fresh => nodeCodeWithFresh N H common fresh v s) =
      boundaryKernel N (originalNodeOperation N H gamma common v) s := by
  by_cases hr : v = N.root
  · simp only [nodeCodeWithFresh, originalNodeOperation, dif_pos hr, boundaryKernel,
      PMF.map_const]
  · by_cases hh : N.graph.IsHybrid v
    · cases hc : common ⟨v,hh⟩ with
      | false =>
          simp only [nodeCodeWithFresh, originalNodeOperation, dif_neg hr, dif_pos hh,
            hc, Bool.false_eq_true, if_false, nodeFreshParameter, boundaryKernel,
            independentPulseKernel]
          rw [← full_coin_current_owner_pmf N (gamma ⟨v,hh⟩) s (H.parents ⟨v,hh⟩).hybrid,
            PMF.map_comp]
          rfl
      | true =>
          simp only [nodeCodeWithFresh, originalNodeOperation, dif_neg hr, dif_pos hh,
            hc, if_true, boundaryKernel, PMF.map_const]
          rw [H.original_site ⟨v,hh⟩]
    · simp only [nodeCodeWithFresh, originalNodeOperation, dif_neg hr, dif_neg hh,
        boundaryKernel, PMF.map_const]

theorem full_coin_pulse_copy_location (H : GProgram.G2.OriginalHybridParents N)
    {sample : Copy → X} (s : Code N sample) (fresh : Copy → Bool) (x : Copy) :
    copyLocation (state (pulseCode H s (fun l => fresh l.val))) x =
      if copyLocation (state s) x = .node H.hybrid then
        .edge (H.parent (fresh ((state s).ancestor x))) else copyLocation (state s) x := by
  rw [show copyLocation (state (pulseCode H s (fun l => fresh l.val))) x =
      copyLocation (pulse H (state s) (fun l => fresh l.val)) x from
    decode_encode_copyLocation N.root _
      (pulse_source_valid H sample _ s.property _).forest x]
  have hl := s.property.forest.ancestor_live x
  by_cases hn : (state s).location ((state s).ancestor x) = .node H.hybrid
  · simp only [copyLocation, pulse, transport, dif_pos (And.intro hl hn), if_pos hn]
  · have hh : ¬((state s).ancestor x ∈ (state s).live ∧
        (state s).location ((state s).ancestor x) = .node H.hybrid) := fun h => hn h.2
    simp only [copyLocation, pulse, transport, dif_neg hh, if_neg hn]

theorem node_destination_not_node (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : V) (l : Copy) (w : V) :
    nodeDestination N H common register fresh v l ≠ .node w := by
  unfold nodeDestination
  split_ifs <;> intro he <;> cases he

noncomputable def nodeLocation (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : V) (l : Copy) (old : Location V E) : Location V E :=
  if old = .node v then nodeDestination N H common register fresh v l else old

/-- The pure location patch is proved to be the ACTUAL source node update at
each original copy's current owner; no node movement is supplied as a field. -/
theorem actual_node_fresh_location (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (fresh : Copy → Bool) (v : V)
    {sample : Copy → X} (s : Code N sample) (x : Copy) :
    copyLocation (state (nodeCodeWithFresh N H common fresh v s)) x =
      nodeLocation N H common (state s).register fresh v ((state s).ancestor x)
        (copyLocation (state s) x) := by
  by_cases hr : v = N.root
  · simp only [nodeCodeWithFresh, dif_pos hr]
    rw [rootCode_copyLocation]
    simp only [nodeLocation, nodeDestination, dif_pos hr, hr, rootLocation]
  · by_cases hh : N.graph.IsHybrid v
    · simp only [nodeCodeWithFresh, dif_neg hr, dif_pos hh]
      rw [show (fun l : AtNode (state s) (H.parents ⟨v,hh⟩).hybrid =>
          if common ⟨v,hh⟩ then (state s).register v else fresh l.val) =
        (fun l : AtNode (state s) (H.parents ⟨v,hh⟩).hybrid =>
          (fun owner : Copy => if common ⟨v,hh⟩ then (state s).register v else fresh owner) l.val)
        from rfl, full_coin_pulse_copy_location]
      rw [H.original_site ⟨v,hh⟩]
      simp only [nodeLocation, nodeDestination, dif_neg hr, dif_pos hh]
    · simp only [nodeCodeWithFresh, dif_neg hr, dif_neg hh]
      rw [ordinaryCode_copyLocation]
      simp only [nodeLocation, nodeDestination, dif_neg hr, dif_neg hh, ordinaryLocation,
        (defaultSelector N).target ⟨v,hr⟩]

/-- Actual deterministic current-owner patches commute for DISTINCT nodes:
their triggers are disjoint and their outputs are original edges/root, never
another node. No equal kernel or desired batch law is a premise. -/
theorem node_locations_commute (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool)
    (freshV freshW : Copy → Bool) (v w : V) (hvw : v ≠ w) (l : Copy) (old : Location V E) :
    nodeLocation N H common register freshV v l
        (nodeLocation N H common register freshW w l old) =
      nodeLocation N H common register freshW w l
        (nodeLocation N H common register freshV v l old) := by
  by_cases hv : old = .node v
  · have hw : old ≠ .node w := by
      intro he
      exact hvw (Location.node.inj (hv.symm.trans he))
    have hd := node_destination_not_node N H common register freshV v l w
    simp only [nodeLocation, if_neg hw, if_pos hv, if_neg hd]
  · by_cases hw : old = .node w
    · have hd := node_destination_not_node N H common register freshW w l v
      simp only [nodeLocation, if_neg hv, if_pos hw, if_neg hd]
    · simp only [nodeLocation, if_neg hv, if_neg hw]

/-- Pure conditional node-batch output is invariant under the ACTUAL two
carrier lists' permutation, with one fixed full-Copy row per original node.
This does not identify Finset.toList orders or reorder exits after entries. -/
theorem node_batch_location_permutation (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : V → Copy → Bool)
    (l : Copy) (old : Location V E) (vs ws : List V) (hperm : vs.Perm ws) :
    vs.foldl (fun place v => nodeLocation N H common register (fresh v) v l place) old =
      ws.foldl (fun place v => nodeLocation N H common register (fresh v) v l place) old := by
  letI : RightCommutative
      (fun place v => nodeLocation N H common register (fresh v) v l place) := ⟨by
    intro place v w
    by_cases hvw : v = w
    · subst w
      rfl
    · exact (node_locations_commute N H common register (fresh v) (fresh w)
        v w hvw l place).symm⟩
  exact hperm.foldl_eq old

/-- Before the PRIVATE original hybrid date, every actually scheduled node
is a retained original vertex. Removed h/r cannot enter a hidden tied batch. -/
theorem below_h_node_retained (C : Calendar N.graph) (a : ℝ)
    (ha : a < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid)
    (v : V) (hv : C.age v = a) :
    v ≠ (derivedBigon N hcut b hb hp).fragment.upper ∧
      v ≠ (derivedBigon N hcut b hb hp).fragment.parents.hybrid := by
  let A := derivedBigon N hcut b hb hp
  have hhr : C.age A.fragment.parents.hybrid < C.age A.fragment.upper := by
    have hh := C.edge_older A.fragment.parents.parent0
    rw [A.fragment.parents.target0,
      show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false] at hh
    exact hh
  refine ⟨?_, ?_⟩
  · intro he
    rw [he] at hv
    rw [hv] at hhr
    exact ha.asymm hhr
  · intro he
    rw [he] at hv
    rw [hv] at ha
    exact (lt_irrefl _) ha

/-- Every actual exiting occurrence below h is a retained ORIGINAL edge.
This excludes the child and both arms by their original source dates, and
the entry by its strictly older rootward source. -/
theorem below_h_exit_retained (C : Calendar N.graph) (a : ℝ)
    (ha : a < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid)
    (e : E) (he : C.age (N.graph.source e) = a) :
    e ∉ removedEdges N b (derivedBigon N hcut b hb hp) := by
  let A := derivedBigon N hcut b hb hp
  have order := boundary_original_private_age_order N hcut b hb hp C
  change C.age (N.graph.target A.child) < C.age A.fragment.parents.hybrid ∧
    C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
    C.age A.fragment.upper < C.age (N.graph.source A.entry) at order
  intro hm
  have hm : e = A.entry ∨ e = A.child ∨
      e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
    simpa only [removedEdges, Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact (ha.trans (order.2.1.trans order.2.2)).ne he.symm
  · have hd := he
    rw [A.child_source] at hd
    rw [hd] at ha
    exact (lt_irrefl _) ha
  · rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from
      A.fragment.arm_sources false] at he
    exact (ha.trans order.2.1).ne he.symm
  · rw [show N.graph.source A.fragment.parents.parent1 = A.fragment.upper from
      A.fragment.arm_sources true] at he
    exact (ha.trans order.2.1).ne he.symm

/-- New synthetic exit is rootward at u, NOT at the old child's source h.
It cannot be an additional event in a below-h tied batch. -/
theorem below_h_no_synthetic_exit (C : Calendar N.graph) (a : ℝ)
    (ha : a < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid) :
    (splicedCalendar N hcut b hb (derivedBigon N hcut b hb hp) C).age
      ((suppressedNetwork N hcut b hb hp).graph.source (.inr ())) ≠ a := by
  let A := derivedBigon N hcut b hb hp
  change C.age (N.graph.source A.entry) ≠ a
  have order := boundary_original_private_age_order N hcut b hb hp C
  exact (ha.trans (order.2.1.trans order.2.2)).ne.symm

theorem retained_node_date (C : Calendar N.graph)
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) :
    (splicedCalendar N hcut b hb (derivedBigon N hcut b hb hp) C).age v =
      C.age v.val := rfl

theorem retained_exit_date (C : Calendar N.graph)
    (e : RetainedEdge N b (derivedBigon N hcut b hb hp)) :
    (splicedCalendar N hcut b hb (derivedBigon N hcut b hb hp) C).age
      ((suppressedNetwork N hcut b hb hp).graph.source (.inl e)) =
      C.age (N.graph.source e.val) := rfl

/-- Conditional EXIT patches commute occurrence-wise. Distinct IDs remain
distinct even if their endpoint vertices coincide. Outputs are nodes and
therefore cannot trigger another edge exit. -/
theorem exit_locations_commute (e f : E) (hef : e ≠ f) (old : Location V E) :
    exitLocation N e (exitLocation N f old) =
      exitLocation N f (exitLocation N e old) := by
  by_cases he : old = .edge e
  · have hf : old ≠ .edge f := fun h => hef (Location.edge.inj (he.symm.trans h))
    simp only [exitLocation, if_neg hf, if_pos he]
    simp only [Location.node.injEq, reduceCtorEq, if_false]
  · by_cases hf : old = .edge f
    · simp only [exitLocation, if_neg he, if_pos hf]
      simp only [Location.node.injEq, reduceCtorEq, if_false]
    · simp only [exitLocation, if_neg he, if_neg hf]

theorem exit_batch_location_permutation (old : Location V E) (es fs : List E)
    (hperm : es.Perm fs) :
    es.foldl (fun place e => exitLocation N e place) old =
      fs.foldl (fun place e => exitLocation N e place) old := by
  letI : RightCommutative (fun place e => exitLocation N e place) := ⟨by
    intro place e f
    by_cases hef : e = f
    · subst f
      rfl
    · exact (exit_locations_commute N e f hef place).symm⟩
  exact hperm.foldl_eq old

/-- Any actual incoming occurrence at a retained vertex lies in the guarded
physical carrier: the protected child is retained as its OWN original phase,
while all other incoming IDs are literally outside the removed block. -/
noncomputable def guardedIncoming
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp))
    (e : {e : E // N.graph.target e = v.val}) : ChildGuardedEdge N hcut b hb hp :=
  ⟨e.val, by
    by_cases he : e.val = (derivedBigon N hcut b hb hp).child
    · exact Or.inr he
    · exact Or.inl (actual_in_edge_kept_of_ne_child N hcut b
        (derivedBigon N hcut b hb hp) v e.val e.property he)⟩

/-- G1's actual incoming occurrence map is EXACTLY the guarded phase edge
map, not a postulated rate/source casting operation. -/
theorem guarded_incoming_phase
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp))
    (e : {e : E // N.graph.target e = v.val}) :
    phaseEdge N hcut b hb hp (guardedIncoming N hcut b hb hp v e) =
      (actualInEdgeEquiv N hcut b (derivedBigon N hcut b hb hp) v e).val := by
  change phaseEdge N hcut b hb hp (guardedIncoming N hcut b hb hp v e) =
    inDestination N hcut b (derivedBigon N hcut b hb hp) v e
  by_cases he : e.val = (derivedBigon N hcut b hb hp).child
  · simp only [phaseEdge, guardedIncoming, he, dif_pos, inDestination]
  · simp only [phaseEdge, guardedIncoming, he, dif_neg, inDestination]

/-- The independently constructed ordinary selector is NOT assumed equal:
its unique actual incoming ID is derived from binary degree one and the G1
occurrence bijection. This includes old child d -> youngest new occurrence. -/
theorem ordinary_parent_orientation
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp))
    (hr : v.val ≠ N.root) (hh : ¬ N.graph.IsHybrid v.val) :
    (defaultSelector (suppressedNetwork N hcut b hb hp)).edge
        ⟨v, fun he => hr (congrArg Subtype.val he)⟩ =
      (actualInEdgeEquiv N hcut b (derivedBigon N hcut b hb hp) v
        ⟨(defaultSelector N).edge ⟨v.val,hr⟩, (defaultSelector N).target _⟩).val := by
  let R := suppressedNetwork N hcut b hb hp
  have hnr : v ≠ R.root := fun he => hr (congrArg Subtype.val he)
  have hnh : ¬R.graph.IsHybrid v :=
    fun he => hh ((retained_hybrid_iff N hcut b hb hp v).mp he)
  obtain ⟨f, _, hf⟩ := R.incoming_unique_of_indegree_one
    (nonhybrid_nonroot_indegree_one R v hnr hnh)
  exact (hf ((defaultSelector R).edge ⟨v,hnr⟩) ((defaultSelector R).target _)).trans
    (hf _ (actualInEdgeEquiv N hcut b (derivedBigon N hcut b hb hp) v
      ⟨(defaultSelector N).edge ⟨v.val,hr⟩, (defaultSelector N).target _⟩).property).symm

/-- A retained original EXIT commutes with both physical carrier embeddings.
The synthetic occurrence is absent below h (proved separately), so no old h
exit or future u exit is silently identified at a tied boundary. -/
noncomputable def guardedExit
    (e : RetainedEdge N b (derivedBigon N hcut b hb hp))
    (q : ChildGuardedLocation N hcut b hb hp) : ChildGuardedLocation N hcut b hb hp :=
  if q = .edge ⟨e.val, Or.inl e.property⟩ then
    .node (retainedSource N hcut b (derivedBigon N hcut b hb hp) e) else q

theorem original_guarded_exit_square
    (e : RetainedEdge N b (derivedBigon N hcut b hb hp))
    (q : ChildGuardedLocation N hcut b hb hp) :
    exitLocation N e.val (intoOriginalChildGuarded N hcut b hb hp q) =
      intoOriginalChildGuarded N hcut b hb hp (guardedExit N hcut b hb hp e q) := by
  let qedge : ChildGuardedLocation N hcut b hb hp := .edge ⟨e.val, Or.inl e.property⟩
  have he : intoOriginalChildGuarded N hcut b hb hp q = .edge e.val ↔ q = qedge := by
    constructor
    · intro h
      exact (intoOriginalChildGuarded N hcut b hb hp).injective h
    · rintro rfl
      rfl
  by_cases hq : q = qedge
  · subst q
    simp [exitLocation, guardedExit, qedge, intoOriginalChildGuarded, locationEmbedding,
      retainedSource]
  · rw [exitLocation, if_neg (he.not.mpr hq), guardedExit, if_neg hq]

theorem constructed_guarded_exit_square
    (e : RetainedEdge N b (derivedBigon N hcut b hb hp))
    (q : ChildGuardedLocation N hcut b hb hp) :
    exitLocation (suppressedNetwork N hcut b hb hp) (.inl e)
        (intoBoundaryPhase N hcut b hb hp q) =
      intoBoundaryPhase N hcut b hb hp (guardedExit N hcut b hb hp e q) := by
  let qedge : ChildGuardedLocation N hcut b hb hp := .edge ⟨e.val, Or.inl e.property⟩
  have he : intoBoundaryPhase N hcut b hb hp q = .edge (.inl e) ↔ q = qedge := by
    constructor
    · intro h
      apply boundary_phase_injective N hcut b hb hp
      exact h.trans (retained_edge_phase N hcut b hb hp e).symm
    · rintro rfl
      exact retained_edge_phase N hcut b hb hp e
  by_cases hq : q = qedge
  · subst q
    rw [exitLocation, if_pos (he.mpr rfl), guardedExit, if_pos rfl]
    rfl
  · rw [exitLocation, if_neg (he.not.mpr hq), guardedExit, if_neg hq]

noncomputable def guardedNodeDestination (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) (l : Copy) :
    ChildGuardedLocation N hcut b hb hp :=
  if hr : v.val = N.root then .rootPopulation (retainedRoot N b hb (derivedBigon N hcut b hb hp))
  else if hh : N.graph.IsHybrid v.val then
    .edge (guardedIncoming N hcut b hb hp v
      ⟨(H.parents ⟨v.val,hh⟩).parent (if common ⟨v.val,hh⟩ then register v.val else fresh l),
        registry_parent_target N H _ _⟩)
  else .edge (guardedIncoming N hcut b hb hp v
    ⟨(defaultSelector N).edge ⟨v.val,hr⟩, (defaultSelector N).target _⟩)

theorem original_guarded_node_destination (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) (l : Copy) :
    nodeDestination N H common register fresh v.val l =
      intoOriginalChildGuarded N hcut b hb hp
        (guardedNodeDestination N hcut b hb hp H common register fresh v l) := by
  by_cases hr : v.val = N.root
  · simp only [nodeDestination, guardedNodeDestination, dif_pos hr]
    rfl
  · by_cases hh : N.graph.IsHybrid v.val
    · simp only [nodeDestination, guardedNodeDestination, dif_neg hr, dif_pos hh]
      rfl
    · simp only [nodeDestination, guardedNodeDestination, dif_neg hr, dif_neg hh]
      rfl

/-- Every retained ROOT/COMMON/INDEPENDENT/ordinary node uses the transported
ORIGINAL parent orientation, register slot and current-owner bit. -/
theorem constructed_guarded_node_destination (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) (l : Copy) :
    nodeDestination (suppressedNetwork N hcut b hb hp) (retainedRegistry N hcut b hb hp H)
        (retainedCommon N hcut b hb hp common) (restrictRegister N hcut b hb hp register) fresh v l =
      intoBoundaryPhase N hcut b hb hp
        (guardedNodeDestination N hcut b hb hp H common register fresh v l) := by
  by_cases hr : v.val = N.root
  · have hn : v = (suppressedNetwork N hcut b hb hp).root := Subtype.ext hr
    simp only [nodeDestination, guardedNodeDestination, dif_pos hr, dif_pos hn]
    rfl
  · have hn : v ≠ (suppressedNetwork N hcut b hb hp).root :=
      fun h => hr (congrArg Subtype.val h)
    by_cases hh : N.graph.IsHybrid v.val
    · have hnh := (retained_hybrid_iff N hcut b hb hp v).mpr hh
      simp only [nodeDestination, guardedNodeDestination, dif_neg hr, dif_neg hn,
        dif_pos hh, dif_pos hnh, retainedCommon, originalHybrid, restrictRegister,
        intoBoundaryPhase]
      rw [retained_parent_orientation]
      exact congrArg Location.edge (guarded_incoming_phase N hcut b hb hp v _).symm
    · have hnh : ¬(suppressedNetwork N hcut b hb hp).graph.IsHybrid v :=
        fun h => hh ((retained_hybrid_iff N hcut b hb hp v).mp h)
      simp only [nodeDestination, guardedNodeDestination, dif_neg hr, dif_neg hn,
        dif_neg hh, dif_neg hnh, intoBoundaryPhase]
      rw [ordinary_parent_orientation N hcut b hb hp v hr hh]
      exact congrArg Location.edge (guarded_incoming_phase N hcut b hb hp v _).symm

noncomputable def guardedNode (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) (l : Copy)
    (q : ChildGuardedLocation N hcut b hb hp) : ChildGuardedLocation N hcut b hb hp :=
  if q = .node v then guardedNodeDestination N hcut b hb hp H common register fresh v l else q

theorem original_guarded_node_square (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) (l : Copy)
    (q : ChildGuardedLocation N hcut b hb hp) :
    nodeLocation N H common register fresh v.val l
        (intoOriginalChildGuarded N hcut b hb hp q) =
      intoOriginalChildGuarded N hcut b hb hp
        (guardedNode N hcut b hb hp H common register fresh v l q) := by
  have he : intoOriginalChildGuarded N hcut b hb hp q = .node v.val ↔ q = .node v := by
    constructor
    · intro h
      exact (intoOriginalChildGuarded N hcut b hb hp).injective h
    · rintro rfl
      rfl
  by_cases hq : q = .node v
  · rw [nodeLocation, if_pos (he.mpr hq), guardedNode, if_pos hq]
    exact original_guarded_node_destination N hcut b hb hp H common register fresh v l
  · rw [nodeLocation, if_neg (he.not.mpr hq), guardedNode, if_neg hq]

theorem constructed_guarded_node_square (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (register : V → Bool) (fresh : Copy → Bool)
    (v : SplicedVertex N b (derivedBigon N hcut b hb hp)) (l : Copy)
    (q : ChildGuardedLocation N hcut b hb hp) :
    nodeLocation (suppressedNetwork N hcut b hb hp) (retainedRegistry N hcut b hb hp H)
        (retainedCommon N hcut b hb hp common) (restrictRegister N hcut b hb hp register)
        fresh v l (intoBoundaryPhase N hcut b hb hp q) =
      intoBoundaryPhase N hcut b hb hp
        (guardedNode N hcut b hb hp H common register fresh v l q) := by
  have he : intoBoundaryPhase N hcut b hb hp q = .node v ↔ q = .node v := by
    constructor
    · intro h
      exact boundary_phase_injective N hcut b hb hp h
    · rintro rfl
      rfl
  by_cases hq : q = .node v
  · rw [nodeLocation, if_pos (he.mpr hq), guardedNode, if_pos hq]
    exact constructed_guarded_node_destination N hcut b hb hp H common register fresh v l
  · rw [nodeLocation, if_neg (he.not.mpr hq), guardedNode, if_neg hq]

#print axioms retained_hybrid_iff
#print axioms retainedParents
#print axioms retained_parent_orientation
#print axioms actual_outside_coin_marginal
#print axioms actual_retained_seed_product
#print axioms actual_retained_register_pmf
#print axioms initial_codes_related
#print axioms natural_initial_constructed_marginal
#print axioms natural_initial_pair_related
#print axioms node_destination_not_node
#print axioms full_coin_current_owner_pmf
#print axioms node_fresh_row_actual_kernel
#print axioms full_coin_pulse_copy_location
#print axioms actual_node_fresh_location
#print axioms node_locations_commute
#print axioms node_batch_location_permutation
#print axioms below_h_node_retained
#print axioms below_h_exit_retained
#print axioms below_h_no_synthetic_exit
#print axioms exit_locations_commute
#print axioms exit_batch_location_permutation
#print axioms guarded_incoming_phase
#print axioms ordinary_parent_orientation
#print axioms original_guarded_exit_square
#print axioms constructed_guarded_exit_square
#print axioms original_guarded_node_destination
#print axioms constructed_guarded_node_destination
#print axioms original_guarded_node_square
#print axioms constructed_guarded_node_square

end UnifiedLean.G6.RetainedPrefixInterfaces
