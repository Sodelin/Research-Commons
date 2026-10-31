import ResearchCommons.MSCI.JC69ActivatedPrefix
import ResearchCommons.MSCI.JC69EndpointWeight

/-! Source-supported active-population observation bound. UNCOMPILED.
Dot (OpenAI), 31 October 2026. Original Copy labels are relabelled by an
explicit equivalence, never replaced by replicated sites. No total indexing
of impossible locations and no extra root population color are assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69SupportedStateBound
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.NativeParentRouting
open ResearchCommons.MSCI.JC69ActivatedPrefix ResearchCommons.MSCI.JC69CurrentPartition
open ResearchCommons.MSCI.JC69EndpointWeight
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Existing original rootedness and strict calendar give the latest root. -/
theorem actual_root_latest (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) :
    C.age v ≤ C.age N.root := C.age_le_of_directed (N.rooted v)

/-- At the younger endpoint of a NONFINAL completed date block, all activated
copies occupy actually active edges. No choice of an empty-epoch midpoint. -/
theorem actual_initialized_prefix_active (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hactivated : c ≤ prefixDate N C k) (hbefore : prefixDate N C k < C.age N.root)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (initializedPrefix N C H gamma common k)
      (initialCode N sample register)).support) :
    ∀ x : Copy, ∃ e : E, copyLocation (state d) x = .edge e ∧ C.Active (prefixDate N C k) e := by
  have hs := actual_initialized_prefix_support N C sample register H gamma common r c hc k hd
  have hn := actual_initialized_prefix_no_nodes N C sample register H gamma common r c hc k hactivated hd
  intro x
  have hr := hs.1.1.1 x
  cases he : copyLocation (state d) x with
  | node v => exact False.elim (hn x v he)
  | edge e =>
      rw [he] at hr
      exact ⟨e,rfl,hr.1,hs.1.1.2 x e he⟩
  | rootPopulation v =>
      rw [he] at hr
      exact False.elim ((not_le_of_gt hbefore) hr.2)

/-- This finite carrier is physically present edges only, not all graph IDs. -/
def activeLocations (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) :
    Finset (Location V E) :=
  (Finset.univ.filter (C.Active a)).image Location.edge

lemma mem_activeLocations (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (l : Location V E) : l ∈ activeLocations N C a ↔ ∃ e, l = .edge e ∧ C.Active a e := by
  simp only [activeLocations,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,rfl⟩; exact ⟨e,rfl,he⟩
  · rintro ⟨e,rfl,he⟩; exact ⟨e,he,rfl⟩

lemma active_locations_card (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) :
    (activeLocations N C a).card = (Finset.univ.filter (C.Active a)).card := by
  apply Finset.card_image_of_injective
  intro e f h
  exact Location.edge.inj h

/-- Receiver restricted to actual admitted observations and locations in A.
It may contain more than the actual source support, giving a valid overcount. -/
def SupportedObservation (N : RootedBinary V E X) (sample : Copy → X)
    (A : Finset (Location V E)) :=
  {o : BlockPopulationObservation Copy V E //
    (∃ s : Code N sample, observeCode N s = o) ∧ ∀ x : Copy, o.2 x ∈ A}

instance supportedObservationFintype (N : RootedBinary V E X) (sample : Copy → X)
    (A : Finset (Location V E)) : Fintype (SupportedObservation N sample A) := by
  classical
  apply Fintype.ofInjective (fun o : SupportedObservation N sample A => Classical.choose o.property.1)
  intro x y h
  apply Subtype.ext
  exact (Classical.choose_spec x.property.1).symm.trans
    ((congrArg (observeCode N) h).trans (Classical.choose_spec y.property.1))

def representative (N : RootedBinary V E X) {sample : Copy → X} {A : Finset (Location V E)}
    (o : SupportedObservation N sample A) : Code N sample := Classical.choose o.property.1

lemma representative_observation (N : RootedBinary V E X) {sample : Copy → X}
    {A : Finset (Location V E)} (o : SupportedObservation N sample A) :
    observeCode N (representative N o) = o.val := Classical.choose_spec o.property.1

/-- An explicit original-label equivalence transports partitions. -/
def relabelFinsets {n : ℕ} (labels : Copy ≃ Fin n) : Finset Copy ≃o Finset (Fin n) where
  toEquiv := labels.finsetCongr
  map_rel_iff' := by intro s t; exact Finset.map_subset_map

def relabelPartition {n : ℕ} (labels : Copy ≃ Fin n)
    (p : Finpartition (Finset.univ : Finset Copy)) : Finpartition (Finset.univ : Finset (Fin n)) :=
  (p.map (relabelFinsets labels)).copy (by simp [relabelFinsets])

lemma relabelPartition_injective {n : ℕ} (labels : Copy ≃ Fin n) :
    Function.Injective (relabelPartition labels) := by
  intro p q h
  apply Finpartition.ext
  have hh := congrArg Finpartition.parts h
  exact Finset.map_injective (relabelFinsets labels).toEmbedding hh

/-- Population indexing is required only on A. No default for impossible
locations, and in particular no hidden P>0 assumption, is needed. -/
def encodeObservation (N : RootedBinary V E X) {sample : Copy → X}
    {A : Finset (Location V E)} {n P : ℕ} (labels : Copy ≃ Fin n) (colors : A ↪ Fin P)
    (o : SupportedObservation N sample A) : StateEnvelope n P :=
  (relabelPartition labels (currentPartition (state (representative N o))
      (representative N o).property.forest),
    fun x => colors ⟨o.val.2 (labels.symm x),o.property.2 (labels.symm x)⟩)

lemma encodeObservation_injective (N : RootedBinary V E X) {sample : Copy → X}
    {A : Finset (Location V E)} {n P : ℕ} (labels : Copy ≃ Fin n) (colors : A ↪ Fin P) :
    Function.Injective (encodeObservation N (sample:=sample) labels colors) := by
  intro o p h
  apply Subtype.ext
  apply Prod.ext
  · have hp := relabelPartition_injective labels (congrArg Prod.fst h)
    have hb := congrArg Finpartition.parts hp
    have ho := congrArg Prod.fst (representative_observation N o)
    have ht := congrArg Prod.fst (representative_observation N p)
    exact ho.symm.trans (hb.trans ht)
  · funext x
    have he := congrFun (congrArg Prod.snd h) (labels x)
    have hv := congrArg Subtype.val (colors.injective he)
    simpa only [Equiv.symm_apply_apply] using hv

def populationColors {A : Finset (Location V E)} {P : ℕ} (hP : A.card ≤ P) : A ↪ Fin P where
  toFun x := ⟨(Fintype.equivFin A x).val,lt_of_lt_of_le (Fintype.equivFin A x).isLt (by simpa using hP)⟩
  inj' := by
    intro x y h
    apply (Fintype.equivFin A).injective
    apply Fin.ext
    exact congrArg (fun z : Fin P => z.val) h

/-- Exact original-copy Bell envelope. This counts observations, not Codes,
register assignments or ordered genealogy shapes. -/
theorem supported_observation_card (N : RootedBinary V E X) (sample : Copy → X)
    (A : Finset (Location V E)) (P : ℕ) (hP : A.card ≤ P) :
    Fintype.card (SupportedObservation N sample A) ≤
      BellCount (Fintype.card Copy) * P ^ Fintype.card Copy := by
  have hi := encodeObservation_injective N (sample:=sample) (Fintype.equivFin Copy) (populationColors hP)
  exact (Fintype.card_le_of_injective _ hi).trans_eq
    (state_envelope_card (Fintype.card Copy) P)

theorem supported_active_observation_card (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (a : ℝ) (P : ℕ)
    (hP : (Finset.univ.filter (C.Active a)).card ≤ P) :
    Fintype.card (SupportedObservation N sample (activeLocations N C a)) ≤
      BellCount (Fintype.card Copy) * P ^ Fintype.card Copy := by
  apply supported_observation_card N sample _ P
  rw [active_locations_card]
  exact hP

/-- Every actual activated nonfinal prefix observation enters the SAME
bank-independent, site-count-independent physically active carrier. -/
theorem actual_prefix_observation_supported (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hactivated : c ≤ prefixDate N C k) (hbefore : prefixDate N C k < C.age N.root)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (initializedPrefix N C H gamma common k)
      (initialCode N sample register)).support) :
    (∃ s : Code N sample, observeCode N s = observeCode N d) ∧
      ∀ x : Copy, (observeCode N d).2 x ∈ activeLocations N C (prefixDate N C k) := by
  refine ⟨⟨d,rfl⟩,?_⟩
  intro x
  apply (mem_activeLocations N C _ _).mpr
  exact actual_initialized_prefix_active N C sample register H gamma common r c hc k hactivated hbefore hd x

#print axioms actual_root_latest
#print axioms actual_initialized_prefix_active
#print axioms encodeObservation_injective
#print axioms supported_observation_card
#print axioms supported_active_observation_card
#print axioms actual_prefix_observation_supported
end ResearchCommons.MSCI.JC69SupportedStateBound
