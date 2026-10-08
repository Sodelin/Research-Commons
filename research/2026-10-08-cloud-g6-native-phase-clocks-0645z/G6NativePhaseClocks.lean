import G6BoundaryPhaseRelation
import UnifiedLean.Source.SourceActualHoldingClocks
import G2HistoryResidualAttachment
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Actual guarded current-pair catalogue and JOINT native clock-product law.
Cloud Sol delegated G6 structural/source lane, 8 October 2026, 06:45 UTC.
Original source/catalogue/clock providers: Dot; phase relation Cloud Sol.
Compiler UNCHECKED; outside the sole179. No provider/input is changed.

The constructed graph uses the original child rate only in this YOUNGEST
guarded phase. Its spine's future word law is not a scalar ordinary-edge law.
SourceValid boundary snapshots and actual conditional clocks are proved; an
independently naturally initialized second WHOLE prefix law and recursive
marked outside chronology remain separate consumers. No desired law field,
sourceStep/global-normalizer equality or re-coined old COMMON bit is used.
-/

namespace UnifiedLean.G6.NativePhaseClocks
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open GProgram.SourceForestKingmanPopulationProjection
open G1BigonSpliceGraph G1BigonFootprint
open G1SplicedSourceAdmission
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.G6.OriginalSpliceAdapter UnifiedLean.G6.SpineBoundaryCarrier
open UnifiedLean.G6.ProtectedChildCarrier UnifiedLean.G6.BoundaryPhaseRelation
open GProgram.G2.LiteralMarkedClockTrace
open scoped Classical BigOperators

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable (N : RootedBinary V E X)
variable (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
variable (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
variable (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)

/-- No private-arm/entry site is inserted into this first connector phase. -/
noncomputable def phaseEdgeEquiv : ChildGuardedEdge N hcut b hb hp ≃
    SplicedEdge N b (derivedBigon N hcut b hb hp) where
  toFun := phaseEdge N hcut b hb hp
  invFun
    | .inl e => ⟨e.val, Or.inl e.property⟩
    | .inr _ => protectedChild N hcut b hb hp
  left_inv e := by
    by_cases he : e.val = (derivedBigon N hcut b hb hp).child
    · apply Subtype.ext
      simpa only [phaseEdge, dif_pos he, protectedChild] using he.symm
    · apply Subtype.ext
      simp [phaseEdge, he]
  right_inv e := by
    cases e with
    | inl e =>
        have he : e.val ≠ (derivedBigon N hcut b hb hp).child := by
          intro hh
          apply e.property
          rw [hh]
          simp [removedEdges]
        simp [phaseEdge, he]
    | inr u =>
        cases u
        simp [phaseEdge, protectedChild]

noncomputable def oldSite (j : Option (ChildGuardedEdge N hcut b hb hp)) : Option E :=
  j.map Subtype.val

noncomputable def newSite (j : Option (ChildGuardedEdge N hcut b hb hp)) :
    Option (SplicedEdge N b (derivedBigon N hcut b hb hp)) :=
  j.map (phaseEdge N hcut b hb hp)

noncomputable def siteInverse (j : Option (SplicedEdge N b (derivedBigon N hcut b hb hp))) :
    Option (ChildGuardedEdge N hcut b hb hp) := j.map (phaseEdgeEquiv N hcut b hb hp).symm

theorem old_site_injective : Function.Injective (oldSite N hcut b hb hp) := by
  intro a c he
  cases a with
  | none =>
      cases c with
      | none => rfl
      | some c => cases he
  | some a =>
      cases c with
      | none => cases he
      | some c => exact congrArg some (Subtype.ext (Option.some.inj he))

theorem site_inverse_left (j : Option (ChildGuardedEdge N hcut b hb hp)) :
    siteInverse N hcut b hb hp (newSite N hcut b hb hp j) = j := by
  cases j with
  | none => rfl
  | some e =>
      change some ((phaseEdgeEquiv N hcut b hb hp).symm
        ((phaseEdgeEquiv N hcut b hb hp) e)) = some e
      rw [Equiv.symm_apply_apply]

theorem site_inverse_right (j : Option (SplicedEdge N b (derivedBigon N hcut b hb hp))) :
    newSite N hcut b hb hp (siteInverse N hcut b hb hp j) = j := by
  cases j with
  | none => rfl
  | some e =>
      change some ((phaseEdgeEquiv N hcut b hb hp)
        ((phaseEdgeEquiv N hcut b hb hp).symm e)) = some e
      rw [Equiv.apply_symm_apply]

noncomputable def guardedPlace (j : Option (ChildGuardedEdge N hcut b hb hp)) :
    ChildGuardedLocation N hcut b hb hp :=
  match j with
  | none => .rootPopulation (suppressedNetwork N hcut b hb hp).root
  | some e => .edge e

theorem original_guarded_place (j : Option (ChildGuardedEdge N hcut b hb hp)) :
    intoOriginalChildGuarded N hcut b hb hp (guardedPlace N hcut b hb hp j) =
      originalPlace N (oldSite N hcut b hb hp j) := by cases j <;> rfl

theorem constructed_guarded_place (j : Option (ChildGuardedEdge N hcut b hb hp)) :
    intoBoundaryPhase N hcut b hb hp (guardedPlace N hcut b hb hp j) =
      originalPlace (suppressedNetwork N hcut b hb hp) (newSite N hcut b hb hp j) := by
  cases j <;> rfl

theorem related_place_iff {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t)
    (j : Option (ChildGuardedEdge N hcut b hb hp)) (x : Copy) :
    copyLocation (state s) x = originalPlace N (oldSite N hcut b hb hp j) ↔
      copyLocation (state t) x =
        originalPlace (suppressedNetwork N hcut b hb hp) (newSite N hcut b hb hp j) := by
  obtain ⟨q, ho, hn⟩ := h.location x
  rw [← ho, ← hn, ← original_guarded_place, ← constructed_guarded_place]
  constructor
  · intro he
    rw [(intoOriginalChildGuarded N hcut b hb hp).injective he]
  · intro he
    rw [boundary_phase_injective N hcut b hb hp he]

theorem actual_population_catalogue {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (j : Option (ChildGuardedEdge N hcut b hb hp)) :
    populationRoots (state s) (originalPlace N (oldSite N hcut b hb hp j)) =
      populationRoots (state t)
        (originalPlace (suppressedNetwork N hcut b hb hp) (newSite N hcut b hb hp j)) := by
  ext x
  by_cases hx : x ∈ (state s).live
  · have ht : x ∈ (state t).live := by rw [h.live]; exact hx
    have ho : copyLocation (state s) x = (state s).location x := by
      unfold copyLocation; rw [s.property.forest.representative x hx]
    have hn : copyLocation (state t) x = (state t).location x := by
      unfold copyLocation; rw [t.property.forest.representative x ht]
    simpa only [populationRoots, Finset.mem_filter, hx, ht, true_and, ho, hn] using
      related_place_iff N hcut b hb hp s t h j x
  · have ht : x ∉ (state t).live := by rw [h.live]; exact hx
    simp only [populationRoots, Finset.mem_filter, hx, ht, false_and]

/-- Calendar support of the second actual conditional clock row is DERIVED.
The original child phase's upper date h is below new spine's upper date u;
this supports the same short epoch, not the original whole hidden span law. -/
theorem phase_epoch_compatible {sample : Copy → X}
    (C : Calendar N.graph) (a until : ℝ)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (hs : EpochCompatible N C a until (state s)) :
    EpochCompatible (suppressedNetwork N hcut b hb hp)
      (splicedCalendar N hcut b hb (derivedBigon N hcut b hb hp) C) a until (state t) := by
  let A := derivedBigon N hcut b hb hp
  have hage := boundary_original_private_age_order N hcut b hb hp C
  change C.age (N.graph.target A.child) < C.age A.fragment.parents.hybrid ∧
    C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
    C.age A.fragment.upper < C.age (N.graph.source A.entry) at hage
  intro x
  obtain ⟨q, ho, hn⟩ := h.location x
  have hd := hs x
  rw [← ho] at hd
  rw [← hn]
  cases q with
  | node v => exact hd
  | edge e =>
      change C.age (N.graph.target e.val) ≤ a ∧ until ≤ C.age (N.graph.source e.val) at hd
      by_cases he : e.val = A.child
      · rw [he, A.child_source] at hd
        have hu : until ≤ C.age (N.graph.source A.entry) :=
          hd.2.trans (hage.2.1.trans hage.2.2).le
        simpa [intoBoundaryPhase, phaseEdge, he, A, LocationInEpoch,
          suppressedNetwork, splicedNetwork, spliceGraph, splicedCalendar,
          descendantInterface, rootwardInterface] using And.intro hd.1 hu
      · simpa [intoBoundaryPhase, phaseEdge, he, A, LocationInEpoch,
          suppressedNetwork, splicedNetwork, spliceGraph, splicedCalendar,
          retainedSource, retainedTarget] using hd
  | rootPopulation v => exact ⟨Subtype.ext hd.1, hd.2⟩

/-- Every eligible original pair is at an ACTUAL admitted guarded site.
Empty/unoccupied private populations cannot create fictitious clock choices. -/
theorem actual_choice_site_exists {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) (p : Choice N s) :
    ∃ j : Option (ChildGuardedEdge N hcut b hb hp), oldSite N hcut b hb hp j = p.1 := by
  cases hi : p.1 with
  | none => exact ⟨none, rfl⟩
  | some e =>
      have ha := (Finset.mem_filter.mp (Finset.mem_offDiag.mp p.2.property).1)
      have hl : copyLocation (state s) p.2.val.1 = .edge e := by
        unfold copyLocation
        rw [s.property.forest.representative _ ha.1]
        simpa [hi, originalPlace] using ha.2
      obtain ⟨q, hq⟩ := hs p.2.val.1
      rw [hl] at hq
      cases q with
      | node v => cases hq
      | edge a =>
          have he : a.val = e := Location.edge.inj hq
          exact ⟨some a, congrArg some he⟩
      | rootPopulation v => cases hq

noncomputable def choiceSite {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (p : Choice N s) :
    Option (ChildGuardedEdge N hcut b hb hp) :=
  Classical.choose (actual_choice_site_exists N hcut b hb hp s
    (fun x => by obtain ⟨q, ho, _⟩ := h.location x; exact ⟨q, ho⟩) p)

theorem choice_site_spec {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (p : Choice N s) :
    oldSite N hcut b hb hp (choiceSite N hcut b hb hp s t h p) = p.1 :=
  Classical.choose_spec (actual_choice_site_exists N hcut b hb hp s
    (fun x => by obtain ⟨q, ho, _⟩ := h.location x; exact ⟨q, ho⟩) p)

noncomputable def choiceForward {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (p : Choice N s) :
    Choice (suppressedNetwork N hcut b hb hp) t :=
  ⟨newSite N hcut b hb hp (choiceSite N hcut b hb hp s t h p), ⟨p.2.val, by
    rw [← actual_population_catalogue N hcut b hb hp s t h,
      choice_site_spec N hcut b hb hp s t h p]
    exact p.2.property⟩⟩

noncomputable def choiceReverse {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t)
    (p : Choice (suppressedNetwork N hcut b hb hp) t) : Choice N s :=
  ⟨oldSite N hcut b hb hp (siteInverse N hcut b hb hp p.1), ⟨p.2.val, by
    rw [actual_population_catalogue N hcut b hb hp s t h, site_inverse_right]
    exact p.2.property⟩⟩

private theorem choice_ext {sample : Copy → X} (s : Code N sample) (p q : Choice N s)
    (hi : p.1 = q.1) (hab : p.2.val = q.2.val) : p = q := by
  cases p with
  | mk i p =>
      cases q with
      | mk j q =>
          cases hi
          exact congrArg (Sigma.mk i) (Subtype.ext hab)

/-- All original CURRENT operands and BOTH ordered orientations are retained.
Only the physical youngest-population phase name differs. -/
noncomputable def actualChoiceEquiv {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    Choice N s ≃ Choice (suppressedNetwork N hcut b hb hp) t where
  toFun := choiceForward N hcut b hb hp s t h
  invFun := choiceReverse N hcut b hb hp s t h
  left_inv p := by
    apply choice_ext N s
    · change oldSite N hcut b hb hp
        (siteInverse N hcut b hb hp (newSite N hcut b hb hp
          (choiceSite N hcut b hb hp s t h p))) = p.1
      rw [site_inverse_left, choice_site_spec]
    · rfl
  right_inv p := by
    apply choice_ext (suppressedNetwork N hcut b hb hp) t
    · have he : choiceSite N hcut b hb hp s t h
          (choiceReverse N hcut b hb hp s t h p) = siteInverse N hcut b hb hp p.1 := by
        apply old_site_injective N hcut b hb hp
        exact choice_site_spec N hcut b hb hp s t h _
      change newSite N hcut b hb hp (choiceSite N hcut b hb hp s t h
        (choiceReverse N hcut b hb hp s t h p)) = p.1
      rw [he, site_inverse_right]
    · rfl

/-- A POSITIVE actual constant bank on the admitted constructed graph, used
ONLY before h. Retained/root rates are literal old rates; its new youngest
edge has old child's rate. It does not model original arm/entry phases. -/
noncomputable def youngestPhaseRates (r : PositivePairRates E) :
    PositivePairRates (SplicedEdge N b (derivedBigon N hcut b hb hp)) where
  edge
    | .inl e => r.edge e.val
    | .inr _ => r.edge (derivedBigon N hcut b hb hp).child
  edge_pos e := by cases e with
    | inl e => exact r.edge_pos e.val
    | inr _ => exact r.edge_pos _
  ancestral := r.ancestral
  ancestral_pos := r.ancestral_pos

theorem actual_guarded_site_rate (r : PositivePairRates E)
    (j : Option (ChildGuardedEdge N hcut b hb hp)) :
    pairRate r (oldSite N hcut b hb hp j) =
      pairRate (youngestPhaseRates N hcut b hb hp r) (newSite N hcut b hb hp j) := by
  cases j with
  | none => rfl
  | some e =>
      by_cases he : e.val = (derivedBigon N hcut b hb hp).child
      · simp [oldSite, newSite, pairRate, phaseEdge, he, youngestPhaseRates]
      · simp [oldSite, newSite, pairRate, phaseEdge, he, youngestPhaseRates]

theorem actual_choice_rate {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (p : Choice N s) :
    choiceRate N r s p =
      choiceRate (suppressedNetwork N hcut b hb hp)
        (youngestPhaseRates N hcut b hb hp r) t (actualChoiceEquiv N hcut b hb hp s t h p) := by
  change pairRate r p.1 / 2 = pairRate (youngestPhaseRates N hcut b hb hp r)
    (newSite N hcut b hb hp (choiceSite N hcut b hb hp s t h p)) / 2
  rw [← choice_site_spec N hcut b hb hp s t h p]
  rw [actual_guarded_site_rate]

theorem actual_total_rate {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    totalRate N r s = totalRate (suppressedNetwork N hcut b hb hp)
      (youngestPhaseRates N hcut b hb hp r) t := by
  unfold totalRate
  calc
    _ = ∑ p : Choice N s, choiceRate (suppressedNetwork N hcut b hb hp)
        (youngestPhaseRates N hcut b hb hp r) t (actualChoiceEquiv N hcut b hb hp s t h p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact actual_choice_rate N hcut b hb hp r s t h p
    _ = _ := (actualChoiceEquiv N hcut b hb hp s t h).sum_comp _

/-- The ENTIRE native CURRENT clock product, including every outside clock,
is transported to the second graph's own actual conditional native product.
This is not a desired coupling field or a selected pair marginal equality. -/
theorem actual_joint_clock_product {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    (currentPairClockMeasure N r s).map
      (MeasurableEquiv.piCongrLeft (fun _ : Choice (suppressedNetwork N hcut b hb hp) t => ℝ)
        (actualChoiceEquiv N hcut b hb hp s t h)) =
      currentPairClockMeasure (suppressedNetwork N hcut b hb hp)
        (youngestPhaseRates N hcut b hb hp r) t := by
  let mu : Choice (suppressedNetwork N hcut b hb hp) t → Measure ℝ :=
    fun p => expMeasure (choiceRate (suppressedNetwork N hcut b hb hp)
      (youngestPhaseRates N hcut b hb hp r) t p)
  letI : ∀ p, IsProbabilityMeasure (mu p) := fun p =>
    isProbabilityMeasure_expMeasure
      (div_pos (pairRate_pos (youngestPhaseRates N hcut b hb hp r) p.1) (by norm_num))
  have hr : (fun p : Choice N s => expMeasure (choiceRate N r s p)) =
      fun p => mu (actualChoiceEquiv N hcut b hb hp s t h p) := by
    funext p
    rw [actual_choice_rate N hcut b hb hp r s t h p]
  change (Measure.pi (fun p => expMeasure (choiceRate N r s p))).map _ = Measure.pi mu
  rw [hr]
  exact Measure.pi_map_piCongrLeft (actualChoiceEquiv N hcut b hb hp s t h) mu

/-- Current holding clocks depend on actual live/population operands, not a
latent register slot. This is not independence from an arbitrary exposed past;
natural seed/past independence still requires the original causal guard proof.
The current Choice types are definitionally the same under register erasure. -/
theorem current_clocks_private_register_erasure {sample : Copy → X}
    (P : Finset V) (r : PositivePairRates E) (s : Code N sample) :
    currentPairClockMeasure N r (UnifiedLean.G6.PrivateRegisterErasure.erasePrivateCode N P s) =
      currentPairClockMeasure N r s := rfl

/-- The actual original natural initializer/calendar discharges the relation
premise for this native-law comparison. The second source is evaluated at the
derived guarded boundary snapshot, not an assumed independently initialized
prefix marginal. Every conditional outside CURRENT clock is retained jointly. -/
theorem actual_natural_guard_joint_clocks
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (guard : ℝ)
    (hlower : C.age (N.graph.target (derivedBigon N hcut b hb hp).child) ≤ guard)
    (hupper : guard < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid)
    (hgap : ∀ v : V, C.age (N.graph.target (derivedBigon N hcut b hb hp).child) < C.age v →
      guard ≤ C.age v)
    {s : Code N sample}
    (hs : s ∈ (naturalGuardPhaseLaw N hcut b hb hp C sample H p common r guard).support) :
    (currentPairClockMeasure N r s).map
      (MeasurableEquiv.piCongrLeft
        (fun _ : Choice (suppressedNetwork N hcut b hb hp) (phaseLift N hcut b hb hp s) => ℝ)
        (actualChoiceEquiv N hcut b hb hp s (phaseLift N hcut b hb hp s)
          (actual_natural_guard_phase_related N hcut b hb hp C sample H p common r guard
            hlower hupper hgap hs))) =
      currentPairClockMeasure (suppressedNetwork N hcut b hb hp)
        (youngestPhaseRates N hcut b hb hp r) (phaseLift N hcut b hb hp s) :=
  actual_joint_clock_product N hcut b hb hp r s (phaseLift N hcut b hb hp s)
    (actual_natural_guard_phase_related N hcut b hb hp C sample H p common r guard
      hlower hupper hgap hs)

/-- A full-cap ACTUAL marked epoch-past fibre, including its original whole
outside chronology, stays UNNORMALIZED and unchanged while ALL terminal native
clocks move to the second source's current-pair catalogue. This is stronger
than a fixed-old-History receiver, but does not assert a new graph's past was
generated by its own initializer or transport the recursive future trace. -/
theorem actual_marked_past_clock_fibre {sample : Copy → X} (r : PositivePairRates E)
    (initial d : Code N sample)
    (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp d t) (cut : ℝ≥0) :
    ((((actualMarkedTraceLaw N r (Fintype.card Copy) initial (cut : ℝ)).restrict
        {z | decodedEndpoint N (Fintype.card Copy) initial z = some d}).prod
      (currentPairClockMeasure N r d)).map
        (Prod.map id
          (MeasurableEquiv.piCongrLeft
            (fun _ : Choice (suppressedNetwork N hcut b hb hp) t => ℝ)
            (actualChoiceEquiv N hcut b hb hp d t h))) =
      ((actualMarkedTraceLaw N r (Fintype.card Copy) initial (cut : ℝ)).restrict
        {z | decodedEndpoint N (Fintype.card Copy) initial z = some d}).prod
          (currentPairClockMeasure (suppressedNetwork N hcut b hb hp)
            (youngestPhaseRates N hcut b hb hp r) t) := by
  letI := actual_marked_trace_probability N r (Fintype.card Copy) initial (cut : ℝ)
  letI := GProgram.G2.HistoryResidualAttachment.current_clock_probability N r d
  rw [← Measure.map_prod_map _ _ measurable_id
      (MeasurableEquiv.piCongrLeft
        (fun _ : Choice (suppressedNetwork N hcut b hb hp) t => ℝ)
        (actualChoiceEquiv N hcut b hb hp d t h)).measurable,
    Measure.map_id, actual_joint_clock_product N hcut b hb hp r d t h]

/-- A genuine actual sourceTimeKernel consequence at the FIRST holding event;
the two native globalRateBounds need not agree. This says no merger, not a
posterior, whole kernel or completed prefix equality. Empty pairs are included. -/
theorem actual_no_merger_kernel_mass {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (duration : ℝ≥0) :
    (sourceTimeKernel N r duration s s).toReal =
      (sourceTimeKernel (suppressedNetwork N hcut b hb hp)
        (youngestPhaseRates N hcut b hb hp r) duration t t).toReal := by
  rw [actual_source_kernel_no_merger, actual_source_kernel_no_merger,
    actual_total_rate N hcut b hb hp r s t h]

#print axioms phaseEdgeEquiv
#print axioms actual_population_catalogue
#print axioms phase_epoch_compatible
#print axioms actual_choice_site_exists
#print axioms actualChoiceEquiv
#print axioms youngestPhaseRates
#print axioms actual_choice_rate
#print axioms actual_total_rate
#print axioms actual_joint_clock_product
#print axioms current_clocks_private_register_erasure
#print axioms actual_natural_guard_joint_clocks
#print axioms actual_marked_past_clock_fibre
#print axioms actual_no_merger_kernel_mass

end UnifiedLean.G6.NativePhaseClocks
