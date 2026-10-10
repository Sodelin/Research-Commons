import G5ActualRoutingSupport

/-!
# Original strict boundary-choice histories, without probabilistic premises
Contributor: dot, 2026-10-09. Candidate, pending compilation/review.
LegalBoundaryRoute names the actual deterministic original-edge updates and
finite current-owner coin assignments. COMMON reads its existing register.
-/
namespace GProgram.G5.StrictBoundaryRoutes
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceForestPulseMeasure UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G5.ActualRoutingSupport GProgram.G5.OriginalSelectedPosterior
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma strict_bit_atom_ne_zero (gamma : unitInterval)
    (h0 : 0 < (gamma : ℝ)) (h1 : (gamma : ℝ) < 1) (b : Bool) :
    bitMeasure gamma {b} ≠ 0 := by
  have hp : 0 < (bitMeasure gamma {b}).toReal := by
    cases b with
    | false => simpa [bitMeasure, ← measureReal_def, bernoulliMeasure_real_apply] using sub_pos.mpr h1
    | true => simpa [bitMeasure, ← measureReal_def, bernoulliMeasure_real_apply] using h0
  intro hz
  rw [hz, ENNReal.toReal_zero] at hp
  exact (lt_irrefl 0) hp

lemma strict_current_coin_support (Site : Type*) [Fintype Site] (gamma : unitInterval)
    (h0 : 0 < (gamma : ℝ)) (h1 : (gamma : ℝ) < 1) (coin : Site → Bool) :
    coin ∈ (currentCoinPMF Site gamma).support := by
  apply (PMF.mem_support_iff _ _).mpr
  change (independentCoinMeasure Site gamma).toPMF coin ≠ 0
  rw [Measure.toPMF_apply, independentCoinMeasure, Measure.pi_singleton]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => strict_bit_atom_ne_zero gamma h0 h1 (coin i))

noncomputable def StrictBoundary (N : RootedBinary V E X) : BoundaryOperation N → Prop
  | .independent _ gamma => 0 < (gamma : ℝ) ∧ (gamma : ℝ) < 1
  | _ => True

noncomputable def LegalBoundaryRoute (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s d : Code N sample) : Prop :=
  match b with
  | .exit e => d = exitCode N s e
  | .ordinary e _ => d = ordinaryCode N s e
  | .root => d = rootCode N s
  | .common H => d = pulseCode H s (fun _ => (state s).register H.hybrid)
  | .independent H _ => ∃ coin : AtNode (state s) H.hybrid → Bool, d = pulseCode H s coin

lemma actual_boundary_support_iff_legal (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (hb : StrictBoundary N b) (s d : Code N sample) :
    d ∈ (boundaryKernel N b s).support ↔ LegalBoundaryRoute N b s d := by
  cases b with
  | exit e => simp [boundaryKernel, LegalBoundaryRoute]
  | ordinary e degree => simp [boundaryKernel, LegalBoundaryRoute]
  | root => simp [boundaryKernel, LegalBoundaryRoute]
  | common H => simp [boundaryKernel, LegalBoundaryRoute]
  | independent H gamma =>
      change d ∈ ((currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
        (pulseCode H s)).support ↔ _
      rw [PMF.mem_support_map_iff]
      constructor
      · rintro ⟨coin, _, he⟩; exact ⟨coin, he.symm⟩
      · rintro ⟨coin, he⟩
        exact ⟨coin, strict_current_coin_support _ gamma hb.1 hb.2 coin, he.symm⟩

noncomputable def StrictWord (N : RootedBinary V E X) : List (ProgramStep N) → Prop
  | [] => True
  | .interval _ :: ops => StrictWord N ops
  | .boundary b :: ops => StrictBoundary N b ∧ StrictWord N ops

noncomputable def LegalRoute (N : RootedBinary V E X) {sample : Copy → X} :
    List (ProgramStep N) → Code N sample → Code N sample → Prop
  | [], s, d => d = s
  | .interval _ :: ops, s, d => LegalRoute N ops s d
  | .boundary b :: ops, s, d => ∃ m, LegalBoundaryRoute N b s m ∧ LegalRoute N ops m d

/-- Every admitted finite current-owner coin assignment appears with positive
mass; the legality relation does not assume a desired support theorem. -/
theorem route_support_iff_legal (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (hops : StrictWord N ops) (s d : Code N sample) :
    d ∈ (routeProgram N ops s).support ↔ LegalRoute N ops s d := by
  induction ops generalizing s with
  | nil => simp [routeProgram, LegalRoute]
  | cons op ops ih =>
      cases op with
      | interval t => exact ih hops s
      | boundary b =>
          change d ∈ ((boundaryKernel N b s).bind (routeProgram N ops)).support ↔ _
          rw [PMF.mem_support_bind_iff]
          change (∃ m, m ∈ (boundaryKernel N b s).support ∧
            d ∈ (routeProgram N ops m).support) ↔ _
          simp_rw [actual_boundary_support_iff_legal N b hops.1, ih hops.2]
          rfl

lemma strict_original_register_coin (N : RootedBinary V E X) (p : HybridProbabilities N)
    (coin : Hybrid N → Bool) : coin ∈ (originalRegisterMeasure N p).toPMF.support := by
  apply (PMF.mem_support_iff _ _).mpr
  rw [Measure.toPMF_apply, originalRegisterMeasure, Measure.pi_singleton]
  exact Finset.prod_ne_zero_iff.mpr (fun h _ =>
    strict_bit_atom_ne_zero (originalGamma p h) (p.positive h) (p.below_one h) (coin h))

/-- The natural register law has precisely the original hybrid bit assignments,
with its inert false convention on nonhybrid vertices. -/
theorem actual_original_route_support_iff_seeds (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (ops : List (ProgramStep N))
    (hops : StrictWord N ops) (d : Code N sample) :
    d ∈ (originalRouteLaw N sample p ops).support ↔
      ∃ coin : Hybrid N → Bool,
        LegalRoute N ops (initialCode N sample (originalRegister N coin)) d := by
  rw [originalRouteLaw, PMF.mem_support_bind_iff]
  constructor
  · rintro ⟨reg, hr, hd⟩
    obtain ⟨coin, _, hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst reg
    exact ⟨coin, (route_support_iff_legal N ops hops _ d).mp hd⟩
  · rintro ⟨coin, hd⟩
    exact ⟨originalRegister N coin,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨coin, strict_original_register_coin N p coin, rfl⟩,
      (route_support_iff_legal N ops hops _ d).mpr hd⟩

lemma strict_word_append (N : RootedBinary V E X) (xs ys : List (ProgramStep N)) :
    StrictWord N (xs ++ ys) ↔ StrictWord N xs ∧ StrictWord N ys := by
  induction xs with
  | nil => simp [StrictWord]
  | cons x xs ih => cases x <;> simp [StrictWord, ih, and_assoc]

lemma strict_boundary_map (N : RootedBinary V E X) {A : Type*}
    (f : A → BoundaryOperation N) (hf : ∀ a, StrictBoundary N (f a)) (xs : List A) :
    StrictWord N (xs.map (fun a => ProgramStep.boundary (f a))) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨hf x, ih⟩

lemma original_node_strict (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (v : V) :
    StrictBoundary N (originalNodeOperation N H (originalGamma p) common v) := by
  rcases original_node_is_actual_operation N H (originalGamma p) common v with h | h | h
  · rw [h.1]; trivial
  · obtain ⟨hy, _, _, hc | hi⟩ := h
    · rw [hc]; trivial
    · rw [hi]; exact ⟨p.positive hy, p.below_one hy⟩
  · obtain ⟨e, _, hd, he⟩ := h
    rw [he]; trivial

lemma actual_boundary_batch_strict (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (a : ℝ) :
    StrictWord N (boundaryOperations N C H (originalGamma p) common a) := by
  unfold boundaryOperations
  apply (strict_word_append N _ _).mpr
  exact ⟨strict_boundary_map N (fun e => .exit e) (fun _ => trivial) _,
    strict_boundary_map N _ (original_node_strict N H p common) _⟩

lemma actual_calendar_tail_strict (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (a : ℝ) (dates : List ℝ) :
    StrictWord N (calendarTail N C H (originalGamma p) common a dates) := by
  induction dates generalizing a with
  | nil => trivial
  | cons b dates ih =>
      change StrictWord N (boundaryOperations N C H (originalGamma p) common b ++
        calendarTail N C H (originalGamma p) common b dates)
      exact (strict_word_append N _ _).mpr ⟨actual_boundary_batch_strict N C H p common b, ih b⟩

/-- Strict source admission is derived for the actual original calendar and
its same immutable parameter bank, not added as a legal-route hypothesis. -/
theorem actual_compiled_calendar_strict (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) :
    StrictWord N (compiledCalendarProgram N C H (originalGamma p) common) := by
  unfold compiledCalendarProgram
  cases sortedOriginalDates N C with
  | nil => trivial
  | cons a dates =>
      exact (strict_word_append N _ _).mpr
        ⟨actual_boundary_batch_strict N C H p common a,
          actual_calendar_tail_strict N C H p common a dates⟩

/-- Original posterior support is exactly the images of finite legal source
routing choices, with no probability/support premise on those choices. -/
theorem actual_posterior_support_iff_seeds (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (hops : StrictWord N ops)
    (v : JoinedIndex N sample Finset.univ) :
    v ∈ (originalFullPosterior N sample p r Finset.univ ops).support ↔
      ∃ (coin : Hybrid N → Bool) (d : Code N sample),
        LegalRoute N ops (initialCode N sample (originalRegister N coin)) d ∧
        joinedProjection N Finset.univ (.inl d) = v := by
  rw [actual_posterior_route_support]
  constructor
  · rintro ⟨d, hd, hv⟩
    obtain ⟨coin, hc⟩ := (actual_original_route_support_iff_seeds N sample p ops hops d).mp hd
    exact ⟨coin, d, hc, hv⟩
  · rintro ⟨coin, d, hc, hv⟩
    exact ⟨d, (actual_original_route_support_iff_seeds N sample p ops hops d).mpr ⟨coin, hc⟩, hv⟩

#print axioms strict_current_coin_support
#print axioms actual_boundary_support_iff_legal
#print axioms route_support_iff_legal
#print axioms actual_original_route_support_iff_seeds
#print axioms actual_compiled_calendar_strict
#print axioms actual_posterior_support_iff_seeds
end GProgram.G5.StrictBoundaryRoutes
