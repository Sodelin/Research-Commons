import ActualCalendarCutPattern
import GeneratedCompleteBinProxy

/-!
One original-ID symbolic finite-bin word for the actual completed-law proxy.
The finite ancestral extension is the existing generated extension, not a new
process. Its starting date is derived by telescoping the anchored schema.
Contributor: dot (OpenAI), 10 October 2026. Candidate, not yet compiler checked.
-/
namespace UnifiedLean.G6.ActualCompleteCutPattern
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.OriginalCalendarSchema
open UnifiedLean.G6.OriginalCalendarPattern UnifiedLean.G6.GeneratedNaturalChronology
open UnifiedLean.G6.StableCutSchema UnifiedLean.G6.StableFiniteCutSchema
open UnifiedLean.G6.ActualCalendarCutPattern UnifiedLean.G6.FiniteCutSourceWord
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G2.ChronologicalPathReadout
open CloudG3.ActualObservationCutRefinement CloudG3.ActualCalendarCutContext
open CloudG3.ActualCalendarEndpointHistory
open DotG6.GeneratedCompleteBinProxy
open scoped Classical NNReal
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

/-- The actual nonnegative interval lengths telescope along an anchored word. -/
theorem anchored_duration {Tag : Type*} (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    {a z : AgeAtom V} {ws : List (Step V E × Tag)}
    (ha : Anchored a ws z) (ho : Ordered C.age ws) :
    a.eval C.age + (programDuration N (instantiate N C H p common (ws.map Prod.fst)) : ℝ) =
      z.eval C.age := by
  induction ha with
  | nil a => simp [instantiate,programDuration]
  | exit a c e tag ws ha ih =>
      have ht : Ordered C.age ws := fun x y t hm => ho x y t (List.mem_cons_of_mem _ hm)
      simpa [instantiate,instantiateStep,programDuration] using ih ht
  | enter a c v tag ws ha ih =>
      have ht : Ordered C.age ws := fun x y t hm => ho x y t (List.mem_cons_of_mem _ hm)
      simpa [instantiate,instantiateStep,programDuration] using ih ht
  | interval a b c tag ws ha ih =>
      have hab := ho a b tag (by simp)
      have ht : Ordered C.age ws := fun x y t hm => ho x y t (List.mem_cons_of_mem _ hm)
      have hi := ih ht
      have hd : (Real.toNNReal (b.eval C.age-a.eval C.age) : ℝ) =
          b.eval C.age-a.eval C.age := Real.coe_toNNReal _ (sub_nonneg.mpr hab)
      have he : a.eval C.age + (b.eval C.age-a.eval C.age +
          (programDuration N (instantiate N C H p common (ws.map Prod.fst)) : ℝ)) =
          c.eval C.age := by linarith
      simpa [instantiate,instantiateStep,programDuration,NNReal.coe_add,hd] using he

noncomputable def endAtom (age : V → ℝ) (z : V) (q : ℚ) : AgeAtom V :=
  if age z ≤ (q:ℝ) then .fixed q else .node z

noncomputable def endStep (age : V → ℝ) (z : V) (q : ℚ) : Step V E :=
  .interval (.node z) (endAtom age z q)

theorem end_atom_ge (age : V → ℝ) (z : V) (q : ℚ) :
    age z ≤ (endAtom age z q).eval age := by
  by_cases h : age z ≤ (q:ℝ)
  · simpa [endAtom,h,AgeAtom.eval] using h
  · simp [endAtom,h,AgeAtom.eval]

theorem end_atom_stable {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    {age age' : V → ℝ} (h : Realizes cuts sig age) (h' : Realizes cuts sig age')
    (k : Fin j) (z : V) : endAtom age z (cuts k) = endAtom age' z (cuts k) := by
  have he : age z ≤ (cuts k:ℝ) ↔ age' z ≤ (cuts k:ℝ) :=
    available_le cuts sig h h' ⟨.inl z,rfl⟩ ⟨.inr k,rfl⟩
  simp only [endAtom,he]

theorem end_step_agrees (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (z : V) (q : ℚ) :
    instantiateStep N C H p common (endStep C.age z q) =
      ProgramStep.interval (Real.toNNReal ((q:ℝ)-C.age z)) := by
  by_cases h : C.age z ≤ (q:ℝ)
  · simp [endStep,endAtom,h,instantiateStep,AgeAtom.eval]
  · have hn : (q:ℝ)-C.age z ≤ 0 := sub_nonpos.mpr (le_of_not_ge h)
    simp [endStep,endAtom,h,instantiateStep,AgeAtom.eval,Real.toNNReal_of_nonpos hn]

theorem end_atom_available {j : ℕ} (cuts : Fin j → ℚ) (age : V → ℝ)
    (k : Fin j) (z : V) : Available cuts (endAtom age z (cuts k)) := by
  by_cases h : age z ≤ (cuts k:ℝ)
  · simpa [endAtom,h] using (show Available (V := V) cuts (.fixed (cuts k)) from ⟨.inr k,rfl⟩)
  · simpa [endAtom,h] using (show Available (V := V) cuts (.node z) from ⟨.inl z,rfl⟩)

/-- The cut bank contains its computed last-cut bound. This is an arithmetic
condition on supplied rational constants, not a source-law or refinement oracle.
A zero/last-cut slot can always be appended to the event-signature bank. -/
theorem actual_complete_word_per_cell (N : RootedBinary V E X) (C : Calendar N.graph)
    {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    (hc : Realizes cuts sig C.age) (ks : List (Fin j)) (kend : Fin j)
    (hlast : (cuts kend:ℝ) = lastCut (values cuts ks)) :
    ∃ w : List (Step V E × Fin ((values cuts ks).length+1)),
      ∀ (D : Calendar N.graph), Realizes cuts sig D.age →
      ∀ (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool),
        interpret N D H p common w = originalCutWord N D H p common (values cuts ks) ∧
        CutRefines N (extendedOriginalOps N D H p common (values cuts ks))
          (physicalOps N (interpret N D H p common w)) ∧
        wordBinContract N (rankBin (values cuts ks)) (interpret N D H p common w)
          (firstOriginalDate N D) := by
  obtain ⟨v,z,ha,hfirst⟩ := calendar_anchored N C
  let schema : List (Step V E) := calendarSchema N C ++ [endStep C.age z (cuts kend)]
  have hs : ∀ a b, Step.interval a b ∈ schema → Available cuts a ∧ Available cuts b := by
    intro a b hm
    change Step.interval a b ∈ calendarSchema N C ++ [endStep C.age z (cuts kend)] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact calendar_available N C cuts a b hm
    · simp only [List.mem_singleton,endStep] at hm
      cases hm
      exact ⟨⟨.inl z,rfl⟩,end_atom_available cuts C.age kend z⟩
  have ha' : Anchored (.node v) (schema.map (fun s => (s,())))
      (endAtom C.age z (cuts kend)) := by
    change Anchored (.node v) ((calendarSchema N C ++ [endStep C.age z (cuts kend)]).map
      (fun s => (s,()))) _
    rw [List.map_append]
    exact anchored_append ha (.interval _ _ _ () [] (.nil _))
  refine ⟨ranked C.age cuts ks schema,?_⟩
  intro D hd H p common
  have horder := realized_sameOrder cuts sig hc hd
  have hend := end_atom_stable cuts sig hc hd kend z
  have ho : Ordered D.age (schema.map (fun s => (s,()))) := by
    intro a b tag hm
    change (.interval a b,tag) ∈
      (calendarSchema N C ++ [endStep C.age z (cuts kend)]).map (fun s => (s,())) at hm
    rw [List.map_append,List.mem_append] at hm
    rcases hm with hm | hm
    · exact calendar_ordered N C D horder a b tag hm
    · simp only [List.map_cons,List.map_nil,List.mem_singleton,endStep] at hm
      cases hm
      simpa only [AgeAtom.eval,hend] using end_atom_ge D.age z (cuts kend)
  have hdur := anchored_duration N D H p common ha (calendar_ordered N C D horder)
  have hmap : ((calendarSchema N C).map (fun s => (s,()))).map Prod.fst = calendarSchema N C := by simp [Function.comp_def]
  rw [hmap,actual_calendar_schema N C D horder H p common] at hdur
  have hfinal : firstOriginalDate N D +
      (programDuration N (compiledCalendarProgram N D H (originalGamma p) common) : ℝ) = D.age z := by
    simpa only [AgeAtom.eval,hfirst D horder] using hdur
  have hop : instantiate N D H p common schema =
      extendedOriginalOps N D H p common (values cuts ks) := by
    have he : endStep C.age z (cuts kend) = (endStep D.age z (cuts kend) : Step V E) := by
      simp only [endStep,hend]
    simp only [schema,instantiate,List.map_append,List.map_cons,List.map_nil]
    change instantiate N D H p common (calendarSchema N C) ++
      [instantiateStep N D H p common (endStep C.age z (cuts kend))] = _
    rw [actual_calendar_schema N C D horder H p common,he,end_step_agrees]
    simp only [extendedOriginalOps,hfinal,hlast]
  have hw : interpret N D H p common (ranked C.age cuts ks schema) =
      originalCutWord N D H p common (values cuts ks) := by
    rw [ranked_stable cuts sig hc hd ks schema hs]
    have he := ranked_agrees N D H p common cuts ks schema (.node v)
      (endAtom C.age z (cuts kend)) ha' ho
    simpa only [hop,AgeAtom.eval,hfirst D horder,originalCutWord] using he
  refine ⟨hw,?_,?_⟩
  · rw [hw]
    exact ranked_word_refines N (values cuts ks) _ _
  · rw [hw]
    exact ranked_word_contract N (values cuts ks) _ _


/-- Computed rational end bound, including zero for an empty cut list. -/
def lastRationalCut {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) : ℚ :=
  (ks.map cuts).foldr max 0

theorem last_rational_cut_cast {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) :
    (lastRationalCut cuts ks : ℝ) = lastCut (values cuts ks) := by
  induction ks with
  | nil => simp [lastRationalCut,lastCut,values]
  | cons k ks ih =>
      simpa only [lastRationalCut,lastCut,values,List.map_cons,List.foldr_cons,Rat.cast_max]
        using congrArg (max (cuts k:ℝ)) ih

/-- The additional event atom is a computed constant; no new physical step,
node, edge, inheritance coin or source parameter is introduced. -/
def completedCutBank {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) : Fin (j+1) → ℚ :=
  Fin.cons (lastRationalCut cuts ks) cuts

theorem completed_cut_bank_values {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) :
    values (completedCutBank cuts ks) (ks.map Fin.succ) = values cuts ks := by
  simp [values,completedCutBank,List.map_map,Function.comp_def]

theorem completed_cut_bank_bound {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) :
    (completedCutBank cuts ks 0 : ℝ) =
      lastCut (values (completedCutBank cuts ks) (ks.map Fin.succ)) := by
  rw [completed_cut_bank_values]
  simpa only [completedCutBank,Fin.cons_zero] using last_rational_cut_cast cuts ks

/-- Arbitrary finite rational observation cuts, including the empty list.
The event cell contains the original dates, all supplied cuts and their
computed last-cut/zero bound. One symbolic word then instantiates to the
actual generated complete-law word for every source realization of that cell.
Original IDs, register bank and COMMON flags are unchanged. -/
theorem actual_complete_word_from_augmented_cell (N : RootedBinary V E X)
    (C : Calendar N.graph) {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j))
    (sig : Signature V (j+1)) (hc : Realizes (completedCutBank cuts ks) sig C.age) :
    ∃ w : List (Step V E × Fin ((values cuts ks).length+1)),
      ∀ (D : Calendar N.graph), Realizes (completedCutBank cuts ks) sig D.age →
      ∀ (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool),
        interpret N D H p common w = originalCutWord N D H p common (values cuts ks) ∧
        CutRefines N (extendedOriginalOps N D H p common (values cuts ks))
          (physicalOps N (interpret N D H p common w)) ∧
        wordBinContract N (rankBin (values cuts ks)) (interpret N D H p common w)
          (firstOriginalDate N D) := by
  let P : List ℝ → Prop := fun qs =>
    ∃ w : List (Step V E × Fin (qs.length+1)),
      ∀ (D : Calendar N.graph), Realizes (completedCutBank cuts ks) sig D.age →
      ∀ (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool),
        interpret N D H p common w = originalCutWord N D H p common qs ∧
        CutRefines N (extendedOriginalOps N D H p common qs)
          (physicalOps N (interpret N D H p common w)) ∧
        wordBinContract N (rankBin qs) (interpret N D H p common w) (firstOriginalDate N D)
  have hP : P (values (completedCutBank cuts ks) (ks.map Fin.succ)) :=
    actual_complete_word_per_cell N C (completedCutBank cuts ks) sig hc (ks.map Fin.succ) 0
      (completed_cut_bank_bound cuts ks)
  exact (congrArg P (completed_cut_bank_values cuts ks)).mp hP

#print axioms anchored_duration
#print axioms actual_complete_word_per_cell
#print axioms actual_complete_word_from_augmented_cell
end UnifiedLean.G6.ActualCompleteCutPattern
