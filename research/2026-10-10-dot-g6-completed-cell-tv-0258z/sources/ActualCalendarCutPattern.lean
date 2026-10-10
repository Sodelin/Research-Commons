import StableFiniteCutSchema
import UnifiedLean.Source.SourceCalendarTiming

/-! Fixed full event cells determine the actual finite-calendar cut/rank word.
No zero-date assumption is made: the offset is the original first date. -/
namespace UnifiedLean.G6.ActualCalendarCutPattern
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.OriginalCalendarSchema
open UnifiedLean.G6.OriginalCalendarPattern UnifiedLean.G6.GeneratedNaturalChronology
open UnifiedLean.G6.StableCutSchema UnifiedLean.G6.StableFiniteCutSchema
open UnifiedLean.G6.FiniteCutSourceWord
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarTiming UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

 theorem anchored_append {Tag : Type*} {a b c : AgeAtom V}
    {xs ys : List (Step V E × Tag)} (hx : Anchored a xs b) (hy : Anchored b ys c) :
    Anchored a (xs ++ ys) c := by
  induction hx with
  | nil => exact hy
  | interval a b z tag ws h ih => exact .interval a b c tag _ (ih hy)
  | exit a z e tag ws h ih => exact .exit a c e tag _ (ih hy)
  | enter a z v tag ws h ih => exact .enter a c v tag _ (ih hy)

 theorem boundaries_anchored (a : AgeAtom V) (xs : List (Step V E))
    (h : ∀ x y, Step.interval x y ∉ xs) :
    Anchored a (xs.map (fun s => (s,()))) a := by
  induction xs with
  | nil => exact .nil a
  | cons s ss ih =>
    have ht := ih (fun x y hm => h x y (List.mem_cons_of_mem _ hm))
    cases s with
    | interval x y => exact False.elim (h x y (by simp))
    | exit e => exact .exit a a e () _ ht
    | enter v => exact .enter a a v () _ ht

 def lastVertex (v : V) : List V → V
  | [] => v
  | w::ws => lastVertex w ws

 theorem tail_anchored (N : RootedBinary V E X) (age : V → ℝ) (v : V) (vs : List V) :
    Anchored (.node v) ((tailSchema N age v vs).map (fun s => (s,())))
      (.node (lastVertex v vs)) := by
  induction vs generalizing v with
  | nil => exact .nil _
  | cons w ws ih =>
    simp only [tailSchema,List.map_cons,List.map_append,lastVertex]
    exact .interval _ _ _ () _ (anchored_append
      (boundaries_anchored (.node w) _ (boundary_no_interval N age w)) (ih w))

 theorem tail_available (N : RootedBinary V E X) (age : V → ℝ)
    {j : ℕ} (cuts : Fin j → ℚ) (v : V) (vs : List V) :
    ∀ a b, Step.interval a b ∈ tailSchema N age v vs →
      Available cuts a ∧ Available cuts b := by
  induction vs generalizing v with
  | nil => intro a b hm; simp [tailSchema] at hm
  | cons w ws ih =>
    intro a b hm
    simp only [tailSchema,List.mem_cons,List.mem_append] at hm
    rcases hm with he | hb | ht
    · cases he; exact ⟨⟨.inl v,rfl⟩,⟨.inl w,rfl⟩⟩
    · exact False.elim (boundary_no_interval N age w a b hb)
    · exact ih w a b ht

 theorem calendar_available (N : RootedBinary V E X) (C : Calendar N.graph)
    {j : ℕ} (cuts : Fin j → ℚ) :
    ∀ a b, Step.interval a b ∈ calendarSchema N C →
      Available cuts a ∧ Available cuts b := by
  intro a b hm
  unfold calendarSchema at hm
  cases hv : representatives N C with
  | nil => simp [hv] at hm
  | cons v vs =>
    rw [hv] at hm
    rcases List.mem_append.mp hm with hb | ht
    · exact False.elim (boundary_no_interval N C.age v a b hb)
    · exact tail_available N C.age cuts v vs a b ht

 theorem calendar_ordered (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) :
    Ordered D.age ((calendarSchema N C).map (fun s => (s,()))) := by
  intro a b tag hm
  obtain ⟨s,hs,he⟩ := List.mem_map.mp hm
  have he' := congrArg Prod.fst he
  change s = Step.interval a b at he'
  subst s
  have ho := (original_dates_ordered N D).1
  rw [← representatives_retime N C D h,List.pairwise_map] at ho
  unfold calendarSchema at hs
  cases hv : representatives N C with
  | nil => simp [hv] at hs
  | cons v vs =>
    rw [hv] at hs ho
    rcases List.mem_append.mp hs with hb | ht
    · exact False.elim (boundary_no_interval N C.age v a b hb)
    · exact tail_interval_ordered N C.age D.age v vs ho a b ht

 theorem calendar_anchored (N : RootedBinary V E X) (C : Calendar N.graph) :
    ∃ v z : V, Anchored (.node v) ((calendarSchema N C).map (fun s => (s,()))) (.node z) ∧
      ∀ (D : Calendar N.graph), SameOrder C.age D.age → D.age v = firstOriginalDate N D := by
  have hne : representatives N C ≠ [] := by
    intro hn
    have hm := original_date_scheduled N C N.root
    rw [← representatives_dates N C,hn] at hm
    exact List.not_mem_nil hm
  obtain ⟨v,vs,hvs⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨v,lastVertex v vs,?_,?_⟩
  · simp only [calendarSchema,hvs,List.map_append]
    exact anchored_append (boundaries_anchored (.node v) _ (boundary_no_interval N C.age v))
      (tail_anchored N C.age v vs)
  · intro D h
    have hd := representatives_retime N C D h
    rw [hvs,List.map_cons] at hd
    have hi := first_compiled_date_is_initial_boundary N D
    simpa only [← hd,List.getElem_cons_zero] using hi

/-- A single reference realization supplies original-ID syntax for every
realization of its full event cell. Literal ages/rates remain source values. -/
 theorem actual_calendar_ranked_schema (N : RootedBinary V E X) (C D : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    (hc : Realizes cuts sig C.age) (hd : Realizes cuts sig D.age) (ks : List (Fin j)) :
    interpret N D H p common (ranked C.age cuts ks (calendarSchema N C)) =
      rankedWord N (values cuts ks)
        (compiledCalendarProgram N D H (originalGamma p) common) (firstOriginalDate N D) := by
  have horder := realized_sameOrder cuts sig hc hd
  obtain ⟨v,z,ha,hfirst⟩ := calendar_anchored N C
  rw [ranked_stable cuts sig hc hd ks _ (calendar_available N C cuts)]
  have he := ranked_agrees N D H p common cuts ks (calendarSchema N C)
    (.node v) (.node z) ha (calendar_ordered N C D horder)
  simpa only [actual_calendar_schema N C D horder H p common,AgeAtom.eval,hfirst D horder] using he

open CloudG3.ActualObservationCutRefinement CloudG3.ActualCalendarCutContext
open CloudG3.ActualCalendarEndpointHistory

/-- The common symbolic word is a legal refinement of each actual original calendar. -/
theorem actual_calendar_ranked_refines (N : RootedBinary V E X) (C D : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    (hc : Realizes cuts sig C.age) (hd : Realizes cuts sig D.age) (ks : List (Fin j)) :
    CutRefines N (compiledCalendarProgram N D H (originalGamma p) common)
      (physicalOps N (interpret N D H p common (ranked C.age cuts ks (calendarSchema N C)))) := by
  rw [actual_calendar_ranked_schema N C D H p common cuts sig hc hd ks]
  exact ranked_word_refines N (values cuts ks) _ _

/-- Bin tags, including equality at cuts, belong to the same actual source word. -/
theorem actual_calendar_ranked_bin_contract (N : RootedBinary V E X) (C D : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    {j : ℕ} (cuts : Fin j → ℚ) (sig : Signature V j)
    (hc : Realizes cuts sig C.age) (hd : Realizes cuts sig D.age) (ks : List (Fin j)) :
    wordBinContract N (rankBin (values cuts ks))
      (interpret N D H p common (ranked C.age cuts ks (calendarSchema N C)))
      (firstOriginalDate N D) := by
  rw [actual_calendar_ranked_schema N C D H p common cuts sig hc hd ks]
  exact ranked_word_contract N (values cuts ks) _ _

#print axioms actual_calendar_ranked_refines
#print axioms actual_calendar_ranked_bin_contract

#print axioms actual_calendar_ranked_schema
end UnifiedLean.G6.ActualCalendarCutPattern
