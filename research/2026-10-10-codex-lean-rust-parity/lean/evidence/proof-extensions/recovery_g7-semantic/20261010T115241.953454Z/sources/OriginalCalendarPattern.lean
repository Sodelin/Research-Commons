import OriginalCalendarSchema
import GeneratedNaturalChronology
import Mathlib.Data.List.Sort

/-! Actual original calendar pattern under a fixed age-order cell. No stochastic
law or desired equality is an input. The representative vertex list is derived
from the actual finite original date set. Cut insertion is handled separately. -/
namespace UnifiedLean.G6.OriginalCalendarPattern
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.GeneratedNaturalChronology
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

def SameOrder (a b : V → ℝ) : Prop := ∀ v w, a v ≤ a w ↔ b v ≤ b w

theorem sameOrder_eq {a b : V → ℝ} (h : SameOrder a b) (v w : V) :
    a v = a w ↔ b v = b w := by
  constructor <;> intro he
  · exact le_antisymm ((h v w).mp he.le) ((h w v).mp he.ge)
  · exact le_antisymm ((h v w).mpr he.le) ((h w v).mpr he.ge)

theorem realized_sameOrder {j : ℕ} (cuts : Fin j → ℚ) (s : Signature V j)
    {a b : V → ℝ} (ha : Realizes cuts s a) (hb : Realizes cuts s b) : SameOrder a b := by
  intro v w
  exact (atMost_iff ha (.inl v) (.inl w)).symm.trans (atMost_iff hb (.inl v) (.inl w))

theorem exists_representatives (N : RootedBinary V E X) (C : Calendar N.graph) :
    ∃ vs : List V, vs.map C.age = sortedOriginalDates N C := by
  have aux : ∀ ds : List ℝ, (∀ a ∈ ds, ∃ v, C.age v = a) →
      ∃ vs : List V, vs.map C.age = ds := by
    intro ds
    induction ds with
    | nil => exact fun _ => ⟨[],rfl⟩
    | cons a ds ih =>
      intro h
      obtain ⟨v,hv⟩ := h a (by simp)
      obtain ⟨vs,hvs⟩ := ih (fun x hx => h x (by simp [hx]))
      exact ⟨v::vs,by simp [hv,hvs]⟩
  apply aux
  intro a ha
  simpa [sortedOriginalDates,originalDates] using ha

noncomputable def representatives (N : RootedBinary V E X) (C : Calendar N.graph) : List V :=
  Classical.choose (exists_representatives N C)

theorem representatives_dates (N : RootedBinary V E X) (C : Calendar N.graph) :
    (representatives N C).map C.age = sortedOriginalDates N C :=
  Classical.choose_spec (exists_representatives N C)

theorem representatives_retime (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) :
    (representatives N C).map D.age = sortedOriginalDates N D := by
  have hc := original_dates_ordered N C
  rw [← representatives_dates N C] at hc
  have hdorder : ((representatives N C).map D.age).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map] at hc ⊢
    exact hc.1.imp (fun {v w} hvw => (h v w).mp hvw)
  have hdunique : ((representatives N C).map D.age).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    have hn := hc.2
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hn
    exact hn.imp (fun {v w} hvw he => hvw ((sameOrder_eq h v w).mpr he))
  apply List.Perm.eq_of_pairwise' hdorder (original_dates_ordered N D).1
  apply (List.perm_ext_iff_of_nodup hdunique (original_dates_ordered N D).2).mpr
  intro x
  constructor
  · intro hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact original_date_scheduled N D v
  · intro hx
    obtain ⟨v,hv⟩ : ∃ v, D.age v = x := by
      simpa [sortedOriginalDates,originalDates] using hx
    have hcdate := original_date_scheduled N C v
    rw [← representatives_dates N C] at hcdate
    obtain ⟨w,hw,he⟩ := List.mem_map.mp hcdate
    exact List.mem_map.mpr ⟨w,hw,((sameOrder_eq h w v).mp he).trans hv⟩

noncomputable def boundarySchema (N : RootedBinary V E X) (a : V → ℝ) (v : V) : List (Step V E) :=
  ((Finset.univ.filter (fun e : E => a (N.graph.source e) = a v)).toList.map Step.exit) ++
  ((Finset.univ.filter (fun w : V => a w = a v)).toList.map Step.enter)

noncomputable def tailSchema (N : RootedBinary V E X) (a : V → ℝ) : V → List V → List (Step V E)
  | _,[] => []
  | v,w::ws => .interval (.node v) (.node w) ::
      (boundarySchema N a w ++ tailSchema N a w ws)

noncomputable def calendarSchema (N : RootedBinary V E X) (C : Calendar N.graph) : List (Step V E) :=
  match representatives N C with
  | [] => []
  | v::vs => boundarySchema N C.age v ++ tailSchema N C.age v vs

 theorem boundary_schema_stable (N : RootedBinary V E X) {a b : V → ℝ}
    (h : SameOrder a b) (v : V) : boundarySchema N a v = boundarySchema N b v := by
  simp only [boundarySchema]
  congr 2 <;> congr 1 <;> ext x <;> simp [sameOrder_eq h]

 theorem boundary_instantiates (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (v : V) :
    instantiate N D H p common (boundarySchema N C.age v) =
      boundaryOperations N D H (originalGamma p) common (D.age v) := by
  rw [boundary_schema_stable N h]
  simp [instantiate,boundarySchema,boundaryOperations,List.map_map,Function.comp_def,instantiateStep]

 theorem tail_instantiates (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (v : V) (vs : List V) :
    instantiate N D H p common (tailSchema N C.age v vs) =
      calendarTail N D H (originalGamma p) common (D.age v) (vs.map D.age) := by
  induction vs generalizing v with
  | nil => rfl
  | cons w ws ih =>
    simp only [tailSchema,instantiate,List.map_cons,List.map_append,instantiateStep,
      NaturalCellInverseRates.AgeAtom.eval,calendarTail]
    rw [show List.map (instantiateStep N D H p common) (boundarySchema N C.age w) =
      boundaryOperations N D H (originalGamma p) common (D.age w) from
      boundary_instantiates N C D h H p common w]
    rw [show List.map (instantiateStep N D H p common) (tailSchema N C.age w ws) = _ from ih w]

 theorem actual_calendar_schema (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) :
    instantiate N D H p common (calendarSchema N C) =
      compiledCalendarProgram N D H (originalGamma p) common := by
  unfold calendarSchema compiledCalendarProgram
  rw [← representatives_retime N C D h]
  cases hv : representatives N C with
  | nil => rfl
  | cons v vs =>
    simp only [List.map_cons,instantiate,List.map_append]
    exact congrArg₂ (· ++ ·) (boundary_instantiates N C D h H p common v)
      (tail_instantiates N C D h H p common v vs)

 theorem boundary_no_interval (N : RootedBinary V E X) (a : V → ℝ) (v : V)
    (x y : NaturalCellInverseRates.AgeAtom V) :
    Step.interval x y ∉ boundarySchema N a v := by
  simp [boundarySchema]

 theorem tail_interval_ordered (N : RootedBinary V E X) (a b : V → ℝ)
    (v : V) (vs : List V) (hs : (v::vs).Pairwise (fun v w => b v ≤ b w))
    (x y : NaturalCellInverseRates.AgeAtom V)
    (hm : Step.interval x y ∈ tailSchema N a v vs) : x.eval b ≤ y.eval b := by
  induction vs generalizing v with
  | nil => simp [tailSchema] at hm
  | cons w ws ih =>
    simp only [tailSchema,List.mem_cons,List.mem_append] at hm
    rcases hm with he | hb | ht
    · cases he
      exact (List.pairwise_cons.mp hs).1 w (by simp)
    · exact False.elim (boundary_no_interval N a w x y hb)
    · exact ih w (List.pairwise_cons.mp hs).2 ht

 theorem actual_schema_nonnegative (N : RootedBinary V E X) (C D : Calendar N.graph)
    (h : SameOrder C.age D.age) : nonnegative (calendarSchema N C) D.age := by
  have aux : ∀ x y, Step.interval x y ∈ calendarSchema N C → x.eval D.age ≤ y.eval D.age := by
    intro x y hm
    have ho := (original_dates_ordered N D).1
    rw [← representatives_retime N C D h,List.pairwise_map] at ho
    unfold calendarSchema at hm
    cases hv : representatives N C with
    | nil => simp [hv] at hm
    | cons v vs =>
      rw [hv] at hm ho
      rcases List.mem_append.mp hm with hb | ht
      · exact False.elim (boundary_no_interval N C.age v _ _ hb)
      · exact tail_interval_ordered N C.age D.age v vs ho _ _ ht
  intro i
  apply aux
  rw [← step_interval_of_flag _ i.property]
  exact List.get_mem _ _

end UnifiedLean.G6.OriginalCalendarPattern
