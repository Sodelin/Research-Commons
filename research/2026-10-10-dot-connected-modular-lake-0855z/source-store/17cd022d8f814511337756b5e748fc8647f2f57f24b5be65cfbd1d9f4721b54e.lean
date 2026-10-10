import G5PhysicalCutChart

/-! Older-side cut chart, including a cut exactly at an original vertex age.
The prefix processes the entire tied original boundary batch first. -/
namespace GProgram.G5.OlderSideCutChart
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarTiming GProgram.G5.PhysicalCutChart
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

lemma adjacent_older_gap {a t : ℝ} (dates : List ℝ) (ha : a ≤ t)
    (hfuture : ∃ b ∈ a :: dates, t < b) :
    ∃ pre left right post, a :: dates = pre ++ left :: right :: post ∧ left ≤ t ∧ t < right := by
  induction dates generalizing a with
  | nil =>
    obtain ⟨b,hb,ht⟩ := hfuture
    have hb' : b = a := by simpa using hb
    subst b
    exact False.elim (not_lt_of_ge ha ht)
  | cons b bs ih =>
    by_cases htb : t < b
    · exact ⟨[],a,b,bs,rfl,ha,htb⟩
    · have hf : ∃ c ∈ b :: bs, t < c := by
        obtain ⟨c,hc,htc⟩ := hfuture
        rcases List.mem_cons.mp hc with hca | hc
        · subst c
          exact False.elim (not_lt_of_ge ha htc)
        · exact ⟨c,hc,htc⟩
      obtain ⟨pre,l,r,post,he,hl,hr⟩ := ih (le_of_not_gt htb) hf
      exact ⟨a::pre,l,r,post,by simp only [List.cons_append,←he],hl,hr⟩

lemma original_older_gap_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (t : ℝ) (hfirst : firstOriginalDate N C ≤ t) (hroot : t < C.age N.root) :
    ∃ pre guard next post, sortedOriginalDates N C = pre ++ guard :: next :: post ∧
      guard ≤ t ∧ t < next := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro hz
    have h := original_date_scheduled N C N.root
    rw [hz] at h
    exact List.not_mem_nil h
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have ha : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  obtain ⟨pre,l,r,post,hs,hl,hr⟩ := adjacent_older_gap dates (ha.symm ▸ hfirst)
    ⟨C.age N.root,heq ▸ original_date_scheduled N C N.root,hroot⟩
  exact ⟨pre,l,r,post,heq.trans hs,hl,hr⟩

lemma older_gap_three_parts {guard t next : ℝ} (hleft : guard ≤ t) (hright : t < next)
    (u : ℝ≥0) (hu : (u : ℝ) < next-t) :
    Real.toNNReal (next-guard) = Real.toNNReal (t-guard) +
      (u + Real.toNNReal (next-t-u)) := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add]
  rw [Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith),
    Real.coe_toNNReal _ (by linarith)]
  ring

#print axioms original_older_gap_exists
end GProgram.G5.OlderSideCutChart
