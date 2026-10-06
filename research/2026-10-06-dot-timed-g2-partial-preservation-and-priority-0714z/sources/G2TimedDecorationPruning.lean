import G2FaithfulPairAgeDecoration

/-!
Actual graft-age retention under leaf deletion and unary suppression.
Contributor: dot (OpenAI), 6 October 2026.
The operation recursively deletes unwanted leaves, suppresses one-sided grafts,
and retains exactly the original age of every surviving two-sided graft.
-/
namespace GProgram.G2.TimedDecorationPruning
set_option backward.isDefEq.respectTransparency false
open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration
open UnifiedLean.Source.SourceForestSilentPruning
open scoped Classical
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
abbrev Decorated := (t : Genealogy Copy) × Decoration t

noncomputable def join (age : ℝ) : Option (Decorated (Copy := Copy)) →
    Option (Decorated (Copy := Copy)) → Option (Decorated (Copy := Copy))
  | none, b => b
  | a, none => a
  | some a, some b => some ⟨.graft a.1 b.1,(age,a.2,b.2)⟩

noncomputable def prune (keep : Finset Copy) : (t : Genealogy Copy) → Decoration t →
    Option (Decorated (Copy := Copy))
  | .leaf x, _ => if x ∈ keep then some ⟨.leaf x,PUnit.unit⟩ else none
  | .graft a b, d => join d.1 (prune keep a d.2.1) (prune keep b d.2.2)

lemma join_forgets (age : ℝ) (a b : Option (Decorated (Copy := Copy))) :
    (join age a b).map Sigma.fst = Genealogy.joinPruned (a.map Sigma.fst) (b.map Sigma.fst) := by
  cases a <;> cases b <;> rfl

theorem prune_forgets (keep : Finset Copy) (t : Genealogy Copy) (d : Decoration t) :
    (prune keep t d).map Sigma.fst = t.prune keep := by
  induction t with
  | leaf x => by_cases h : x ∈ keep <;> simp [prune,Genealogy.prune,h]
  | graft a b ha hb =>
      simp only [prune,join_forgets,ha,hb,Genealogy.prune]

lemma pruned_leaves (keep : Finset Copy) (t : Genealogy Copy) (d : Decoration t)
    (u : Decorated (Copy := Copy)) (hu : prune keep t d = some u) :
    u.1.leaves = t.leaves ∩ keep := by
  have hf := prune_forgets keep t d
  rw [hu] at hf
  have hl := Genealogy.prune_leaves keep t
  rw [←hf] at hl
  exact hl

lemma absent_pruning (keep : Finset Copy) (t : Genealogy Copy) (d : Decoration t)
    (h : prune keep t d = none) : t.leaves ∩ keep = ∅ := by
  have hf := prune_forgets keep t d
  rw [h] at hf
  exact (prune_none_iff_no_selected_leaves keep t).mp hf.symm

/-- Every selected pair keeps its original MRCA age. Suppressing a unary
vertex does not substitute that vertex's age for the surviving child's age. -/
theorem prune_preserves_pair_age (leafAge : Copy → ℝ) (keep : Finset Copy)
    (t : Genealogy Copy) (d : Decoration t) (u : Decorated (Copy := Copy))
    (hu : prune keep t d = some u) {x y : Copy}
    (hx : x ∈ u.1.leaves) (hy : y ∈ u.1.leaves) :
    pairAge leafAge u.1 u.2 x y = pairAge leafAge t d x y := by
  induction t generalizing u with
  | leaf z =>
      by_cases hz : z ∈ keep
      · simp only [prune,if_pos hz,Option.some.injEq] at hu
        subst u
        rfl
      · simp [prune,hz] at hu
  | graft a b iha ihb =>
      cases ha : prune keep a d.2.1 with
      | none =>
        have ea := absent_pruning keep a d.2.1 ha
        cases hb : prune keep b d.2.2 with
        | none => simp [prune,ha,hb,join] at hu
        | some ub =>
          simp only [prune,ha,hb,join,Option.some.injEq] at hu
          subst u
          have lb := pruned_leaves keep b d.2.2 ub hb
          have hxb := (Finset.mem_inter.mp (lb ▸ hx)).1
          have hyb := (Finset.mem_inter.mp (lb ▸ hy)).1
          have hxk := (Finset.mem_inter.mp (lb ▸ hx)).2
          have hxa : x ∉ a.leaves := by
            intro h
            have hm := Finset.mem_inter.mpr ⟨h,hxk⟩
            rw [ea] at hm
            exact Finset.notMem_empty _ hm
          rw [pairAge,if_neg (fun h => hxa h.1),if_pos ⟨hxb,hyb⟩]
          exact ihb d.2.2 ub hb hx hy
      | some ua =>
        have la := pruned_leaves keep a d.2.1 ua ha
        cases hb : prune keep b d.2.2 with
        | none =>
          simp only [prune,ha,hb,join,Option.some.injEq] at hu
          subst u
          have hxa := (Finset.mem_inter.mp (la ▸ hx)).1
          have hya := (Finset.mem_inter.mp (la ▸ hy)).1
          rw [pairAge,if_pos ⟨hxa,hya⟩]
          exact iha d.2.1 ua ha hx hy
        | some ub =>
          have lb := pruned_leaves keep b d.2.2 ub hb
          simp only [prune,ha,hb,join,Option.some.injEq] at hu
          subst u
          have hxk : x ∈ keep := by
            rcases Finset.mem_union.mp hx with h | h
            · exact (Finset.mem_inter.mp (la ▸ h)).2
            · exact (Finset.mem_inter.mp (lb ▸ h)).2
          have hyk : y ∈ keep := by
            rcases Finset.mem_union.mp hy with h | h
            · exact (Finset.mem_inter.mp (la ▸ h)).2
            · exact (Finset.mem_inter.mp (lb ▸ h)).2
          have ex : x ∈ ua.1.leaves ↔ x ∈ a.leaves := by rw [la]; simp [hxk]
          have ey : y ∈ ua.1.leaves ↔ y ∈ a.leaves := by rw [la]; simp [hyk]
          have fx : x ∈ ub.1.leaves ↔ x ∈ b.leaves := by rw [lb]; simp [hxk]
          have fy : y ∈ ub.1.leaves ↔ y ∈ b.leaves := by rw [lb]; simp [hyk]
          simp only [pairAge,ex,ey,fx,fy]
          by_cases hal : x ∈ a.leaves ∧ y ∈ a.leaves
          · rw [if_pos hal,if_pos hal]
            exact iha d.2.1 ua ha (ex.mpr hal.1) (ey.mpr hal.2)
          · rw [if_neg hal,if_neg hal]
            by_cases hbl : x ∈ b.leaves ∧ y ∈ b.leaves
            · rw [if_pos hbl,if_pos hbl]
              exact ihb d.2.2 ub hb (fx.mpr hbl.1) (fy.mpr hbl.2)
            · simp only [if_neg hbl]

theorem prune_decode_pair_age (leafAge : Copy → ℝ) (keep : Finset Copy)
    (t : Genealogy Copy) (ht : t.WellLabelled) (d : Decoration t)
    (u : Decorated (Copy := Copy)) (hu : prune keep t d = some u) :
    decode (pairAge leafAge t d) u.1 = u.2 := by
  have hf := prune_forgets keep t d
  rw [hu] at hf
  have hw := Genealogy.prune_wellLabelled keep t ht
  rw [←hf] at hw
  apply decode_of_pair_agreement leafAge u.1 hw u.2
  intro x hx y hy
  exact (prune_preserves_pair_age leafAge keep t d u hu hx hy).symm

lemma decorated_mk_measurable (t : Genealogy Copy) : Measurable (Sigma.mk
    (β := fun t : Genealogy Copy => Decoration t) t) := by
  apply Measurable.of_le_map
  exact iInf_le _ t

/-- A varying source shape indexed by any countable measurable carrier is
allowed; in the actual application the terminal coded-state carrier is finite. -/
theorem decode_family_measurable {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (shape : S → Genealogy Copy) :
    Measurable (fun z : S × (Copy → Copy → ℝ) =>
      (⟨shape z.1,decode z.2 (shape z.1)⟩ : Decorated (Copy := Copy))) := by
  apply measurable_from_prod_countable_right
  intro s
  exact (decorated_mk_measurable (shape s)).comp (decode_measurable (shape s))

#print axioms prune_decode_pair_age
#print axioms decode_family_measurable
#print axioms prune_forgets
#print axioms prune_preserves_pair_age
end GProgram.G2.TimedDecorationPruning
