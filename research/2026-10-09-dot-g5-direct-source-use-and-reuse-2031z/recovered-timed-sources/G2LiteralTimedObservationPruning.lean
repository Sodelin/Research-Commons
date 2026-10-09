import G2FaithfulTimedOutput

/-!
Literal pruning of the observed timed genealogy forest, retaining original ages.
Contributor: dot (OpenAI), 6 October 2026.
-/
namespace GProgram.G2.LiteralTimedObservationPruning
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.JointTimedObservation GProgram.G2.FaithfulTimedOutput
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma prune_all (t : Genealogy Copy) : t.prune Finset.univ = some t := by
  induction t with
  | leaf x => simp [Genealogy.prune]
  | graft a b ha hb => simp [Genealogy.prune,ha,hb,Genealogy.joinPruned]

lemma mem_forest_iff_live (s : State V E Copy) (hs : Valid s) (keep : Finset Copy)
    (q : UnrankedTree Copy) : q ∈ sourceUnrankedForest s keep ↔
      ∃ l ∈ s.live, optionUnranked ((s.genealogy l).prune keep) = some q := by
  constructor
  · exact forest_member_live_witness s hs keep
  · rintro ⟨l,hl,hq⟩
    cases hp : (s.genealogy l).prune keep with
    | none => simp [hp,optionUnranked] at hq
    | some t =>
        have hqt : toUnranked t = q := by simpa [hp,optionUnranked] using hq
        obtain ⟨x,hx⟩ := genealogy_leaves_nonempty t
        have he := Genealogy.prune_leaves keep (s.genealogy l)
        rw [hp] at he
        have hxl : x ∈ (s.genealogy l).leaves ∧ x ∈ keep := Finset.mem_inter.mp (he ▸ hx)
        have ha : s.ancestor x = l := (hs.leaf_fiber l hl x).mp hxl.1
        exact (mem_sourceUnrankedForest s keep q).mpr ⟨x,hxl.2,t,by simpa [ha] using hp,hqt⟩

noncomputable def pruneForest (keep : Finset Copy) (F : Finset (UnrankedTree Copy)) : Finset (UnrankedTree Copy) :=
  F.biUnion (fun q => match pruneTree keep q with | none => ∅ | some u => {u})

lemma mem_prune_forest (keep : Finset Copy) (F : Finset (UnrankedTree Copy)) (u : UnrankedTree Copy) :
    u ∈ pruneForest keep F ↔ ∃ q ∈ F, pruneTree keep q = some u := by
  simp only [pruneForest,Finset.mem_biUnion]
  apply exists_congr
  intro q
  apply and_congr_right
  intro _
  cases h : pruneTree keep q <;> simp [eq_comm]

/-- Forest-level deletion is the existing source observer's literal pruning;
no new tree or topology is fitted to selected pair ages. -/
theorem prune_source_forest (s : State V E Copy) (hs : Valid s) (keep : Finset Copy) :
    pruneForest keep (sourceUnrankedForest s Finset.univ) = sourceUnrankedForest s keep := by
  ext u
  rw [mem_prune_forest,mem_forest_iff_live s hs keep]
  constructor
  · rintro ⟨q,hq,hp⟩
    obtain ⟨l,hl,hq⟩ := (mem_forest_iff_live s hs Finset.univ q).mp hq
    have he : toUnranked (s.genealogy l) = q := by simpa [prune_all,optionUnranked] using hq
    exact ⟨l,hl,by simpa only [←he,prune_toUnranked] using hp⟩
  · rintro ⟨l,hl,hp⟩
    refine ⟨toUnranked (s.genealogy l),?_,hp⟩
    apply (mem_forest_iff_live s hs Finset.univ _).mpr
    exact ⟨l,hl,by simp [prune_all,optionUnranked]⟩

noncomputable def pruneTimedObservation (keep : Finset Copy) (o : TimedObservation Copy) : TimedObservation Copy :=
  (o.1.map (pruneForest keep),fun x y => if x ∈ keep ∧ y ∈ keep then o.2 x y else (false,0))

theorem prune_matrix_observation (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) (M : Copy → Copy → ℝ) :
    pruneTimedObservation keep (matrixObservation N Finset.univ s M) = matrixObservation N keep s M := by
  apply Prod.ext
  · exact congrArg some (prune_source_forest (state s) s.property.forest keep)
  · funext x y
    simp only [pruneTimedObservation,matrixObservation,Finset.mem_univ,and_self,if_true]

#print axioms prune_source_forest
#print axioms prune_matrix_observation
end GProgram.G2.LiteralTimedObservationPruning
