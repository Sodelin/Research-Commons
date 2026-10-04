import G5OriginalTipRepresentativeDeletion

/-!
# Finite attained original-tip deletion chronology
Contributor: dot / OpenAI, 2026-10-03.
Every step uses the constructed first attained age and all simultaneous exact
blocks. The final single original representative and the |B|-1 deletion-step
bound are derived by cardinal descent, with no supplied chronology field.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [LinearOrder X]

/-- A trace records the actual recursive deletion operation. It never replaces
the original graph, leaf labels, rates, calendar or parent registry. -/
inductive DeletionTrace (N : RootedBinary V E X) (C : Calendar N.graph) :
    Finset X → ℝ → Finset X → ℝ → Nat → Prop
  | terminal (B : Finset X) (s : ℝ) (hB : B.card = 1) : DeletionTrace N C B s B s 0
  | step (B : Finset X) (s : ℝ) (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card)
      {F : Finset X} {u : ℝ} {n : Nat}
      (rest : DeletionTrace N C
        (survivors N C B (firstGroupingAge N C B hs hc))
        (firstGroupingAge N C B hs hc) F u n) : DeletionTrace N C B s F u (n+1)

/-- The final singleton exists, remains safe, and occurs after at most |B|-1
simultaneous deletion stages. For an original quartet this gives at most three. -/
theorem finite_safe_attained_deletion_trace (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hB : B.Nonempty)
    (hstart : SafeAt N C B s) :
    ∃ F u n, DeletionTrace N C B s F u n ∧ F.card = 1 ∧ F ⊆ B ∧
      s ≤ u ∧ u ≤ C.age N.root ∧ SafeAt N C F u ∧ n ≤ B.card-1 := by
  have aux : ∀ k : Nat, ∀ B : Finset X, B.card = k → ∀ s : ℝ,
      s ≤ C.age N.root → B.Nonempty → SafeAt N C B s →
      ∃ F u n, DeletionTrace N C B s F u n ∧ F.card = 1 ∧ F ⊆ B ∧
        s ≤ u ∧ u ≤ C.age N.root ∧ SafeAt N C F u ∧ n ≤ B.card-1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro B hk s hs hB hstart
      by_cases hc : 2 ≤ B.card
      · let τ := firstGroupingAge N C B hs hc
        let B' := survivors N C B τ
        have hat := firstGroupingAge_attained N C B hs hc
        have hd := attained_deletion_safe_and_descends N C hcut B hs hc hstart
        have hlt : B'.card < B.card := hd.2
        have hB' : B'.Nonempty := by
          obtain ⟨D,hDB,hD,hblock⟩ := hat.2.2.2
          have hmem := (mem_simultaneousBlocks N C B D τ).mpr ⟨hDB,hD,hblock⟩
          exact ⟨originalRepresentative D hD,representative_survives N C B D τ hmem⟩
        obtain ⟨F,u,n,htrace,hF,hFB',hτu,hu,hFs,hbound⟩ :=
          ih B'.card (by omega) B' rfl τ hat.2.2.1 hB' hd.1
        refine ⟨F,u,n+1,DeletionTrace.step B s hs hc htrace,hF,
          hFB'.trans (survivors_subset N C B τ),hat.2.1.trans hτu,hu,hFs,?_⟩
        omega
      · have hcard : B.card = 1 := by have hp := Finset.card_pos.mpr hB; omega
        exact ⟨B,s,0,DeletionTrace.terminal B s hcard,hcard,Finset.Subset.refl _,le_rfl,hs,hstart,by omega⟩
  exact aux B.card B rfl s hs hB hstart

/-- Initial entire-past safety is constructed from the actual sampling ages. -/
theorem contemporaneous_original_tip_chronology (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s : ℝ} (hB : B.Nonempty)
    (htips : ∀ x ∈ B, C.age (N.leaf x) = s) :
    ∃ F u n, DeletionTrace N C B s F u n ∧ F.card = 1 ∧ F ⊆ B ∧
      s ≤ u ∧ u ≤ C.age N.root ∧ SafeAt N C F u ∧ n ≤ B.card-1 := by
  have hs : s ≤ C.age N.root := by
    obtain ⟨x,hx⟩ := hB
    rw [←htips x hx]
    exact C.age_le_of_directed (N.rooted (N.leaf x))
  exact finite_safe_attained_deletion_trace N C hcut B hs hB (safeAt_sampling_age N C B s htips)

theorem quartet_original_tip_chronology (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (A : Finset X) {s : ℝ} (hA : A.card = 4)
    (htips : ∀ x ∈ A, C.age (N.leaf x) = s) :
    ∃ F u n, DeletionTrace N C A s F u n ∧ F.card = 1 ∧ F ⊆ A ∧
      s ≤ u ∧ u ≤ C.age N.root ∧ SafeAt N C F u ∧ n ≤ 3 := by
  have hn : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨F,u,n,ht,hF,hFA,hsu,hu,hFs,hbound⟩ := contemporaneous_original_tip_chronology N C hcut A hn htips
  exact ⟨F,u,n,ht,hF,hFA,hsu,hu,hFs,by omega⟩

#print axioms finite_safe_attained_deletion_trace
#print axioms contemporaneous_original_tip_chronology
#print axioms quartet_original_tip_chronology
end GProgram.G5.AttainedChronology
