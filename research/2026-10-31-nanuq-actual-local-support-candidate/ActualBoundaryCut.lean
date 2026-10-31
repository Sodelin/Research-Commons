import ActualCutIntervals
import ActualPairCut

/-! UNCOMPILED adjacent-boundary identification. Four boundary incidences
pin the WHOLE original cut only after derived interval convexity; arbitrary
four-label restrictions are not promoted to whole splits. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open GProgram.G5.Normalization
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem actual_boundary_resolution_whole_cut (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (i j : Nat) (hij : i<j) (hjn : j<n)
    (q : Fin 4 ↪ X)
    (h0 : (rank (q 0)).val=i+1) (h1 : (rank (q 1)).val=j)
    (h2 : (rank (q 2)).val=i)
    (h3 : (rank (q 3)).val=if j+1=n then 0 else j+1)
    (hq : Resolution.xy_zw ∈ N.rawDisplayedQuartets q) :
    ∃ S : N.Switching, ∃ e : S.Edge,
      ((∀ x : X, S.graph.DReach (S.graph.target e) (N.leaf x) ↔
          i<(rank x).val ∧ (rank x).val≤j) ∨
       (∀ x : X, ¬S.graph.DReach (S.graph.target e) (N.leaf x) ↔
          i<(rank x).val ∧ (rank x).val≤j)) := by
  obtain ⟨S,e,hq⟩ := (actual_first_pair_cut_iff N q).mp hq
  have hne : (sampledDescendants N S Finset.univ (S.graph.target e)).Nonempty := by
    rcases hq with hq | hq
    · exact ⟨q 0,by simp [sampledDescendants,hq.1]⟩
    · exact ⟨q 2,by simp [sampledDescendants,hq.2.2.1]⟩
  have hproper : (Finset.univ \ sampledDescendants N S Finset.univ (S.graph.target e)).Nonempty := by
    rcases hq with hq | hq
    · exact ⟨q 2,by simp [sampledDescendants,hq.2.2.1]⟩
    · exact ⟨q 0,by simp [sampledDescendants,hq.1]⟩
  obtain ⟨a,b,hab,hbn,hor⟩ := actual_proper_cut_interval N n mask rank T hs hsets S e hne hproper
  let A := Finset.Ioc a b
  have hz : 0∉A := by simp [A]
  have hb : ∀ x∈A, x<n := by intro x hx; simp only [A,Finset.mem_Ioc] at hx; omega
  have hc : ∀ x y z : Nat, x∈A → z∈A → x≤y → y≤z → y∈A := by
    intro x y z hx hzs hxy hyz
    simp only [A,Finset.mem_Ioc] at hx hzs ⊢
    omega
  have hp :
      ((i+1∈A ∧ j∈A) ∧ (i∉A ∧ (if j+1=n then 0 else j+1)∉A)) ∨
      ((i∈A ∧ (if j+1=n then 0 else j+1)∈A) ∧ (i+1∉A ∧ j∉A)) := by
    rcases hor with hor | hor
    all_goals
      have ha0 := hor (rank (q 0))
      have ha1 := hor (rank (q 1))
      have ha2 := hor (rank (q 2))
      have ha3 := hor (rank (q 3))
      simp only [rank.symm_apply_apply,h0,h1,h2,h3] at ha0 ha1 ha2 ha3
      simp only [A,Finset.mem_Ioc]
      tauto
  have hA : A=Finset.Ioc i j := by
    rcases hp with hp | hp
    · exact boundary_pins_convex_side n i j hij hjn A hb hz hc hp.1 hp.2
    · exact False.elim (boundary_outer_orientation_impossible n i j hij A hz hc hp.1 hp.2.1)
  have hi (x : Fin n) : (a<x.val ∧ x.val≤b) ↔ (i<x.val ∧ x.val≤j) := by
    have hx : x.val∈A ↔ x.val∈Finset.Ioc i j := by rw [hA]
    simpa only [A,Finset.mem_Ioc] using hx
  refine ⟨S,e,?_⟩
  rcases hor with hor | hor
  · exact Or.inl (by intro x; simpa using (hor (rank x)).trans (hi (rank x)))
  · exact Or.inr (by intro x; simpa using (hor (rank x)).trans (hi (rank x)))

end Nanuq.ActualCutClusters
