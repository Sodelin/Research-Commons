import G7NaturalWordRelabelling
import G7BoundaryPhasePermutation

/-! Exact original node compiler transport. The nonhybrid selector is handled
by its indegree-one uniqueness, not by an equivariance assumption on choice.
Contributor: dot, 2026-10-09. -/
namespace GProgram.G7.CalendarNodeRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceBoundaryKernels
open GProgram.G7.OriginalRelabelling
open scoped Classical
variable {V E W F X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]

theorem incoming_unique (G : EdgeGraph V E) (a : V) (h : G.inDegree a = 1)
    (f g : E) (hf : G.target f = a) (hg : G.target g = a) : f = g := by
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp h
  have hfm : f ∈ Finset.univ.filter (fun e => G.target e = a) := by simp [hf]
  have hgm : g ∈ Finset.univ.filter (fun e => G.target e = a) := by simp [hg]
  rw [hj] at hfm hgm
  exact (Finset.mem_singleton.mp hfm).trans (Finset.mem_singleton.mp hgm).symm

theorem ordinary_selector (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (a : V) (hr : a ≠ N.root) (hh : ¬ N.graph.IsHybrid a)
    (hr' : v a ≠ (network N v e).root) :
    e ((defaultSelector N).edge ⟨a,hr⟩) =
      (defaultSelector (network N v e)).edge ⟨v a,hr'⟩ := by
  apply incoming_unique (network N v e).graph (v a)
  · simpa [network] using nonhybrid_nonroot_indegree_one N a hr hh
  · simp only [network,graph_target,Equiv.symm_apply_apply]
    exact congrArg v ((defaultSelector N).target ⟨a,hr⟩)
  · exact (defaultSelector (network N v e)).target _

def gamma (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (g : Hybrid N → unitInterval) : Hybrid (network N v e) → unitInterval :=
  fun h => g ((hybrids N v e).symm h)

def common (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Hybrid N → Bool) : Hybrid (network N v e) → Bool :=
  fun h => c ((hybrids N v e).symm h)

theorem node_operation (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (H : OriginalParentRegistry N) (g : Hybrid N → unitInterval)
    (c : Hybrid N → Bool) (a : V) :
    GProgram.G7.BoundaryRelabelling.operation N v e (originalNodeOperation N H g c a) =
      originalNodeOperation (network N v e) (registry N v e H)
        (gamma N v e g) (common N v e c) (v a) := by
  by_cases hr : a = N.root
  · subst a
    simp [originalNodeOperation,network,GProgram.G7.BoundaryRelabelling.operation]
  · have hr' : v a ≠ (network N v e).root := by
      exact fun he => hr (v.injective he)
    by_cases hh : N.graph.IsHybrid a
    · have hh' : (network N v e).graph.IsHybrid (v a) := by simpa [network] using hh
      cases hc : c ⟨a,hh⟩ <;>
        simp [originalNodeOperation,hr,hr',hh,hh',hc,gamma,common,registry,hybrids,
          GProgram.G7.BoundaryRelabelling.operation]
    · have hh' : ¬ (network N v e).graph.IsHybrid (v a) := by simpa [network] using hh
      simp only [originalNodeOperation,dif_neg hr,dif_neg hr',dif_neg hh,dif_neg hh',
        GProgram.G7.BoundaryRelabelling.operation]
      congr 1
      exact ordinary_selector N v e a hr hh hr'

#print axioms ordinary_selector
#print axioms node_operation
end GProgram.G7.CalendarNodeRelabelling
