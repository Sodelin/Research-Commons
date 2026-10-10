import G7SnapshotRelabelling
import G7CoinReindexing

/-!
Actual original boundary-kernel intertwining under graph relabelling.
Contributor: dot, 2026-10-09. This is a derived full finite-state law, with
current-owner independent coins and the same original COMMON register.
-/
namespace GProgram.G7.BoundaryRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.G7.OriginalRelabelling
open GProgram.G7.SnapshotRelabelling
open GProgram.G7.CoinReindexing
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open scoped Classical
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

theorem admitted_congr (N : RootedBinary V E X) (sample : Copy → X)
    (s t : State V E Copy) (hs : SourceValid N sample s) (ht : SourceValid N sample t)
    (he : s = t) : admittedCode N sample s hs = admittedCode N sample t ht := by
  subst t
  rfl

theorem pulse_state_congr (N : RootedBinary V E X) (H : GProgram.G2.OriginalHybridParents N)
    (s t : State V E Copy) (he : s = t)
    (c : AtNode s H.hybrid → Bool) (d : AtNode t H.hybrid → Bool)
    (hc : ∀ a b, a.val = b.val → c a = d b) : pulse H s c = pulse H t d := by
  subst t
  have hcd : c = d := funext (fun a => hc a a rfl)
  rw [hcd]

def operation (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) :
    BoundaryOperation N → BoundaryOperation (network N v e)
  | .exit f => .exit (e f)
  | .ordinary f h => .ordinary (e f) (by simpa [network] using h)
  | .root => .root
  | .independent H g => .independent (parents N v e H) g
  | .common H => .common (parents N v e H)

theorem exit_code (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (f : E) :
    code N v e (exitCode N s f) = exitCode (network N v e) (code N v e s) (e f) := by
  unfold exitCode
  rw [admittedCode_commutes]
  have hs := GProgram.G7.SourceStateRelabelling.exitEdge_commutes N v e (state s) f
  rw [← code_state N v e s] at hs
  exact admitted_congr _ _ _ _ _ _ hs

theorem ordinary_code (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (f : E) :
    code N v e (ordinaryCode N s f) = ordinaryCode (network N v e) (code N v e s) (e f) := by
  unfold ordinaryCode
  rw [admittedCode_commutes]
  have hs := GProgram.G7.SourceStateRelabelling.enterEdge_commutes N v e (state s) f
  rw [← code_state N v e s] at hs
  exact admitted_congr _ _ _ _ _ _ hs

theorem root_code (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) :
    code N v e (rootCode N s) = rootCode (network N v e) (code N v e s) := by
  unfold rootCode
  rw [admittedCode_commutes]
  have hs := GProgram.G7.SourceStateRelabelling.enterRoot_commutes N v e (state s)
  rw [← code_state N v e s] at hs
  exact admitted_congr _ _ _ _ _ _ hs

def owners (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (H : GProgram.G2.OriginalHybridParents N) :
    AtNode (state s) H.hybrid ≃ AtNode (state (code N v e s)) (parents N v e H).hybrid where
  toFun l := ⟨l.val,by
    rw [code_state]
    exact (GProgram.G7.SourceStateRelabelling.atNodeEquiv v e (state s) H.hybrid l).property⟩
  invFun l := ⟨l.val,by
    have hl := l.property
    have hl' : l.val ∈ (GProgram.G7.SourceStateRelabelling.state v e (state s)).live ∧
        (GProgram.G7.SourceStateRelabelling.state v e (state s)).location l.val = .node (v H.hybrid) := by
      simpa only [code_state,parents] using hl
    exact ((GProgram.G7.SourceStateRelabelling.atNodeEquiv v e (state s) H.hybrid).symm ⟨l.val,hl'⟩).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem pulse_code (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (H : GProgram.G2.OriginalHybridParents N)
    (coin : AtNode (state s) H.hybrid → Bool) :
    code N v e (pulseCode H s coin) =
      pulseCode (parents N v e H) (code N v e s) (coinTransport (owners N v e s H) coin) := by
  unfold pulseCode
  rw [admittedCode_commutes]
  have hs : GProgram.G7.SourceStateRelabelling.state v e (pulse H (state s) coin) =
      pulse (parents N v e H) (state (code N v e s)) (coinTransport (owners N v e s H) coin) := by
    apply (GProgram.G7.SourceStateRelabelling.pulse_commutes N v e H (state s) coin).trans
    apply pulse_state_congr (network N v e) (parents N v e H) _ _ (code_state N v e s).symm
    intro a b hab
    apply congrArg coin
    apply Subtype.ext
    exact hab
  exact admitted_congr _ _ _ _ _ _ hs

theorem independent_kernel (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (H : GProgram.G2.OriginalHybridParents N)
    (gamma : unitInterval) :
    (independentPulseKernel H gamma s).map (code N v e) =
      independentPulseKernel (parents N v e H) gamma (code N v e s) := by
  unfold independentPulseKernel
  rw [PMF.map_comp]
  have hf : (code N v e ∘ pulseCode H s) =
      pulseCode (parents N v e H) (code N v e s) ∘ coinTransport (owners N v e s H) := by
    funext coin
    exact pulse_code N v e s H coin
  rw [hf,← PMF.map_comp,current_coin_pmf]

theorem boundary_kernel (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (op : BoundaryOperation N) :
    (boundaryKernel N op s).map (code N v e) =
      boundaryKernel (network N v e) (operation N v e op) (code N v e s) := by
  cases op with
  | exit f => simp only [boundaryKernel,operation,PMF.pure_map,exit_code]
  | ordinary f h => simp only [boundaryKernel,operation,PMF.pure_map,ordinary_code]
  | root => simp only [boundaryKernel,operation,PMF.pure_map,root_code]
  | independent H gamma => exact independent_kernel N v e s H gamma
  | common H =>
    simp only [boundaryKernel,operation,PMF.pure_map,pulse_code]
    congr 2
    funext l
    simp [coinTransport,code_state,GProgram.G7.SourceStateRelabelling.state,parents]

#print axioms independent_kernel
#print axioms boundary_kernel
end GProgram.G7.BoundaryRelabelling
