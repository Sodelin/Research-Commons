import G7GlobalOwnerCoins
import UnifiedLean.Source.SourceCalendarCompiler

/-! Actual node-phase source operations on a fixed coin carrier. This is the
source-specific interface for tied-node kernel commutation, not a desired-law
axiom. Contributor: dot, 2026-10-09. -/
namespace GProgram.G7.NodeActions
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open GProgram.G7.GlobalOwnerCoins
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceForestPulseTransport
open scoped Classical
variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [Fintype Copy] [DecidableEq Copy]

inductive Action (N : RootedBinary V E X)
  | ordinary (edge : E) (degree : N.graph.inDegree (N.graph.target edge) = 1)
  | root
  | independent (parents : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
  | common (parents : GProgram.G2.OriginalHybridParents N)

def site {N : RootedBinary V E X} : Action N → V
  | .ordinary e _ => N.graph.target e
  | .root => N.root
  | .independent H _ => H.hybrid
  | .common H => H.hybrid

def operation {N : RootedBinary V E X} : Action N → BoundaryOperation N
  | .ordinary e h => .ordinary e h
  | .root => .root
  | .independent H gamma => .independent H gamma
  | .common H => .common H

noncomputable def coinLaw {N : RootedBinary V E X} : Action N → PMF (Copy → Bool)
  | .independent _ gamma => currentCoinPMF Copy gamma
  | _ => PMF.pure (fun _ => false)

noncomputable def destination {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) (c : Copy → Bool) : Code N sample :=
  match a with
  | .ordinary e _ => ordinaryCode N s e
  | .root => rootCode N s
  | .independent H _ => pulseCode H s (restrictOwners N s H.hybrid c)
  | .common H => pulseCode H s (fun _ => (state s).register H.hybrid)

def target {N : RootedBinary V E X} (a : Action N) (reg : V → Bool)
    (c : Copy → Bool) (l : Copy) : Location V E :=
  match a with
  | .ordinary e _ => .edge e
  | .root => .rootPopulation N.root
  | .independent H _ => .edge (H.parent (c l))
  | .common H => .edge (H.parent (reg H.hybrid))

def route {N : RootedBinary V E X} (a : Action N) (reg : V → Bool)
    (c : Copy → Bool) (l : Copy) (loc : Location V E) : Location V E :=
  if loc = .node (site a) then target a reg c l else loc

@[simp] theorem target_not_node {N : RootedBinary V E X} (a : Action N)
    (reg : V → Bool) (c : Copy → Bool) (l : Copy) (v : V) :
    target a reg c l ≠ .node v := by
  cases a <;> simp [target]

theorem route_commute {N : RootedBinary V E X} (a b : Action N) (h : site a ≠ site b)
    (reg : V → Bool) (c d : Copy → Bool) (l : Copy) (loc : Location V E) :
    route b reg d l (route a reg c l loc) = route a reg c l (route b reg d l loc) := by
  by_cases ha : loc = .node (site a)
  · subst loc
    simp [route,h,Ne.symm h]
  · by_cases hb : loc = .node (site b)
    · subst loc
      simp [route,h,Ne.symm h]
    · simp [route,ha,hb]

theorem kernel_fixed_carrier {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) :
    boundaryKernel N (operation a) s = (coinLaw (Copy:=Copy) a).map (destination a s) := by
  cases a with
  | ordinary e h => simp [operation,boundaryKernel,coinLaw,destination,PMF.pure_map]
  | root => simp [operation,boundaryKernel,coinLaw,destination,PMF.pure_map]
  | common H => simp [operation,boundaryKernel,coinLaw,destination,PMF.pure_map]
  | independent H gamma => exact independent_pulse_fixed_carrier H gamma s

@[simp] theorem destination_live {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) (c : Copy → Bool) :
    (state (destination a s c)).live = (state s).live := by
  cases a <;> rfl

@[simp] theorem destination_ancestor {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) (c : Copy → Bool) :
    (state (destination a s c)).ancestor = (state s).ancestor := by
  cases a <;> rfl

@[simp] theorem destination_register {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) (c : Copy → Bool) :
    (state (destination a s c)).register = (state s).register := by
  cases a <;> rfl

theorem destination_genealogy {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) (c : Copy → Bool) (l : Copy) :
    (state (destination a s c)).genealogy l =
      if l ∈ (state s).live then (state s).genealogy l else .leaf l := by
  by_cases hl : l ∈ (state s).live
  · cases a <;> simp [destination,ordinaryCode,rootCode,pulseCode,admittedCode,state,
      encodeSnapshot,decodeSnapshot,enterEdge,enterRoot,pulse,transport] at hl ⊢ <;> simp [hl]
  · cases a <;> simp [destination,ordinaryCode,rootCode,pulseCode,admittedCode,state,
      encodeSnapshot,decodeSnapshot,enterEdge,enterRoot,pulse,transport] at hl ⊢ <;> simp [hl]

theorem destination_location {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) (c : Copy → Bool) (l : Copy) :
    (state (destination a s c)).location l =
      if l ∈ (state s).live then route a (state s).register c l ((state s).location l)
      else .node N.root := by
  by_cases hl : l ∈ (state s).live
  · cases a <;> simp [destination,ordinaryCode,rootCode,pulseCode,admittedCode,state,
      encodeSnapshot,decodeSnapshot,enterEdge,enterRoot,pulse,transport,route,site,target,
      restrictOwners] at hl ⊢ <;> simp [hl]
  · cases a <;> simp [destination,ordinaryCode,rootCode,pulseCode,admittedCode,state,
      encodeSnapshot,decodeSnapshot,enterEdge,enterRoot,pulse,transport,route,site,target,
      restrictOwners] at hl ⊢ <;> simp [hl]


/-- Normalization is a property of constructed source snapshots, not an
assumption that arbitrary unused snapshot entries encode physical data. -/
def Canonical {N : RootedBinary V E X} {sample : Copy → X} (s : Code N sample) : Prop :=
  encodeSnapshot (state s) s.property.forest = s.val

theorem admitted_canonical (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) :
    Canonical (admittedCode N sample s hs) := by
  apply Snapshot.ext
  · rfl
  · rfl
  · funext l
    by_cases hl : l ∈ s.live
    · simp [Canonical,admittedCode,state,encodeSnapshot,decodeSnapshot,hl]
    · simp [Canonical,admittedCode,state,encodeSnapshot,decodeSnapshot,hl]
  · funext l
    by_cases hl : l ∈ s.live <;>
      simp [Canonical,admittedCode,state,encodeSnapshot,decodeSnapshot,hl]
  · rfl

theorem canonical_ext {N : RootedBinary V E X} {sample : Copy → X}
    (s t : Code N sample) (hs : Canonical s) (ht : Canonical t)
    (h : state s = state t) : s = t := by
  apply Subtype.ext
  exact hs.symm.trans ((congrArg Subtype.val
    (GProgram.G7.BoundaryRelabelling.admitted_congr N sample (state s) (state t) s.property t.property h)).trans ht)

theorem destination_canonical {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (s : Code N sample) (c : Copy → Bool) :
    Canonical (destination a s c) := by
  cases a with
  | ordinary e h => exact admitted_canonical N sample _ (enterEdge_source_valid N sample _ s.property e)
  | root => exact admitted_canonical N sample _ (enterRoot_source_valid N sample _ s.property)
  | independent H gamma => exact admitted_canonical N sample _ (pulse_source_valid H sample _ s.property _)
  | common H => exact admitted_canonical N sample _ (pulse_source_valid H sample _ s.property _)

theorem state_ext (s t : State V E Copy)
    (hl : s.live = t.live) (ha : s.ancestor = t.ancestor)
    (hg : s.genealogy = t.genealogy) (hp : s.location = t.location)
    (hr : s.register = t.register) (hh : s.history = t.history) : s = t := by
  cases s
  cases t
  simp_all

theorem destination_commute {N : RootedBinary V E X} {sample : Copy → X}
    (a b : Action N) (h : site a ≠ site b) (s : Code N sample) (c d : Copy → Bool) :
    destination b (destination a s c) d = destination a (destination b s d) c := by
  apply canonical_ext _ _ (destination_canonical _ _ _) (destination_canonical _ _ _)
  apply state_ext
  · simp
  · simp
  · funext l
    simp only [destination_genealogy,destination_live]
  · funext l
    simp only [destination_location,destination_live,destination_register]
    by_cases hl : l ∈ (state s).live
    · simp only [hl,if_pos]
      exact route_commute a b h _ c d l _
    · simp [hl]
  · simp
  · rfl

/-- Only distinct NODE operations commute. The exits phase must stay earlier. -/
theorem kernels_commute {N : RootedBinary V E X} {sample : Copy → X}
    (a b : Action N) (h : site a ≠ site b) (s : Code N sample) :
    (boundaryKernel N (operation a) s).bind (boundaryKernel N (operation b)) =
      (boundaryKernel N (operation b) s).bind (boundaryKernel N (operation a)) := by
  simp_rw [kernel_fixed_carrier]
  rw [PMF.bind_map,PMF.bind_map]
  change ((coinLaw (Copy:=Copy) a).bind (fun c => boundaryKernel N (operation b) (destination a s c))) =
    (coinLaw (Copy:=Copy) b).bind (fun d => boundaryKernel N (operation a) (destination b s d))
  simp_rw [kernel_fixed_carrier]
  have hc := PMF.bind_comm (coinLaw (Copy:=Copy) a) (coinLaw (Copy:=Copy) b)
    (fun c d => PMF.pure (destination b (destination a s c) d))
  simpa only [PMF.map,Function.comp_def,destination_commute a b h] using hc


open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open GProgram.SourceForestKingmanPopulationProjection

noncomputable def originalAction (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) : Action N :=
  if hr : v = N.root then .root
  else if hh : N.graph.IsHybrid v then
    if common ⟨v,hh⟩ then .common (H.parents ⟨v,hh⟩)
    else .independent (H.parents ⟨v,hh⟩) (gamma ⟨v,hh⟩)
  else .ordinary ((defaultSelector N).edge ⟨v,hr⟩) (by
    rw [(defaultSelector N).target]
    exact nonhybrid_nonroot_indegree_one N v hr hh)

theorem original_operation (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) :
    operation (originalAction N H gamma common v) = originalNodeOperation N H gamma common v := by
  by_cases hr : v = N.root
  · simp [originalAction,originalNodeOperation,hr,operation]
  · by_cases hh : N.graph.IsHybrid v
    · cases hc : common ⟨v,hh⟩ <;> simp [originalAction,originalNodeOperation,hr,hh,hc,operation]
    · simp [originalAction,originalNodeOperation,hr,hh,operation]

theorem original_site (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) : site (originalAction N H gamma common v) = v := by
  unfold originalAction
  split
  · rename_i h
    exact h.symm
  · split
    · split <;> exact H.original_site _
    · exact (defaultSelector N).target _

#print axioms kernel_fixed_carrier
#print axioms destination_location
#print axioms kernels_commute
#print axioms original_operation
#print axioms original_site
end GProgram.G7.NodeActions
