import NonrootTwoPortBigon
import Mathlib.Logic.Equiv.Basic

/-!
Original parallel-arm switching transport, Cloud structural source lane.
8 October 2026, 02:37 UTC. Compiler UNCHECKED; outside actual166/proposed176.

The original Switching ordinary/hybrid fields construct the flipped
switching. An actual edge-occurrence equivalence fixes every vertex and
preserves both original endpoint maps. Adjacency/reachability follow.
The genuine arm witness is derived from actual nonroot two-port blobs.
No supplied displayed-target equality, suppression or replacement graph.
-/

namespace UnifiedLean.G6.ParallelArmSwitching

open Nanuq.Source

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X}

/-- Narrow actual graph data consumed by the arm flip. Its existence for
the source component is DERIVED below, not a decomposition premise. -/
structure OriginalParallelArms (N : RootedBinary V E X) where
  entry : V
  hybrid : V
  arm0 : E
  arm1 : E
  arm_ne : arm0 ≠ arm1
  entry_degrees : N.graph.inDegree entry = 1 ∧ N.graph.outDegree entry = 2
  isHybrid : N.graph.IsHybrid hybrid
  source0 : N.graph.source arm0 = entry
  source1 : N.graph.source arm1 = entry
  target0 : N.graph.target arm0 = hybrid
  target1 : N.graph.target arm1 = hybrid

/-- The accepted actual two-port classification constructs the witness. -/
theorem actual_parallel_arms_nonempty (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2) :
    Nonempty (OriginalParallelArms N) := by
  obtain ⟨r, h, e₀, e₁, _, hrd, hh, _, hne, hs₀, ht₀, hs₁, ht₁, _⟩ :=
    NonrootTwoPortBigon.actual_nonroot_two_port_bigon N hcut b hb hp
  exact ⟨{ entry := r, hybrid := h, arm0 := e₀, arm1 := e₁,
    arm_ne := hne, entry_degrees := hrd, isHybrid := hh,
    source0 := hs₀, source1 := hs₁, target0 := ht₀, target1 := ht₁ }⟩

/-- Degree two and distinct original arm IDs exhaust actual incoming occurrences. -/
theorem incoming_iff_arm (P : OriginalParallelArms N) (e : E) :
    N.graph.target e = P.hybrid ↔ e = P.arm0 ∨ e = P.arm1 := by
  classical
  have hset : ({P.arm0, P.arm1} : Finset E) =
      Finset.univ.filter (fun f => N.graph.target f = P.hybrid) := by
    apply Finset.eq_of_subset_of_card_le
    · intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · simp [P.target0]
      · simp [P.target1]
    · rw [show (Finset.univ.filter (fun f => N.graph.target f = P.hybrid)).card = 2
        from P.isHybrid.1]
      simp [P.arm_ne]
  constructor
  · intro he
    have hm : e ∈ Finset.univ.filter (fun f => N.graph.target f = P.hybrid) := by
      simp [he]
    rw [← hset] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  · rintro (rfl | rfl)
    · exact P.target0
    · exact P.target1

/-- Exactly one original arm is selected, from actual hybrid uniqueness. -/
theorem selected_arm_exactly_one (P : OriginalParallelArms N) (S : N.Switching) :
    (S.keep P.arm0 ∧ ¬ S.keep P.arm1) ∨
      (¬ S.keep P.arm0 ∧ S.keep P.arm1) := by
  obtain ⟨e, he, hk, hu⟩ := S.hybrid_unique P.hybrid P.isHybrid
  rcases (incoming_iff_arm P e).mp he with he₀ | he₁
  · subst e
    left
    refine ⟨hk, ?_⟩
    intro hk₁
    exact P.arm_ne (hu P.arm1 P.target1 hk₁).symm
  · subst e
    right
    refine ⟨?_, hk⟩
    intro hk₀
    exact P.arm_ne (hu P.arm0 P.target0 hk₀)

noncomputable def armSwap (P : OriginalParallelArms N) : E ≃ E := by
  classical
  exact Equiv.swap P.arm0 P.arm1

theorem armSwap_arm0 (P : OriginalParallelArms N) : armSwap P P.arm0 = P.arm1 := by
  classical
  exact Equiv.swap_apply_left _ _

theorem armSwap_arm1 (P : OriginalParallelArms N) : armSwap P P.arm1 = P.arm0 := by
  classical
  exact Equiv.swap_apply_right _ _

theorem armSwap_off (P : OriginalParallelArms N) (e : E)
    (h₀ : e ≠ P.arm0) (h₁ : e ≠ P.arm1) : armSwap P e = e := by
  classical
  exact Equiv.swap_apply_of_ne_of_ne h₀ h₁

theorem armSwap_involutive (P : OriginalParallelArms N) (e : E) :
    armSwap P (armSwap P e) = e := by
  classical
  exact Equiv.swap_apply_self _ _ _

theorem armSwap_source (P : OriginalParallelArms N) (e : E) :
    N.graph.source (armSwap P e) = N.graph.source e := by
  classical
  exact Equiv.apply_swap_eq_self (P.source0.trans P.source1.symm) e

theorem armSwap_target (P : OriginalParallelArms N) (e : E) :
    N.graph.target (armSwap P e) = N.graph.target e := by
  classical
  exact Equiv.apply_swap_eq_self (P.target0.trans P.target1.symm) e

/-- Construct the other actual switching; original ordinary retention and
one-incoming-occurrence hybrid uniqueness are PROVED for this keep predicate. -/
noncomputable def flippedSwitching (P : OriginalParallelArms N) (S : N.Switching) :
    N.Switching where
  keep e := S.keep (armSwap P e)
  ordinary e hn := S.ordinary (armSwap P e) (by rw [armSwap_target]; exact hn)
  hybrid_unique a ha := by
    obtain ⟨e, he, hk, hu⟩ := S.hybrid_unique a ha
    refine ⟨armSwap P e, ?_, ?_, ?_⟩
    · rw [armSwap_target]
      exact he
    · rw [armSwap_involutive]
      exact hk
    · intro f hf hkf
      have hfe : armSwap P f = e := hu (armSwap P f)
        (by rw [armSwap_target]; exact hf) hkf
      calc
        f = armSwap P (armSwap P f) := (armSwap_involutive P f).symm
        _ = armSwap P e := congrArg (armSwap P) hfe

theorem flipped_keep_arm0 (P : OriginalParallelArms N) (S : N.Switching) :
    (flippedSwitching P S).keep P.arm0 ↔ S.keep P.arm1 := by
  change S.keep (armSwap P P.arm0) ↔ S.keep P.arm1
  rw [armSwap_arm0]

theorem flipped_keep_arm1 (P : OriginalParallelArms N) (S : N.Switching) :
    (flippedSwitching P S).keep P.arm1 ↔ S.keep P.arm0 := by
  change S.keep (armSwap P P.arm1) ↔ S.keep P.arm0
  rw [armSwap_arm1]

theorem flipped_keep_off (P : OriginalParallelArms N) (S : N.Switching) (e : E)
    (h₀ : e ≠ P.arm0) (h₁ : e ≠ P.arm1) :
    (flippedSwitching P S).keep e ↔ S.keep e := by
  change S.keep (armSwap P e) ↔ S.keep e
  rw [armSwap_off P e h₀ h₁]

theorem flipped_ordinary_retained (P : OriginalParallelArms N) (S : N.Switching)
    (e : E) (hn : ¬ N.graph.IsHybrid (N.graph.target e)) :
    S.keep e ∧ (flippedSwitching P S).keep e :=
  ⟨S.ordinary e hn, (flippedSwitching P S).ordinary e hn⟩

/-- Original selected edge occurrences are bijective, not identified by endpoints. -/
noncomputable def selectedEdgeEquiv (P : OriginalParallelArms N) (S : N.Switching) :
    S.Edge ≃ (flippedSwitching P S).Edge where
  toFun e := ⟨armSwap P e.val, by
    change S.keep (armSwap P (armSwap P e.val))
    rw [armSwap_involutive]
    exact e.property⟩
  invFun e := ⟨armSwap P e.val, e.property⟩
  left_inv e := Subtype.ext (armSwap_involutive P e.val)
  right_inv e := Subtype.ext (armSwap_involutive P e.val)

theorem selectedEdgeEquiv_source (P : OriginalParallelArms N) (S : N.Switching)
    (e : S.Edge) : (flippedSwitching P S).graph.source (selectedEdgeEquiv P S e) =
      S.graph.source e := armSwap_source P e.val

theorem selectedEdgeEquiv_target (P : OriginalParallelArms N) (S : N.Switching)
    (e : S.Edge) : (flippedSwitching P S).graph.target (selectedEdgeEquiv P S e) =
      S.graph.target e := armSwap_target P e.val

theorem selectedEdgeEquiv_symm_source (P : OriginalParallelArms N) (S : N.Switching)
    (e : (flippedSwitching P S).Edge) :
    S.graph.source ((selectedEdgeEquiv P S).symm e) =
      (flippedSwitching P S).graph.source e := armSwap_source P e.val

theorem selectedEdgeEquiv_symm_target (P : OriginalParallelArms N) (S : N.Switching)
    (e : (flippedSwitching P S).Edge) :
    S.graph.target ((selectedEdgeEquiv P S).symm e) =
      (flippedSwitching P S).graph.target e := armSwap_target P e.val

theorem flipped_dstep_iff (P : OriginalParallelArms N) (S : N.Switching) (a b : V) :
    (flippedSwitching P S).graph.DStep a b ↔ S.graph.DStep a b := by
  constructor
  · rintro ⟨e, hs, ht⟩
    exact ⟨(selectedEdgeEquiv P S).symm e,
      (selectedEdgeEquiv_symm_source P S e).trans hs,
      (selectedEdgeEquiv_symm_target P S e).trans ht⟩
  · rintro ⟨e, hs, ht⟩
    exact ⟨selectedEdgeEquiv P S e,
      (selectedEdgeEquiv_source P S e).trans hs,
      (selectedEdgeEquiv_target P S e).trans ht⟩

theorem flipped_dreach_iff (P : OriginalParallelArms N) (S : N.Switching) (a b : V) :
    (flippedSwitching P S).graph.DReach a b ↔ S.graph.DReach a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact ih.tail ((flipped_dstep_iff P S _ _).mp hab)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact ih.tail ((flipped_dstep_iff P S _ _).mpr hab)

theorem selectedEdgeEquiv_inc_iff (P : OriginalParallelArms N) (S : N.Switching)
    (e : S.Edge) (a b : V) :
    (flippedSwitching P S).graph.Inc (selectedEdgeEquiv P S e) a b ↔
      S.graph.Inc e a b := by
  simp only [EdgeGraph.Inc, selectedEdgeEquiv_source, selectedEdgeEquiv_target]

theorem selectedEdgeEquiv_symm_inc_iff (P : OriginalParallelArms N) (S : N.Switching)
    (e : (flippedSwitching P S).Edge) (a b : V) :
    S.graph.Inc ((selectedEdgeEquiv P S).symm e) a b ↔
      (flippedSwitching P S).graph.Inc e a b := by
  simp only [EdgeGraph.Inc, selectedEdgeEquiv_symm_source, selectedEdgeEquiv_symm_target]

theorem flipped_ustep_iff (P : OriginalParallelArms N) (S : N.Switching) (a b : V) :
    (flippedSwitching P S).graph.UStep (fun _ => True) a b ↔
      S.graph.UStep (fun _ => True) a b := by
  constructor
  · rintro ⟨e, _, he⟩
    exact ⟨(selectedEdgeEquiv P S).symm e, trivial,
      (selectedEdgeEquiv_symm_inc_iff P S e a b).mpr he⟩
  · rintro ⟨e, _, he⟩
    exact ⟨selectedEdgeEquiv P S e, trivial,
      (selectedEdgeEquiv_inc_iff P S e a b).mpr he⟩

theorem flipped_ureach_iff (P : OriginalParallelArms N) (S : N.Switching) (a b : V) :
    (flippedSwitching P S).graph.UReach (fun _ => True) a b ↔
      S.graph.UReach (fun _ => True) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact ih.tail ((flipped_ustep_iff P S _ _).mp hab)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact ih.tail ((flipped_ustep_iff P S _ _).mpr hab)

/-- Pointwise original-tip descendants follow; no displayed-target field is used. -/
theorem original_tip_descendants_iff (P : OriginalParallelArms N) (S : N.Switching)
    (a : V) (x : X) :
    (flippedSwitching P S).graph.DReach a (N.leaf x) ↔
      S.graph.DReach a (N.leaf x) := flipped_dreach_iff P S a (N.leaf x)

#print axioms actual_parallel_arms_nonempty
#print axioms incoming_iff_arm
#print axioms selected_arm_exactly_one
#print axioms flipped_ordinary_retained
#print axioms selectedEdgeEquiv_source
#print axioms selectedEdgeEquiv_target
#print axioms flipped_dstep_iff
#print axioms flipped_dreach_iff
#print axioms flipped_ustep_iff
#print axioms flipped_ureach_iff

end UnifiedLean.G6.ParallelArmSwitching
