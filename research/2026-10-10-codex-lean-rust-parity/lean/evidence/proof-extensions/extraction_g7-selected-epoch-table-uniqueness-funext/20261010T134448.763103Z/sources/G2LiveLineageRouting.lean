import SourceNetwork
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

/-!
# Original-hybrid pulse: coins index live ancestors, not original copies

New assumption stress test: dot's dedicated Lean lane, 2026-10-01.
The pulse names one actual original hybrid and its two original incoming edge
IDs. A current ancestral forest token can contain several original copies.
Independent inheritance supplies one coin to that LIVE token. This primitive
cannot split copies whose ancestors have already coalesced.

This does not construct the whole coalescent source process or prove all-copy
projectivity. The compiler must still establish that its current forest state
has the claimed ancestor map and that original IDs/parameters/registers are
held fixed. The exact finite wrong-pulse control below checks that requirement.
-/

namespace GProgram.G2

open Nanuq.Source

variable {V E X Copy L : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- One named actual original hybrid with the two legal original parent edges. -/
structure OriginalHybridParents (N : RootedBinary V E X) where
  hybrid : V
  isHybrid : N.graph.IsHybrid hybrid
  parent0 : E
  parent1 : E
  target0 : N.graph.target parent0 = hybrid
  target1 : N.graph.target parent1 = hybrid
  different : parent0 ≠ parent1

def OriginalHybridParents.parent {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (bit : Bool) : E :=
  if bit then H.parent1 else H.parent0

theorem OriginalHybridParents.parent_injective {N : RootedBinary V E X}
    (H : OriginalHybridParents N) : Function.Injective H.parent := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · exact False.elim (H.different (by simpa [parent] using hab))
  · exact False.elim (H.different (by simpa [parent] using hab.symm))
  · rfl

/-- Current original-copy membership in each live ancestral forest token. -/
structure LiveAncestry (Copy L : Type*) where
  ancestor : Copy → L
  surjective : Function.Surjective ancestor

def routedParent {N : RootedBinary V E X} (H : OriginalHybridParents N)
    (state : LiveAncestry Copy L) (coin : L → Bool) (copy : Copy) : E :=
  H.parent (coin (state.ancestor copy))

/-- A source-mode independent pulse preserves an already merged ancestral
forest token. This holds for every coin realization, not only on average. -/
theorem coalesced_copies_cannot_split {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (state : LiveAncestry Copy L) (coin : L → Bool)
    {x y : Copy} (hxy : state.ancestor x = state.ancestor y) :
    routedParent H state coin x = routedParent H state coin y := by
  simp only [routedParent, hxy]

/-- The pulse exposes exactly the live-ancestor coin. Original parent labels
cannot be silently merged or reinterpreted as a compressed actuator ID. -/
theorem routed_parent_eq_iff_live_coin_eq {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (state : LiveAncestry Copy L) (coin : L → Bool)
    (x y : Copy) :
    routedParent H state coin x = routedParent H state coin y ↔
      coin (state.ancestor x) = coin (state.ancestor y) := by
  exact H.parent_injective.eq_iff

def mergedPair : LiveAncestry Bool Unit :=
  ⟨fun _ => (), by intro u; cases u; exact ⟨false, rfl⟩⟩

/-- A per-original-copy assignment can fail to factor through the actual
single live ancestor after the pair's merger. -/
theorem opposite_copy_bits_are_not_a_live_pulse :
    ¬ ∃ coin : Unit → Bool, ∀ copy : Bool, coin (mergedPair.ancestor copy) = copy := by
  rintro ⟨coin, hcoin⟩
  have hf := hcoin false
  have ht := hcoin true
  have h : (false : Bool) = true := hf.symm.trans ht
  cases h

def bitWeight (p : ℚ) (bit : Bool) : ℚ := if bit then 1 - p else p

/-- Incorrect pulse: one independent coin for each original copy, even though
they currently share one live ancestral forest token. -/
def perCopyPulse (p : ℚ) (a b : Bool) : ℚ := bitWeight p a * bitWeight p b

/-- Correct single-live-ancestor pulse, lifted back to its original copy labels. -/
def oneLivePulse (p : ℚ) (a b : Bool) : ℚ :=
  if a = b then bitWeight p a else 0

theorem perCopyPulse_normalized (p : ℚ) :
    perCopyPulse p false false + perCopyPulse p false true +
    perCopyPulse p true false + perCopyPulse p true true = 1 := by
  simp [perCopyPulse, bitWeight]
  ring

theorem oneLivePulse_normalized (p : ℚ) :
    oneLivePulse p false false + oneLivePulse p false true +
    oneLivePulse p true false + oneLivePulse p true true = 1 := by
  simp [oneLivePulse, bitWeight]

theorem wrong_pulse_split_mass (p : ℚ) :
    perCopyPulse p false true + perCopyPulse p true false = 2 * p * (1 - p) ∧
    oneLivePulse p false true + oneLivePulse p true false = 0 := by
  constructor
  · simp [perCopyPulse, bitWeight]
    ring
  · simp [oneLivePulse]

theorem fair_copy_pulse_splits_merged_ancestor :
    perCopyPulse (1 / 2) false true + perCopyPulse (1 / 2) true false = 1 / 2 ∧
    oneLivePulse (1 / 2) false true + oneLivePulse (1 / 2) true false = 0 := by
  exact ⟨by norm_num [perCopyPulse, bitWeight], by simp [oneLivePulse]⟩

#print axioms coalesced_copies_cannot_split
#print axioms routed_parent_eq_iff_live_coin_eq
#print axioms opposite_copy_bits_are_not_a_live_pulse
#print axioms wrong_pulse_split_mass
#print axioms fair_copy_pulse_splits_merged_ancestor

end GProgram.G2
