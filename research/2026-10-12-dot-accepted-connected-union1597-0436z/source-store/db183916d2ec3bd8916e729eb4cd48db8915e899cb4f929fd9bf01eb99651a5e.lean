import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
Classical representation transport, checked for the G5/CG1 integration pilot.
Contributor: dot, representation integration lane, 2026-10-02.
No original biological-source theorem or missing G5 chronology is assumed.
The rational Haar map is an encoding of two exact coordinates, not a physical
lineage waveform. All coefficients are retained. Finset incidence preserves
original labels and complete joint event groups; flattening is not this map.
-/

namespace RepresentationPilot

def FiberConstant {S O T : Type*} (obs : S → O) (target : S → T) : Prop :=
  ∀ s t, obs s = obs t → target s = target t

theorem recoding_preserves_collision {O R : Type*} (E : O → R)
    {a b : O} (h : a = b) : E a = E b := congrArg E h

theorem target_constant_after_recoding_implies_before {S O R T : Type*}
    (obs : S → O) (target : S → T) (E : O → R)
    (h : FiberConstant (E ∘ obs) target) : FiberConstant obs target := by
  intro s t heq
  exact h s t (congrArg E heq)

theorem same_observation_fibers_of_decoder {S O R : Type*}
    (obs : S → O) (E : O → R) (D : R → O)
    (hDE : Function.LeftInverse D E) (s t : S) :
    E (obs s) = E (obs t) ↔ obs s = obs t := by
  constructor
  · intro h
    have hd := congrArg D h
    rw [hDE (obs s), hDE (obs t)] at hd
    exact hd
  · exact congrArg E

theorem target_fiber_constancy_iff_of_decoder {S O R T : Type*}
    (obs : S → O) (target : S → T) (E : O → R) (D : R → O)
    (hDE : Function.LeftInverse D E) :
    FiberConstant (E ∘ obs) target ↔ FiberConstant obs target := by
  constructor
  · exact target_constant_after_recoding_implies_before obs target E
  · intro h s t heq
    exact h s t ((same_observation_fibers_of_decoder obs E D hDE s t).mp heq)

/-- Label-preserving incidence of a finite block. IDs are arguments, not erased. -/
def incidence {L : Type*} [DecidableEq L] (block : Finset L) : L → Bool :=
  fun label => decide (label ∈ block)

theorem incidence_injective {L : Type*} [DecidableEq L] :
    Function.Injective (@incidence L _) := by
  intro a b h
  apply Finset.ext
  intro x
  have hx := congrFun h x
  simpa [incidence] using hx

/-- A joint event remains a set of whole labeled blocks. The outer grouping is
retained. This also applies a second time to a finite support of joint events. -/
theorem joint_incidence_injective {L : Type*} [DecidableEq L] :
    Function.Injective (@incidence (Finset L) _) := incidence_injective

def haar2 (v : ℚ × ℚ) : ℚ × ℚ :=
  ((v.1 + v.2) / 2, (v.1 - v.2) / 2)

def unhaar2 (c : ℚ × ℚ) : ℚ × ℚ := (c.1 + c.2, c.1 - c.2)

theorem full_haar_leftInverse : Function.LeftInverse unhaar2 haar2 := by
  rintro ⟨a,b⟩
  apply Prod.ext <;> dsimp [haar2, unhaar2] <;> ring

theorem full_haar_injective : Function.Injective haar2 :=
  full_haar_leftInverse.injective

def coarse2 (v : ℚ × ℚ) : ℚ := (haar2 v).1

theorem dropping_detail_collides :
    coarse2 (1,0) = coarse2 (0,1) ∧ ((1,0) : ℚ × ℚ) ≠ (0,1) := by
  constructor
  · dsimp [coarse2, haar2]
    ring
  · intro h
    have hx : (1 : ℚ) = 0 := congrArg Prod.fst h
    exact one_ne_zero hx

#print axioms recoding_preserves_collision
#print axioms target_fiber_constancy_iff_of_decoder
#print axioms incidence_injective
#print axioms joint_incidence_injective
#print axioms full_haar_leftInverse
#print axioms full_haar_injective
#print axioms dropping_detail_collides

end RepresentationPilot
