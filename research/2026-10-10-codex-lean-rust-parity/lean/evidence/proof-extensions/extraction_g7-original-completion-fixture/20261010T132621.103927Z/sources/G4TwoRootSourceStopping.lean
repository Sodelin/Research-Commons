import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
G4 two-current-root private source compiler and observable size certificate.

The Boolean route table is explicit. A previously merged pair is one absorbing
root, so it does not receive two fresh coins at a later cell. The observation is
the A-only cherry in the rooted three-leaf restriction, after fixed positive
ordinary padding, with an ordinary three-root first pair chosen uniformly.

This proves the exact finite two-root algebra and conditional rival-wide length
certificate. It does not formalize a full source-graph admission checker, general
Kingman projectivity/pruning, the all-copy normal form, or the bounded-length
full-forest QE algorithm. Those are separate package obligations.
-/

namespace G4TwoRootSourceStopping

structure PositiveEdge where
  survival : ℝ
  positive : 0 < survival
  below_one : survival < 1

structure PositiveBigon where
  x : ℝ
  y : ℝ
  g : ℝ
  x_positive : 0 < x
  x_below_one : x < 1
  y_positive : 0 < y
  y_below_one : y < 1
  g_positive : 0 < g
  g_below_one : g < 1

def coinWeight (g : ℝ) (choice : Bool) : ℝ :=
  if choice then g else 1 - g

def pairRouteSurvival (x y : ℝ) (a b : Bool) : ℝ :=
  if a then (if b then x else 1) else (if b then 1 else y)

def bareSurvival (B : PositiveBigon) : ℝ :=
  ∑ a : Bool, ∑ b : Bool,
    coinWeight B.g a * coinWeight B.g b * pairRouteSurvival B.x B.y a b

theorem bareSurvival_eq (B : PositiveBigon) :
    bareSurvival B = B.g ^ 2 * B.x + (1 - B.g) ^ 2 * B.y +
      2 * B.g * (1 - B.g) := by
  simp [bareSurvival, coinWeight, pairRouteSurvival]
  <;> ring

theorem routing_normalized (g : ℝ) :
    (∑ a : Bool, ∑ b : Bool, coinWeight g a * coinWeight g b) = 1 := by
  simp [coinWeight]
  <;> ring

theorem bareSurvival_defect (B : PositiveBigon) :
    bareSurvival B = 1 - B.g ^ 2 * (1 - B.x) -
      (1 - B.g) ^ 2 * (1 - B.y) := by
  rw [bareSurvival_eq]
  ring

theorem bareSurvival_positive (B : PositiveBigon) : 0 < bareSurvival B := by
  rw [bareSurvival_eq]
  have hx := B.x_positive
  have hy := B.y_positive
  have hg := B.g_positive
  have hh : 0 < 1 - B.g := sub_pos.mpr B.g_below_one
  positivity

theorem bareSurvival_below_one (B : PositiveBigon) : bareSurvival B < 1 := by
  rw [bareSurvival_defect]
  have hleft : 0 < B.g ^ 2 * (1 - B.x) :=
    mul_pos (sq_pos_of_pos B.g_positive) (sub_pos.mpr B.x_below_one)
  have hright : 0 ≤ (1 - B.g) ^ 2 * (1 - B.y) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (sub_pos.mpr B.y_below_one))
  linarith

structure Cell where
  bigon : PositiveBigon
  connector : PositiveEdge

def cellSurvival (C : Cell) : ℝ :=
  bareSurvival C.bigon * C.connector.survival

theorem cellSurvival_positive (C : Cell) : 0 < cellSurvival C :=
  mul_pos (bareSurvival_positive C.bigon) C.connector.positive

theorem cellSurvival_le_bare (C : Cell) : cellSurvival C ≤ bareSurvival C.bigon := by
  dsimp [cellSurvival]
  have hp := bareSurvival_positive C.bigon
  have hq := C.connector.below_one
  nlinarith

theorem cellSurvival_below_one (C : Cell) : cellSurvival C < 1 :=
  lt_of_le_of_lt (cellSurvival_le_bare C) (bareSurvival_below_one C.bigon)

-- The merged state is absorbing. Only the unmerged state is routed twice.
def serialMerged (p q : ℝ) : ℝ := (1 - p) * 1 + p * (1 - q)
def serialUnmerged (p q : ℝ) : ℝ := p * q

theorem serial_pair_kernel (p q : ℝ) :
    serialMerged p q = 1 - serialUnmerged p q := by
  dsimp [serialMerged, serialUnmerged]
  ring

def tailSurvival : List Cell → ℝ
  | [] => 1
  | C :: rest => serialUnmerged (cellSurvival C) (tailSurvival rest)

structure PositiveChain where
  leading : PositiveEdge
  cells : List Cell

def sourceSurvival (K : PositiveChain) : ℝ :=
  serialUnmerged K.leading.survival (tailSurvival K.cells)

theorem tailSurvival_positive (cells : List Cell) : 0 < tailSurvival cells := by
  induction cells with
  | nil => simp [tailSurvival]
  | cons C rest ih =>
      exact mul_pos (cellSurvival_positive C) ih

theorem tailSurvival_le_one (cells : List Cell) : tailSurvival cells ≤ 1 := by
  induction cells with
  | nil => simp [tailSurvival]
  | cons C rest ih =>
      change cellSurvival C * tailSurvival rest ≤ 1
      have hc := cellSurvival_below_one C
      have hcp := cellSurvival_positive C
      have htp := tailSurvival_positive rest
      nlinarith

theorem sourceSurvival_positive (K : PositiveChain) : 0 < sourceSurvival K :=
  mul_pos K.leading.positive (tailSurvival_positive K.cells)

theorem sourceSurvival_below_one (K : PositiveChain) : sourceSurvival K < 1 := by
  change K.leading.survival * tailSurvival K.cells < 1
  have hp := K.leading.positive
  have ht := tailSurvival_positive K.cells
  have hlt := K.leading.below_one
  have hle := tailSurvival_le_one K.cells
  nlinarith

theorem tailSurvival_le_power (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ cells : List Cell, (∀ C ∈ cells, cellSurvival C ≤ ρ) →
      tailSurvival cells ≤ ρ ^ cells.length := by
  intro cells
  induction cells with
  | nil => intro _; simp [tailSurvival]
  | cons C rest ih =>
      intro hcells
      have hc : cellSurvival C ≤ ρ := hcells C (by simp)
      have hrest : tailSurvival rest ≤ ρ ^ rest.length :=
        ih (fun D hD => hcells D (by simp [hD]))
      have hm : cellSurvival C * tailSurvival rest ≤ ρ * ρ ^ rest.length :=
        mul_le_mul hc hrest (le_of_lt (tailSurvival_positive rest)) hρ
      simpa [tailSurvival, serialUnmerged, pow_succ, mul_comm] using hm

def UniformContractionClass (ρ : ℝ) (K : PositiveChain) : Prop :=
  ∀ C ∈ K.cells, bareSurvival C.bigon ≤ ρ

theorem sourceSurvival_le_power (ρ : ℝ) (hρ : 0 ≤ ρ)
    (K : PositiveChain) (hK : UniformContractionClass ρ K) :
    sourceSurvival K ≤ ρ ^ K.cells.length := by
  have hc : ∀ C ∈ K.cells, cellSurvival C ≤ ρ :=
    fun C hC => le_trans (cellSurvival_le_bare C) (hK C hC)
  have ht := tailSurvival_le_power ρ hρ K.cells hc
  have hp := tailSurvival_positive K.cells
  have hlead := K.leading.below_one
  change K.leading.survival * tailSurvival K.cells ≤ ρ ^ K.cells.length
  have hpad : K.leading.survival * tailSurvival K.cells ≤ tailSurvival K.cells := by
    nlinarith
  exact le_trans hpad ht

-- A-only merger before joining B forces the rooted A-cherry. With three
-- unmerged roots, exactly one of the three equally likely first pairs does so.
noncomputable def rootedACladeResponse (before after : PositiveEdge) (p : ℝ) : ℝ :=
  let r := before.survival * after.survival * p
  (1 - r) * 1 + r * (1 / 3)

theorem rootedACladeResponse_eq (before after : PositiveEdge) (p : ℝ) :
    rootedACladeResponse before after p =
      1 - (2 / 3) * before.survival * after.survival * p := by
  dsimp [rootedACladeResponse]
  ring

theorem rootedACladeResponse_injective (before after : PositiveEdge) :
    Function.Injective (rootedACladeResponse before after) := by
  intro p q h
  rw [rootedACladeResponse_eq, rootedACladeResponse_eq] at h
  have hmul : before.survival * after.survival * p =
      before.survival * after.survival * q := by linarith
  exact mul_left_cancel₀ (ne_of_gt (mul_pos before.positive after.positive)) hmul

theorem rootedACladeResponse_is_probability
    (before after : PositiveEdge) (K : PositiveChain) :
    (1 / 3 : ℝ) < rootedACladeResponse before after (sourceSurvival K) ∧
      rootedACladeResponse before after (sourceSurvival K) < 1 := by
  have hcoef : 0 < before.survival * after.survival :=
    mul_pos before.positive after.positive
  have hcoef1 : before.survival * after.survival < 1 := by
    calc
      before.survival * after.survival < before.survival * 1 :=
        mul_lt_mul_of_pos_left after.below_one before.positive
      _ = before.survival := mul_one _
      _ < 1 := before.below_one
  have hr : 0 < before.survival * after.survival * sourceSurvival K :=
    mul_pos hcoef (sourceSurvival_positive K)
  have hr1 : before.survival * after.survival * sourceSurvival K < 1 := by
    calc
      before.survival * after.survival * sourceSurvival K <
          (before.survival * after.survival) * 1 :=
        mul_lt_mul_of_pos_left (sourceSurvival_below_one K) hcoef
      _ = before.survival * after.survival := mul_one _
      _ < 1 := hcoef1
  rw [rootedACladeResponse_eq]
  constructor <;> nlinarith

-- This premise is explicitly about every rival. No target-only margin is used.
def RivalEnvelope (C : PositiveChain → Prop) (U : ℕ → ℝ) : Prop :=
  ∀ K : PositiveChain, C K → sourceSurvival K ≤ U K.cells.length

theorem uniform_contraction_envelope (ρ : ℝ) (hρ : 0 ≤ ρ) :
    RivalEnvelope (UniformContractionClass ρ) (fun n => ρ ^ n) := by
  intro K hK
  exact sourceSurvival_le_power ρ hρ K hK

theorem certified_crossing_length_bound
    (C : PositiveChain → Prop) (U : ℕ → ℝ)
    (hU : Antitone U) (henv : RivalEnvelope C U)
    (target rival : PositiveChain) (before after : PositiveEdge)
    (hrival : C rival)
    (hobs : rootedACladeResponse before after (sourceSurvival rival) =
      rootedACladeResponse before after (sourceSurvival target))
    (b : ℕ) (hcross : U b < sourceSurvival target) :
    rival.cells.length < b := by
  have heq : sourceSurvival rival = sourceSurvival target :=
    rootedACladeResponse_injective before after hobs
  by_contra hnot
  have hb : b ≤ rival.cells.length := Nat.le_of_not_gt hnot
  have hupper : sourceSurvival rival ≤ U b := le_trans (henv rival hrival) (hU hb)
  rw [heq] at hupper
  exact (not_lt_of_ge hupper) hcross

-- A zero-limit condition without relying on an exact computable-real equality
-- test. A certified interval/dovetailed search can expose one strict crossing.
def ArbitrarilySmall (U : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ b : ℕ, U b < ε

theorem positive_target_has_crossing
    (U : ℕ → ℝ) (hU : Antitone U) (hsmall : ArbitrarilySmall U)
    (target : PositiveChain) :
    ∃ b : ℕ, 0 < b ∧ U b < sourceSurvival target := by
  obtain ⟨b, hb⟩ := hsmall (sourceSurvival target) (sourceSurvival_positive target)
  refine ⟨b + 1, Nat.succ_pos b, ?_⟩
  exact lt_of_le_of_lt (hU (Nat.le_succ b)) hb

theorem observable_finite_length_certificate
    (C : PositiveChain → Prop) (U : ℕ → ℝ)
    (hU : Antitone U) (henv : RivalEnvelope C U)
    (hsmall : ArbitrarilySmall U) (target : PositiveChain)
    (before after : PositiveEdge) :
    ∃ b : ℕ, 0 < b ∧ ∀ rival : PositiveChain,
      C rival →
      rootedACladeResponse before after (sourceSurvival rival) =
        rootedACladeResponse before after (sourceSurvival target) →
      rival.cells.length < b := by
  obtain ⟨b, hpositive, hcross⟩ := positive_target_has_crossing U hU hsmall target
  exact ⟨b, hpositive, fun rival hrival hobs =>
    certified_crossing_length_bound C U hU henv target rival before after hrival hobs b hcross⟩

end G4TwoRootSourceStopping

#print axioms G4TwoRootSourceStopping.bareSurvival_eq
#print axioms G4TwoRootSourceStopping.rootedACladeResponse_injective
#print axioms G4TwoRootSourceStopping.observable_finite_length_certificate
