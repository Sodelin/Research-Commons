import NaturalCellAffineCompiler

/-! Actual finite event signatures and source exposure generation. Work in progress;
no full G6 law/image claim. Original vertices and rational observation cuts are
kept in one event registry. Inconsistent signatures are rejected by the existing
proved affine decision procedure, rather than accepted through an order oracle. -/
namespace UnifiedLean.G6.GeneratedNaturalChronology
open NaturalCellInverseRates NaturalCellAffineCompiler
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture

inductive Sign | lt | eq | gt deriving DecidableEq
instance : Fintype Sign := ⟨{.lt,.eq,.gt}, by intro s; cases s <;> simp⟩
abbrev Event (V : Type*) (j : ℕ) := V ⊕ Fin j
abbrev Signature (V : Type*) (j : ℕ) := Event V j × Event V j → Sign

def atom {V : Type*} {j : ℕ} (cuts : Fin j → ℚ) : Event V j → AgeAtom V
  | .inl v => .node v
  | .inr i => .fixed (cuts i)
def value {V : Type*} {j : ℕ} (cuts : Fin j → ℚ) (a : V → ℝ)
    (i : Event V j) : ℝ := (atom cuts i).eval a

def Sign.holds : Sign → ℝ → ℝ → Prop
  | .lt, x, y => x < y
  | .eq, x, y => x = y
  | .gt, x, y => y < x

def Realizes {V : Type*} {j : ℕ} (cuts : Fin j → ℚ) (s : Signature V j)
    (a : V → ℝ) : Prop := ∀ i k, (s (i,k)).holds (value cuts a i) (value cuts a k)

noncomputable def signatureOf {V : Type*} {j : ℕ} (cuts : Fin j → ℚ)
    (a : V → ℝ) : Signature V j := by
  classical
  exact fun (i,k) => if value cuts a i < value cuts a k then .lt
    else if value cuts a i = value cuts a k then .eq else .gt

theorem realizes_signatureOf {V : Type*} {j : ℕ} (cuts : Fin j → ℚ) (a : V → ℝ) :
    Realizes cuts (signatureOf cuts a) a := by
  classical
  intro i k
  simp only [signatureOf]
  split_ifs with h h <;> simp_all [Sign.holds]
  exact lt_of_le_of_ne ‹value cuts a k ≤ value cuts a i› (Ne.symm h)

def constraint {V : Type*} {j : ℕ} (cuts : Fin j → ℚ) (s : Signature V j)
    (p : Event V j × Event V j) : AgeConstraint V :=
  match s p with
  | .lt => ⟨atom cuts p.1, atom cuts p.2, .strict⟩
  | .eq => ⟨atom cuts p.1, atom cuts p.2, .equal⟩
  | .gt => ⟨atom cuts p.2, atom cuts p.1, .strict⟩

theorem constraint_iff {V : Type*} {j : ℕ} (cuts : Fin j → ℚ)
    (s : Signature V j) (a : V → ℝ) :
    (∀ p, (constraint cuts s p).holds a) ↔ Realizes cuts s a := by
  constructor
  · intro h i k
    have hp := h (i,k)
    cases hs : s (i,k) <;> simpa [constraint, hs, AgeConstraint.holds,
      AgeComparison.holds, Sign.holds, value] using hp
  · intro h p
    have hp := h p.1 p.2
    cases hs : s p <;> simpa [constraint, hs, AgeConstraint.holds,
      AgeComparison.holds, Sign.holds, value] using hp

def Before {V : Type*} {j : ℕ} (s : Signature V j) (i k : Event V j) : Prop :=
  s (i,k) = .lt
def AtMost {V : Type*} {j : ℕ} (s : Signature V j) (i k : Event V j) : Prop :=
  s (i,k) ≠ .gt

theorem before_iff {V : Type*} {j : ℕ} {cuts : Fin j → ℚ} {s : Signature V j}
    {a : V → ℝ} (h : Realizes cuts s a) (i k : Event V j) :
    Before s i k ↔ value cuts a i < value cuts a k := by
  have hp := h i k
  cases hs : s (i,k) <;> simp_all [Before, Sign.holds] <;> linarith

theorem atMost_iff {V : Type*} {j : ℕ} {cuts : Fin j → ℚ} {s : Signature V j}
    {a : V → ℝ} (h : Realizes cuts s a) (i k : Event V j) :
    AtMost s i k ↔ value cuts a i ≤ value cuts a k := by
  have hp := h i k
  cases hs : s (i,k) <;> simp_all [AtMost, Sign.holds] <;> linarith

def Adjacent {V : Type*} {j : ℕ} (s : Signature V j) (i k : Event V j) : Prop :=
  Before s i k ∧ ∀ z, ¬ (Before s i z ∧ Before s z k)
def PhysicalAdjacent {V : Type*} {j : ℕ} (cuts : Fin j → ℚ) (a : V → ℝ)
    (i k : Event V j) : Prop :=
  value cuts a i < value cuts a k ∧
    ∀ z, ¬ (value cuts a i < value cuts a z ∧ value cuts a z < value cuts a k)

theorem adjacent_iff {V : Type*} {j : ℕ} {cuts : Fin j → ℚ} {s : Signature V j}
    {a : V → ℝ} (h : Realizes cuts s a) (i k : Event V j) :
    Adjacent s i k ↔ PhysicalAdjacent cuts a i k := by
  simp only [Adjacent, PhysicalAdjacent, before_iff h]

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X) {j : ℕ}
abbrev ExposureIndex (V E : Type*) (j : ℕ) := Option E × Event V j × Event V j

def Active (s : Signature V j) (p : ExposureIndex V E j) : Prop :=
  Adjacent s p.2.1 p.2.2 ∧ match p.1 with
  | none => AtMost s (.inl N.root) p.2.1
  | some e => AtMost s (.inl (N.graph.target e)) p.2.1 ∧
      AtMost s p.2.2 (.inl (N.graph.source e))

def PhysicalActive (cuts : Fin j → ℚ) (a : V → ℝ)
    (p : ExposureIndex V E j) : Prop :=
  PhysicalAdjacent cuts a p.2.1 p.2.2 ∧ match p.1 with
  | none => a N.root ≤ value cuts a p.2.1
  | some e => a (N.graph.target e) ≤ value cuts a p.2.1 ∧
      value cuts a p.2.2 ≤ a (N.graph.source e)

theorem active_iff {cuts : Fin j → ℚ} {s : Signature V j}
    {a : V → ℝ} (h : Realizes cuts s a) (p : ExposureIndex V E j) :
    Active N s p ↔ PhysicalActive N cuts a p := by
  rcases p with ⟨pop,i,k⟩
  cases pop <;> simp only [Active, PhysicalActive, adjacent_iff h,
    atMost_iff h, value, atom, AgeAtom.eval]

def unrestricted : RationalInterval := ⟨none,none⟩
@[simp] theorem unrestricted_contains (x : ℝ) : unrestricted.contains x := by
  simp [unrestricted, RationalInterval.contains]

instance activeDecidable (s : Signature V j) (p : ExposureIndex V E j) : Decidable (Active N s p) := by
  unfold Active Adjacent Before AtMost
  cases p.1 <;> infer_instance

def exposure (cuts : Fin j → ℚ) (s : Signature V j)
    (cells : ExposureIndex V E j → RationalInterval) (p : ExposureIndex V E j) : Exposure V E :=
  ⟨p.1,atom cuts p.2.1,atom cuts p.2.2,
    if Active N s p then cells p else unrestricted⟩

theorem exposure_rows_iff {cuts : Fin j → ℚ} {s : Signature V j}
    {a : V → ℝ} (h : Realizes cuts s a)
    (r : PositivePairRates E) (cells : ExposureIndex V E j → RationalInterval) :
    (∀ p, (exposure N cuts s cells p).cell.contains
      (pairRate r (exposure N cuts s cells p).population *
        (exposure N cuts s cells p).duration a)) ↔
    (∀ p, PhysicalActive N cuts a p → (cells p).contains
      (pairRate r p.1 * (value cuts a p.2.2 - value cuts a p.2.1))) := by
  classical
  simp only [exposure, Exposure.duration, value]
  constructor
  · intro hrows p hp
    simpa [(active_iff N h p).mpr hp] using hrows p
  · intro hrows p
    split_ifs with hp
    · exact hrows p ((active_iff N h p).mp hp)
    · exact unrestricted_contains _

/-- Exact physical source meaning of a generated chart, not a desired law. -/
def PhysicalChartFeasible (cuts : Fin j → ℚ) (s : Signature V j)
    (cells : ExposureIndex V E j → RationalInterval)
    (coins : Hybrid N → RationalInterval) : Prop :=
  ∃ (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N),
    (∀ x, c.age (N.leaf x) = 0) ∧ Realizes cuts s c.age ∧
    (∀ h, (coins h).contains (g.gamma h)) ∧
    (∀ p, PhysicalActive N cuts c.age p → (cells p).contains
      (pairRate r p.1 * (value cuts c.age p.2.2 - value cuts c.age p.2.1)))

theorem generated_cell_iff (cuts : Fin j → ℚ) (s : Signature V j)
    (cells : ExposureIndex V E j → RationalInterval)
    (coins : Hybrid N → RationalInterval) :
    originalCellFeasible N (constraint cuts s) (exposure N cuts s cells) coins ↔
      PhysicalChartFeasible N cuts s cells coins := by
  constructor
  · rintro ⟨c,r,g,ht,hc,hg,hr⟩
    have hs := (constraint_iff cuts s c.age).mp hc
    exact ⟨c,r,g,ht,hs,hg,(exposure_rows_iff N hs r cells).mp hr⟩
  · rintro ⟨c,r,g,ht,hs,hg,hr⟩
    exact ⟨c,r,g,ht,(constraint_iff cuts s c.age).mpr hs,hg,
      (exposure_rows_iff N hs r cells).mpr hr⟩

/-- The finite producer feeds literal original IDs to the proved decider. -/
def decideGenerated {n : ℕ} (layout : BankVar N ≃ Fin n)
    (cuts : Fin j → ℚ) (s : Signature V j)
    (cells : ExposureIndex V E j → RationalInterval)
    (coins : Hybrid N → RationalInterval) : Bool :=
  decideOriginalCell N layout (constraint cuts s) (exposure N cuts s cells) coins

theorem decideGenerated_correct {n : ℕ} (layout : BankVar N ≃ Fin n)
    (cuts : Fin j → ℚ) (s : Signature V j)
    (cells : ExposureIndex V E j → RationalInterval)
    (coins : Hybrid N → RationalInterval) :
    decideGenerated N layout cuts s cells coins = true ↔
      PhysicalChartFeasible N cuts s cells coins := by
  exact (decideOriginalCell_correct N layout _ _ _).trans
    (generated_cell_iff N cuts s cells coins)

/-- Finite chart labels. No real parameters or independently copied source banks
are used as enumeration indices. -/
abbrev Chart (N : RootedBinary V E X) (j K L : ℕ) :=
  Signature V j × (ExposureIndex V E j → Fin K) × (Hybrid N → Fin L)

/-- Completeness of the generated finite signatures/cell labels for every ACTUAL
source. The only grid premises are one-dimensional coverage of nonnegative
hazards and interior inheritance; they do not assume source feasibility. -/
theorem source_covered {K L : ℕ} (k0 : Fin K)
    (cuts : Fin j → ℚ) (hazardGrid : Fin K → RationalInterval)
    (coinGrid : Fin L → RationalInterval)
    (hH : ∀ z : ℝ, 0 ≤ z → ∃ k, (hazardGrid k).contains z)
    (hG : ∀ z : ℝ, 0 < z → z < 1 → ∃ l, (coinGrid l).contains z)
    (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N)
    (ht : ∀ x, c.age (N.leaf x) = 0) :
    ∃ ch : Chart N j K L, Realizes cuts ch.1 c.age ∧
      (∀ h, (coinGrid (ch.2.2 h)).contains (g.gamma h)) ∧
      (∀ p, PhysicalActive N cuts c.age p → (hazardGrid (ch.2.1 p)).contains
        (pairRate r p.1 * (value cuts c.age p.2.2 - value cuts c.age p.2.1))) := by
  classical
  have he : ∀ p : ExposureIndex V E j, ∃ k : Fin K,
      PhysicalActive N cuts c.age p → (hazardGrid k).contains
        (pairRate r p.1 * (value cuts c.age p.2.2 - value cuts c.age p.2.1)) := by
    intro p
    by_cases hp : PhysicalActive N cuts c.age p
    · obtain ⟨k,hk⟩ := hH _ (mul_nonneg (le_of_lt (pairRate_pos r p.1))
        (le_of_lt (sub_pos.mpr hp.1.1)))
      exact ⟨k,fun _ => hk⟩
    · exact ⟨k0,fun h => False.elim (hp h)⟩
  choose labels hl using he
  have hg : ∀ h : Hybrid N, ∃ l, (coinGrid l).contains (g.gamma h) :=
    fun h => hG _ (g.positive h) (g.below_one h)
  choose gl hgl using hg
  exact ⟨⟨signatureOf cuts c.age,labels,gl⟩,realizes_signatureOf cuts c.age,hgl,hl⟩

/-- Exhaustive finite chart enumeration followed by exact source feasibility.
No chronology-consistency oracle and no real source enumeration occur. -/
def viableCharts {n K L : ℕ} (layout : BankVar N ≃ Fin n)
    (cuts : Fin j → ℚ) (hazardGrid : Fin K → RationalInterval)
    (coinGrid : Fin L → RationalInterval) : Finset (Chart N j K L) :=
  Finset.univ.filter fun ch => decideGenerated N layout cuts ch.1
    (fun p => hazardGrid (ch.2.1 p)) (fun h => coinGrid (ch.2.2 h)) = true

theorem viableCharts_sound {n K L : ℕ} (layout : BankVar N ≃ Fin n)
    (cuts : Fin j → ℚ) (hazardGrid : Fin K → RationalInterval)
    (coinGrid : Fin L → RationalInterval) (ch : Chart N j K L)
    (hc : ch ∈ viableCharts N layout cuts hazardGrid coinGrid) :
    PhysicalChartFeasible N cuts ch.1 (fun p => hazardGrid (ch.2.1 p))
      (fun h => coinGrid (ch.2.2 h)) := by
  apply (decideGenerated_correct N layout _ _ _ _).mp
  exact (Finset.mem_filter.mp hc).2

theorem viableCharts_cover_source {n K L : ℕ} (layout : BankVar N ≃ Fin n)
    (k0 : Fin K) (cuts : Fin j → ℚ) (hazardGrid : Fin K → RationalInterval)
    (coinGrid : Fin L → RationalInterval)
    (hH : ∀ z : ℝ, 0 ≤ z → ∃ k, (hazardGrid k).contains z)
    (hG : ∀ z : ℝ, 0 < z → z < 1 → ∃ l, (coinGrid l).contains z)
    (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N)
    (ht : ∀ x, c.age (N.leaf x) = 0) :
    ∃ ch ∈ viableCharts N layout cuts hazardGrid coinGrid,
      Realizes cuts ch.1 c.age ∧
      (∀ h, (coinGrid (ch.2.2 h)).contains (g.gamma h)) ∧
      (∀ p, PhysicalActive N cuts c.age p → (hazardGrid (ch.2.1 p)).contains
        (pairRate r p.1 * (value cuts c.age p.2.2 - value cuts c.age p.2.1))) := by
  obtain ⟨ch,hs,hg,hp⟩ := source_covered N k0 cuts hazardGrid coinGrid hH hG c r g ht
  refine ⟨ch,?_,hs,hg,hp⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  apply (decideGenerated_correct N layout _ _ _ _).mpr
  exact ⟨c,r,g,ht,hs,hg,hp⟩

end UnifiedLean.G6.GeneratedNaturalChronology
