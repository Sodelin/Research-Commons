import G1OriginalDecoratedSpan
import ActualSerialNoLossComposition
import ActualPopulationRate

/-!
UNCOMPILED source-level candidate, 21 October 2026.

This instantiates the existing actual_no_loss_append row obligation for a
literal ORIGINAL span, including its ordinary populations and original bigon
exits. Entrance is derived from actual_original_span_exit_population; the
entering current count is derived by an explicit finite equivalence. COMMON
remains conditional on the entering once-stored register, whose preservation
is already proved. The final theorem is for a complete supplied OriginalSpan.

No desired arm law, desired row probability, refreshed bit, new word grammar,
new generator or arbitrary finite surrogate graph is an input. The isolated
original programs and physical rates/calendar are those of the inherited
source. To use a naturally initialized whole-calendar source, one must still
identify the literal compiled segment, bind gamma to that bank's originalGamma,
and average the unused original bits with the actual causal-history theorem.
This is a no-loss factor adapter, not the complete seven-state forest kernel,
an eligible-slot graph reconstruction, a count bound or G3 NO termination.
-/

namespace GProgram.G3.ActualOriginalSpanNoLoss

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels
open GProgram.SourceForestKingmanPopulationProjection
open GProgram.G5.ActualNoMergerReadout
open G1NonrootBigonKernel G1ExtractedComponentProgram G1OriginalDecoratedSpan
open DotG34.OriginalBigonProgramDiagonal DotG34.ActualStoredRegister
open DotG34.ActualSerialNoLossComposition DotG34.ActualSerialSurvival
open DotG34.ActualPopulationRate
open scoped Classical BigOperators NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- With all CURRENT roots at this actual node, the pulse index contains every
live representative exactly once, regardless of its carried genealogy. -/
theorem atNode_card_eq_liveCard (N : RootedBinary V E X) {sample : Copy → X}
    (v : V) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node v) :
    Fintype.card (AtNode (state s) v) = liveCard s := by
  classical
  let e : AtNode (state s) v ≃ ↥(state s).live :=
    { toFun := fun l => ⟨l.val, l.property.1⟩
      invFun := fun l => ⟨l.val, ⟨l.property, hall l.val l.property⟩⟩
      left_inv := by intro l; apply Subtype.ext; rfl
      right_inv := by intro l; apply Subtype.ext; rfl }
  change Fintype.card (AtNode (state s) v) = (state s).live.card
  calc
    _ = Fintype.card ↥(state s).live := Fintype.card_congr e
    _ = _ := by simp

noncomputable def arm0Survival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N) : ℝ :=
  Real.exp (-(pairRate r (some B.parents.parent0) * (bigonDuration N C B : ℝ)))

noncomputable def arm1Survival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N) : ℝ :=
  Real.exp (-(pairRate r (some B.parents.parent1) * (bigonDuration N C B : ℝ)))

/-- Native gamma is P(parent1), so the parent0 term has weight 1-gamma. -/
noncomputable def independentCellSurvival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (n : Nat) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (1 - (gamma : ℝ)) ^ k *
    (gamma : ℝ) ^ (n - k) * (arm0Survival N C r B) ^ (k.choose 2) *
    (arm1Survival N C r B) ^ ((n - k).choose 2)

noncomputable def storedCommonCellSurvival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (reg : V → Bool) (n : Nat) : ℝ :=
  if reg B.parents.hybrid then (arm1Survival N C r B) ^ (n.choose 2)
  else (arm0Survival N C r B) ^ (n.choose 2)

private lemma mass_eq_ofReal {A : Type*} (mu : PMF A) (a : A) (x : ℝ)
    (hx : (mu a).toReal = x) : mu a = ENNReal.ofReal x := by
  rw [← hx, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

private lemma originalPlace_injective (N : RootedBinary V E X) :
    Function.Injective (originalPlace N) := by
  intro i j h
  cases i <;> cases j <;> simp_all [originalPlace]

/-- All original current-pair rates are counted; other populations are empty.
The root case is included by Option E, with the same original root rate. -/
theorem actual_colocated_total_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (i : Option E)
    (hall : ∀ l ∈ (state s).live, (state s).location l = originalPlace N i) :
    totalRate N r s = pairRate r i * ((liveCard s).choose 2 : ℝ) := by
  have hself : populationRoots (state s) (originalPlace N i) = (state s).live := by
    apply Finset.filter_eq_self.mpr
    exact hall
  have hother (j : Option E) (hj : j ≠ i) :
      populationRoots (state s) (originalPlace N j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    obtain ⟨hlive, hplace⟩ := Finset.mem_filter.mp hl
    exact hj ((originalPlace_injective N ((hall l hlive).symm.trans hplace)).symm)
  rw [actual_rate_choose_two, Finset.sum_eq_single i]
  · rw [hself]
    rfl
  · intro j _ hj
    rw [hother j hj]
    simp
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

noncomputable def ordinaryCellSurvival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (e : E) (n : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(pairRate r (some e) * (n.choose 2 : ℝ) *
    (edgeDuration N C e : ℝ))))

/-- Literal original ordinary entry, positive calendar interval and actual exit.
The count-rate identity is derived above, rather than supplied as an arm law. -/
theorem actual_original_edge_no_loss (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (e : E)
    (degree : N.graph.inDegree (N.graph.target e) = 1) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live,
      (state s).location l = .node (N.graph.target e)) :
    ((sourceProgram N r (edgeProgram N C e degree) s).map liveCard) (liveCard s) =
      ordinaryCellSurvival N C r e (liveCard s) := by
  have hentered : ∀ l ∈ (state (ordinaryCode N s e)).live,
      (state (ordinaryCode N s e)).location l = originalPlace N (some e) := by
    intro l hl
    have hsrc : copyLocation (state s) l = .node (N.graph.target e) :=
      hall _ (s.property.forest.ancestor_live l)
    have hp : copyLocation (state (ordinaryCode N s e)) l = .edge e := by
      rw [actual_ordinary_copy_population, hsrc, if_pos rfl]
    have hrep : (state (ordinaryCode N s e)).ancestor l = l :=
      (ordinaryCode N s e).property.forest.representative l hl
    simpa only [copyLocation, hrep, originalPlace] using hp
  rw [actual_original_edge_program, PMF.map_comp]
  change ((sourceTimeKernel N r (edgeDuration N C e) (ordinaryCode N s e)).map
    liveCard) (liveCard (ordinaryCode N s e)) = _
  rw [actual_kernel_live_card_mass, actual_holding_weight,
    actual_colocated_total_rate N r (ordinaryCode N s e) (some e) hentered]
  rfl

/-- The native binomial row is constant on the ACTUAL no-loss prefix support.
The conclusion includes both original exits of the next bigon. -/
theorem actual_independent_after_original_span
    (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool)
    (B : NonrootBigon N) {a : V} (pre : OriginalSpan N a B.parents.hybrid)
    (s : Code N sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node a) :
    ((sourceProgram N r
      (spanProgram N C gamma common pre ++
        bigonProgram N C B (gamma B.parents.hybrid) false) s).map liveCard)
        (liveCard s) =
      ((sourceProgram N r (spanProgram N C gamma common pre) s).map liveCard)
        (liveCard s) *
      ENNReal.ofReal (independentCellSurvival N C r B
        (gamma B.parents.hybrid) (liveCard s)) := by
  apply actual_no_loss_append N r (spanProgram N C gamma common pre)
    (bigonProgram N C B (gamma B.parents.hybrid) false) s
  intro d hd hcount
  have hall := actual_original_span_exit_population N C r gamma common pre s hs hd
  have hcard := atNode_card_eq_liveCard N B.parents.hybrid d hall
  have hdiag := actual_original_bigon_independent N C r B
    (gamma B.parents.hybrid) d hall
  dsimp only at hdiag
  have hreal :
      (((sourceProgram N r (bigonProgram N C B (gamma B.parents.hybrid) false) d).map
        liveCard) (liveCard d)).toReal =
      independentCellSurvival N C r B (gamma B.parents.hybrid) (liveCard s) := by
    simpa only [hcard, hcount, independentCellSurvival, arm0Survival, arm1Survival]
      using hdiag
  exact mass_eq_ofReal _ _ _ hreal

/-- The native COMMON row is constant conditional on the ONE entering bank.
This holds even for a mixed-mode prefix. It does not average or redraw a bit. -/
theorem actual_stored_common_after_original_span
    (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool)
    (B : NonrootBigon N) {a : V} (pre : OriginalSpan N a B.parents.hybrid)
    (s : Code N sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node a) :
    ((sourceProgram N r
      (spanProgram N C gamma common pre ++
        bigonProgram N C B (gamma B.parents.hybrid) true) s).map liveCard)
        (liveCard s) =
      ((sourceProgram N r (spanProgram N C gamma common pre) s).map liveCard)
        (liveCard s) *
      ENNReal.ofReal (storedCommonCellSurvival N C r B
        (state s).register (liveCard s)) := by
  apply actual_no_loss_append N r (spanProgram N C gamma common pre)
    (bigonProgram N C B (gamma B.parents.hybrid) true) s
  intro d hd hcount
  have hall := actual_original_span_exit_population N C r gamma common pre s hs hd
  have hcard := atNode_card_eq_liveCard N B.parents.hybrid d hall
  have hreg := actual_program_register_support N r (spanProgram N C gamma common pre)
    s d hd
  have hdiag := actual_original_bigon_common N C r B
    (gamma B.parents.hybrid) d hall
  dsimp only at hdiag
  have hreal :
      (((sourceProgram N r (bigonProgram N C B (gamma B.parents.hybrid) true) d).map
        liveCard) (liveCard d)).toReal =
      storedCommonCellSurvival N C r B (state s).register (liveCard s) := by
    simpa only [hcard, hcount, hreg, storedCommonCellSurvival,
      arm0Survival, arm1Survival] using hdiag
  exact mass_eq_ofReal _ _ _ hreal

/-- Scalar evaluation of the EXISTING original-source word, on its same
calendar/rates/site controls and entering register. This is not another
source/path grammar. A repeated COMMON site would reuse the same reg value. -/
noncomputable def spanNoLossFactor (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool) (reg : V → Bool) (n : Nat)
    {a b : V} : OriginalSpan N a b → ℝ≥0∞
  | .edge e _ => ordinaryCellSurvival N C r e n
  | .bigon B =>
      if common B.parents.hybrid then
        ENNReal.ofReal (storedCommonCellSurvival N C r B reg n)
      else ENNReal.ofReal (independentCellSurvival N C r B (gamma B.parents.hybrid) n)
  | .append first last =>
      spanNoLossFactor N C r gamma common reg n first *
        spanNoLossFactor N C r gamma common reg n last

/-- Whole supplied ORIGINAL span: exact native count-survival factor, all
current counts, arbitrary carried entering trees and fixed original register.
No row-constant or desired continuation probability premise remains.
Natural unused-bit averaging and full forest-kernel identification are separate. -/
theorem actual_original_span_no_loss (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : OriginalSpan N a b) (s : Code N sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node a) :
    ((sourceProgram N r (spanProgram N C gamma common word) s).map liveCard)
      (liveCard s) =
      spanNoLossFactor N C r gamma common (state s).register (liveCard s) word := by
  induction word generalizing s with
  | edge e degree =>
      exact actual_original_edge_no_loss N C r e degree s hs
  | bigon B =>
      have hcard := atNode_card_eq_liveCard N B.parents.hybrid s hs
      cases hmode : common B.parents.hybrid
      · have hdiag := actual_original_bigon_independent N C r B
          (gamma B.parents.hybrid) s hs
        dsimp only at hdiag
        rw [hcard] at hdiag
        have h := mass_eq_ofReal _ _ _ hdiag
        simpa [spanProgram, spanNoLossFactor, hmode,
          independentCellSurvival, arm0Survival, arm1Survival] using h
      · have hdiag := actual_original_bigon_common N C r B
          (gamma B.parents.hybrid) s hs
        dsimp only at hdiag
        rw [hcard] at hdiag
        have h := mass_eq_ofReal _ _ _ hdiag
        simpa [spanProgram, spanNoLossFactor, hmode,
          storedCommonCellSurvival, arm0Survival, arm1Survival] using h
  | append first last ihfirst ihlast =>
      change ((sourceProgram N r
        (spanProgram N C gamma common first ++ spanProgram N C gamma common last) s).map
          liveCard) (liveCard s) =
        spanNoLossFactor N C r gamma common (state s).register (liveCard s) first *
          spanNoLossFactor N C r gamma common (state s).register (liveCard s) last
      have hrow : ∀ d ∈ (sourceProgram N r (spanProgram N C gamma common first) s).support,
          liveCard d = liveCard s →
          ((sourceProgram N r (spanProgram N C gamma common last) d).map liveCard)
            (liveCard d) =
          spanNoLossFactor N C r gamma common (state s).register (liveCard s) last := by
        intro d hd hcount
        have hexit := actual_original_span_exit_population N C r gamma common first s hs hd
        have hreg := actual_program_register_support N r (spanProgram N C gamma common first)
          s d hd
        simpa only [hcount, hreg] using ihlast d hexit
      rw [actual_no_loss_append N r (spanProgram N C gamma common first)
        (spanProgram N C gamma common last) s _ hrow, ihfirst s hs]

#print axioms atNode_card_eq_liveCard
#print axioms actual_colocated_total_rate
#print axioms actual_original_edge_no_loss
#print axioms actual_independent_after_original_span
#print axioms actual_stored_common_after_original_span
#print axioms actual_original_span_no_loss

end GProgram.G3.ActualOriginalSpanNoLoss
