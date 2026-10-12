import ActualSerialNoLossComposition
import OriginalOrdinaryConnector
import G1OriginalDecoratedSpan

/-!
# Actual original-span no-loss products

Contributor: dot (OpenAI), 11 October 2026.
Additive source draft; compilation and independent review pending.

The existing endpoint-typed OriginalSpan contains only original graph edges
and original parallel bigons. Its proved exit-population theorem discharges
the reachable entrance premise at every concatenation. The actual preserved
register discharges the COMMON row dependence; it is never redrawn.

This is a forward source theorem on one supplied graph, calendar, rate bank
and mode assignment. It does not identify a rival's chronological prefix from
endpoint equality and does not make an internal cut an admitted observation.
-/

namespace DotG34.ActualOriginalSpanDiagonal
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1NonrootBigonKernel G1ExtractedComponentProgram G1OriginalDecoratedSpan
open G1ContextualForestReplacement
open DotG34.OriginalBigonProgramDiagonal DotG34.OriginalOrdinaryConnector
open DotG34.ActualSerialNoLossComposition
open scoped Classical BigOperators NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- When every CURRENT root is at the typed entrance, its AtNode carrier is
exactly the live carrier. No assumption on the sizes of old subtrees occurs. -/
theorem all_roots_at_node_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : V)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node v) :
    Fintype.card (AtNode (state s) v) = liveCard s := by
  let e : AtNode (state s) v ≃ {l : Copy // l ∈ (state s).live} :=
    { toFun := fun l => ⟨l.val, l.property.1⟩
      invFun := fun l => ⟨l.val, l.property, hall l.val l.property⟩
      left_inv := fun l => by cases l; rfl
      right_inv := fun l => by cases l; rfl }
  calc
    Fintype.card (AtNode (state s) v) =
        Fintype.card {l : Copy // l ∈ (state s).live} := Fintype.card_congr e
    _ = liveCard s := by
      simp [liveCard]
      rfl

noncomputable def edgeDiagonal (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(pairRate r (some e) * (n.choose 2 : ℝ) *
    (edgeDuration N C e : ℝ))))

noncomputable def armSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (B : NonrootBigon N) (bit : Bool) : ℝ :=
  Real.exp (-(pairRate r (some (B.parents.parent bit)) * (bigonDuration N C B : ℝ)))

/-- true is original parent1, as in the native pulse and natural register. -/
noncomputable def independentDiagonal (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (B : NonrootBigon N) (gamma : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ k ∈ Finset.range (n+1),
    (n.choose k : ℝ) * (1-(gamma:ℝ))^k * (gamma:ℝ)^(n-k) *
      (armSurvival N C r B false)^(k.choose 2) *
      (armSurvival N C r B true)^((n-k).choose 2))

noncomputable def commonDiagonal (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (B : NonrootBigon N) (register : V → Bool) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((armSurvival N C r B (register B.parents.hybrid))^(n.choose 2))

/-- Source-computed scalar product, conditional on the SAME original register. -/
noncomputable def spanDiagonal (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    (register : V → Bool) (n : ℕ) {a b : V} : OriginalSpan N a b → ℝ≥0∞
  | .edge e _ => edgeDiagonal N C r e n
  | .bigon B => if common B.parents.hybrid then commonDiagonal N C r B register n
      else independentDiagonal N C r B (gamma B.parents.hybrid) n
  | .append first last =>
      spanDiagonal N C r gamma common register n first *
        spanDiagonal N C r gamma common register n last

private theorem pmf_mass_of_real {A : Type*} (mu : PMF A) (a : A) (q : ℝ)
    (h : (mu a).toReal = q) : mu a = ENNReal.ofReal q := by
  calc
    mu a = ENNReal.ofReal ((mu a).toReal) :=
      (ENNReal.ofReal_toReal (PMF.apply_ne_top mu a)).symm
    _ = ENNReal.ofReal q := congrArg ENNReal.ofReal h

/-- Full original bigon program, including both original exits. -/
theorem actual_bigon_diagonal (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : V → unitInterval) (common : V → Bool) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid) :
    ((sourceProgram N r (bigonProgram N C B (gamma B.parents.hybrid)
      (common B.parents.hybrid)) s).map liveCard) (liveCard s) =
      spanDiagonal N C r gamma common (state s).register (liveCard s) (.bigon B) := by
  cases hc : common B.parents.hybrid with
  | false =>
      have h := actual_original_bigon_independent N C r B (gamma B.parents.hybrid) s hall
      dsimp only at h
      rw [all_roots_at_node_card N s B.parents.hybrid hall] at h
      simpa [spanDiagonal, hc, independentDiagonal, armSurvival,
        GProgram.G2.OriginalHybridParents.parent] using
        pmf_mass_of_real _ _ _ h
  | true =>
      have h := actual_original_bigon_common N C r B (gamma B.parents.hybrid) s hall
      dsimp only at h
      rw [all_roots_at_node_card N s B.parents.hybrid hall] at h
      cases hr : (state s).register B.parents.hybrid <;>
        simpa [spanDiagonal, hc, commonDiagonal, armSurvival, hr,
          GProgram.G2.OriginalHybridParents.parent] using
          pmf_mass_of_real _ _ _ h

/-- The row-constant premise of actual_no_loss_append is DERIVED from actual
typed exits, the induction hypothesis and actual register preservation. -/
theorem actual_original_span_no_loss (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : OriginalSpan N a b) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node a) :
    ((sourceProgram N r (spanProgram N C gamma common word) s).map liveCard)
      (liveCard s) =
      spanDiagonal N C r gamma common (state s).register (liveCard s) word := by
  induction word generalizing s with
  | edge e degree =>
      simpa [spanProgram, spanDiagonal, edgeDiagonal] using
        pmf_mass_of_real _ _ _ (actual_connector_no_loss N C r e degree s hall)
  | bigon B => exact actual_bigon_diagonal N C r B gamma common s hall
  | append first last ihfirst ihlast =>
      have hrow : ∀ d ∈ (sourceProgram N r (spanProgram N C gamma common first) s).support,
          liveCard d = liveCard s →
          ((sourceProgram N r (spanProgram N C gamma common last) d).map liveCard)
            (liveCard d) =
            spanDiagonal N C r gamma common (state s).register (liveCard s) last := by
        intro d hd hn
        rw [ihlast d (actual_original_span_exit_population N C r gamma common first s hall hd)]
        rw [hn, DotG34.ActualStoredRegister.actual_program_register_support N r
          (spanProgram N C gamma common first) s d hd]
      change ((sourceProgram N r (spanProgram N C gamma common first ++
        spanProgram N C gamma common last) s).map liveCard) (liveCard s) = _
      rw [actual_no_loss_append N r _ _ s _ hrow, ihfirst s hall]
      rfl

theorem spanDiagonal_ne_top (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    (register : V → Bool) (n : ℕ) {a b : V} (word : OriginalSpan N a b) :
    spanDiagonal N C r gamma common register n word ≠ ⊤ := by
  induction word with
  | edge e degree => exact ENNReal.ofReal_ne_top
  | bigon B =>
      simp only [spanDiagonal]
      split <;> exact ENNReal.ofReal_ne_top
  | append first last ihfirst ihlast => exact ENNReal.mul_ne_top ihfirst ihlast

/-- A source-local condition on the actual arms, not an assumed law equality.
Only COMMON cells used by this original span are constrained. -/
def EqualCommonArms (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (common : V → Bool) {a b : V} : OriginalSpan N a b → Prop
  | .edge _ _ => True
  | .bigon B => common B.parents.hybrid = true →
      armSurvival N C r B false = armSurvival N C r B true
  | .append first last => EqualCommonArms N C r common first ∧
      EqualCommonArms N C r common last

theorem spanDiagonal_register_independent (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    (register register' : V → Bool) (n : ℕ) {a b : V} (word : OriginalSpan N a b)
    (hequal : EqualCommonArms N C r common word) :
    spanDiagonal N C r gamma common register n word =
      spanDiagonal N C r gamma common register' n word := by
  induction word with
  | edge e degree => rfl
  | bigon B =>
      cases hc : common B.parents.hybrid with
      | false => simp [spanDiagonal, hc]
      | true =>
          have he := hequal hc
          cases hr : register B.parents.hybrid <;>
            cases hr' : register' B.parents.hybrid <;>
            simp [spanDiagonal, commonDiagonal, hc, hr, hr', he]
  | append first last ihfirst ihlast =>
      exact congrArg₂ (· * ·) (ihfirst hequal.1) (ihlast hequal.2)

/-- Arbitrary entrance histories may bias the register. Their actual mixture
is retained exactly; no fresh natural COMMON weight is substituted. -/
theorem actual_entrance_mixture_no_loss (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : OriginalSpan N a b) (prior : PMF (Code N sample)) (n : ℕ)
    (hcount : ∀ s ∈ prior.support, liveCard s = n)
    (hplace : ∀ s ∈ prior.support, ∀ l ∈ (state s).live,
      (state s).location l = .node a) :
    ((prior.bind (sourceProgram N r (spanProgram N C gamma common word))).map liveCard) n =
      ∑' s, prior s * spanDiagonal N C r gamma common (state s).register n word := by
  rw [PMF.map_bind, PMF.bind_apply]
  apply tsum_congr
  intro s
  by_cases hs : prior s = 0
  · simp [hs]
  · have hn := hcount s hs
    have hp := hplace s hs
    have he := actual_original_span_no_loss N C r gamma common word s hp
    rw [hn] at he
    rw [he]

/-- Once actual COMMON arms agree, even an arbitrary entrance-history bias
cannot affect this no-loss row. The actual entrance law is kept throughout. -/
theorem actual_equal_common_arms_entrance_no_loss
    (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : OriginalSpan N a b) (prior : PMF (Code N sample)) (n : ℕ)
    (hcount : ∀ s ∈ prior.support, liveCard s = n)
    (hplace : ∀ s ∈ prior.support, ∀ l ∈ (state s).live,
      (state s).location l = .node a)
    (hequal : EqualCommonArms N C r common word) (register : V → Bool) :
    ((prior.bind (sourceProgram N r (spanProgram N C gamma common word))).map liveCard) n =
      spanDiagonal N C r gamma common register n word := by
  rw [actual_entrance_mixture_no_loss N C r gamma common word prior n hcount hplace]
  simp_rw [spanDiagonal_register_independent N C r gamma common _ register n word hequal]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Distinct live representatives have different nonempty labelled trees.
Forgetting planar order therefore preserves the number of CURRENT roots. -/
theorem actual_rootForest_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : (rootForest N s).card = liveCard s := by
  unfold rootForest liveCard
  apply Finset.card_image_of_injOn
  intro l hl k hk he
  have ht := toUnranked_equal_leaves he
  have hlleaf : l ∈ ((state s).genealogy l).leaves :=
    (s.property.forest.leaf_fiber l hl l).mpr (s.property.forest.representative l hl)
  have hkleaf : l ∈ ((state s).genealogy k).leaves := ht ▸ hlleaf
  exact (s.property.forest.representative l hl).symm.trans
    ((s.property.forest.leaf_fiber k hk l).mp hkleaf)

/-- The derived scalar is a marginal of the complete UNNORMALIZED labelled
unranked forest law. It is not a conditional one-root shape probability. -/
theorem actual_original_span_forest_no_loss (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : OriginalSpan N a b) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node a) :
    (((sourceProgram N r (spanProgram N C gamma common word) s).map (rootForest N)).map
      Finset.card) (liveCard s) =
      spanDiagonal N C r gamma common (state s).register (liveCard s) word := by
  rw [PMF.map_comp]
  have hf : (Finset.card ∘ rootForest N : Code N sample → ℕ) = liveCard := by
    funext d
    exact actual_rootForest_card N d
  rw [hf]
  exact actual_original_span_no_loss N C r gamma common word s hall

end DotG34.ActualOriginalSpanDiagonal

#print axioms DotG34.ActualOriginalSpanDiagonal.actual_original_span_no_loss
#print axioms DotG34.ActualOriginalSpanDiagonal.actual_entrance_mixture_no_loss
#print axioms DotG34.ActualOriginalSpanDiagonal.actual_equal_common_arms_entrance_no_loss
#print axioms DotG34.ActualOriginalSpanDiagonal.actual_original_span_forest_no_loss
