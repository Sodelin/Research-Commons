import G4TwoRootSourceStopping
import G4AllRootPairClocks
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# NEW path-resolved private-source observation extension

Original positive current-root cell/edge carriers and pair survival recursion
are reused. The additional observable is the COMPLETE consistently labelled
original-parent itinerary on the NO-MERGER event. Its labels are measured,
not reconstructed from passive forests. Failure records no later split coins.
This finite first-merger/absorbing pair fragment does not silently assert the
still-open full graph-to-continuous-source refinement or original passive G4.
-/
namespace GProgram.G4.PathResolved
open G4TwoRootSourceStopping
open scoped BigOperators
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

abbrev Color (Site : Type*) := Site → Bool

noncomputable def itineraryMass (cells : Site → Cell) (c : Color Site) : ℝ :=
  ∏ i, coinWeight (cells i).bigon.g (c i)

noncomputable def localPairMass (C : Cell) (a b : Bool) : ℝ :=
  coinWeight C.bigon.g a * coinWeight C.bigon.g b *
    (C.connector.survival * pairRouteSurvival C.bigon.x C.bigon.y a b)

/-- The original live-pair branch likelihood. Later coins are unobserved on
failure; the all-surviving path multiplies its actual cell branch factors. -/
noncomputable def observedPair (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ := leading.survival * ∏ i, localPairMass (cells i) (c i) (d i)

noncomputable def hiddenKernel (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ := leading.survival * ∏ i,
      (cells i).connector.survival *
        pairRouteSurvival (cells i).bigon.x (cells i).bigon.y (c i) (d i)

noncomputable def measuredKernel (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ :=
  observedPair leading cells c d / (itineraryMass cells c * itineraryMass cells d)

lemma coinWeight_pos (B : PositiveBigon) (a : Bool) : 0 < coinWeight B.g a := by
  cases a <;> simp [coinWeight]
  · exact B.g_below_one
  · exact B.g_positive

lemma pairRouteSurvival_pos (B : PositiveBigon) (a b : Bool) :
    0 < pairRouteSurvival B.x B.y a b := by
  cases a <;> cases b <;> simp [pairRouteSurvival,B.x_positive,B.y_positive]

lemma itineraryMass_pos (cells : Site → Cell) (c : Color Site) :
    0 < itineraryMass cells c := by
  apply Finset.prod_pos
  intro i _
  exact coinWeight_pos (cells i).bigon (c i)

lemma itineraryMass_normalized (cells : Site → Cell) :
    (∑ c : Color Site, itineraryMass cells c) = 1 := by
  unfold itineraryMass
  rw [← Fintype.prod_sum]
  have h : ∀ i : Site, (∑ b : Bool, coinWeight (cells i).bigon.g b) = 1 := by
    intro i
    simp [coinWeight]
  simp only [h, Finset.prod_const_one]

/-- Every source itinerary has strictly positive mass, and the joint measured
no-merger likelihood is derived from cell branch factors rather than fitted. -/
theorem original_source_joint_itinerary_likelihood (leading : PositiveEdge)
    (cells : Site → Cell) (c d : Color Site) :
    observedPair leading cells c d =
      itineraryMass cells c * itineraryMass cells d * hiddenKernel leading cells c d := by
  unfold observedPair itineraryMass hiddenKernel localPairMass
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  ring

lemma localPairMass_sum (C : Cell) :
    (∑ a : Bool, ∑ b : Bool, localPairMass C a b) = cellSurvival C := by
  simp [localPairMass,cellSurvival,bareSurvival,coinWeight,pairRouteSurvival]
  ring

/-- This total agrees with the inherited absorbing original live-pair scalar
recursion. No two fresh coins are attached to a merged ancestral subtree. -/
theorem complete_joint_no_merger_mass (leading : PositiveEdge) (cells : Site → Cell) :
    (∑ c : Color Site, ∑ d : Color Site, observedPair leading cells c d) =
      leading.survival * ∏ i, cellSurvival (cells i) := by
  simp only [observedPair, ← Finset.mul_sum]
  congr 1
  simp_rw [← Fintype.prod_sum]
  rw [← Fintype.prod_sum (fun (i : Site) (a : Bool) =>
    ∑ b : Bool, localPairMass (cells i) a b)]
  simp only [localPairMass_sum]

/-- Source-faithful exact density reconstruction in the CHANGED menu. -/
theorem reconstructed_kernel_eq_original (leading : PositiveEdge)
    (cells : Site → Cell) (c d : Color Site) :
    measuredKernel leading cells c d = hiddenKernel leading cells c d := by
  rw [measuredKernel,original_source_joint_itinerary_likelihood]
  exact mul_div_cancel_left₀ _
    (ne_of_gt (mul_pos (itineraryMass_pos cells c) (itineraryMass_pos cells d)))

noncomputable def totalNoMerger (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  leading.survival * ∏ i, cellSurvival (cells i)

lemma totalNoMerger_pos (leading : PositiveEdge) (cells : Site → Cell) :
    0 < totalNoMerger leading cells :=
  mul_pos leading.positive (Finset.prod_pos (fun i _ => cellSurvival_positive (cells i)))

lemma totalNoMerger_lt_one (leading : PositiveEdge) (cells : Site → Cell) :
    totalNoMerger leading cells < 1 := by
  have hprod : (∏ i, cellSurvival (cells i)) ≤ (1 : ℝ) :=
    Finset.prod_le_one (fun i _ => (cellSurvival_positive (cells i)).le)
      (fun i _ => (cellSurvival_below_one (cells i)).le)
  have hp : 0 < (∏ i : Site, cellSurvival (cells i)) :=
    Finset.prod_pos (fun i _ => cellSurvival_positive (cells i))
  have hl := leading.positive
  have hl1 := leading.below_one
  unfold totalNoMerger
  nlinarith

noncomputable def outcomeMass (leading : PositiveEdge) (cells : Site → Cell) :
    Option (Color Site × Color Site) → ℝ
  | none => 1 - totalNoMerger leading cells
  | some pair => observedPair leading cells pair.1 pair.2

lemma outcomeMass_nonneg (leading : PositiveEdge) (cells : Site → Cell)
    (outcome : Option (Color Site × Color Site)) : 0 ≤ outcomeMass leading cells outcome := by
  cases outcome with
  | none => exact (sub_pos.mpr (totalNoMerger_lt_one leading cells)).le
  | some pair =>
    unfold outcomeMass observedPair
    apply mul_nonneg leading.positive.le
    apply Finset.prod_nonneg
    intro i _
    unfold localPairMass
    exact (mul_pos (mul_pos (coinWeight_pos (cells i).bigon _) (coinWeight_pos (cells i).bigon _))
      (mul_pos (cells i).connector.positive (pairRouteSurvival_pos (cells i).bigon _ _))).le

lemma outcomeMass_normalized (leading : PositiveEdge) (cells : Site → Cell) :
    (∑ o : Option (Color Site × Color Site), outcomeMass leading cells o) = 1 := by
  rw [Fintype.sum_option]
  simp only [outcomeMass, Fintype.sum_prod_type]
  rw [complete_joint_no_merger_mass]
  unfold totalNoMerger
  ring

/-- Genuine normalized terminated pair PMF: failure is absorbing and carries
no later itinerary bits. The complete success record is retained jointly. -/
noncomputable def sourcePairPMF (leading : PositiveEdge) (cells : Site → Cell) :
    PMF (Option (Color Site × Color Site)) :=
  PMF.ofFintype (fun o => ENNReal.ofReal (outcomeMass leading cells o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => outcomeMass_nonneg leading cells o),
      outcomeMass_normalized]
    norm_num)

theorem sourcePairPMF_joint_record (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) :
    sourcePairPMF leading cells (some (c,d)) =
      ENNReal.ofReal (itineraryMass cells c * itineraryMass cells d *
        hiddenKernel leading cells c d) := by
  simp only [sourcePairPMF,PMF.ofFintype_apply,outcomeMass]
  rw [original_source_joint_itinerary_likelihood]

/-- Every finite root count uses the existing actual product of independent
unit pair clocks. Positive source survival encodes its finite hazard duration;
this does not equate physical time and hazard time or supply a calendar. -/
theorem all_input_edge_clock_survival (edge : PositiveEdge) (n : Nat) :
    ((GProgram.G4.PairClocks.pairClockMeasure n)
      (GProgram.G4.PairClocks.noFirstMergeEvent n (-Real.log edge.survival))).toReal =
        edge.survival ^ (n.choose 2) := by
  rw [GProgram.G4.PairClocks.all_root_no_first_merge n
    (le_of_lt (neg_pos.mpr (Real.log_neg edge.positive edge.below_one))),
    neg_neg,Real.exp_log edge.positive]

/-- The complete measured no-merger law has the original absorbing live-pair
scalar recursion for a source word of ANY finite length. -/
theorem observed_mass_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) :
    (∑ c : Color (Fin (n+1)), ∑ d : Color (Fin (n+1)),
      observedPair leading (Fin.cons C rest) c d) =
      serialUnmerged (cellSurvival C)
        (∑ c : Color (Fin n), ∑ d : Color (Fin n), observedPair leading rest c d) := by
  rw [complete_joint_no_merger_mass,complete_joint_no_merger_mass]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,serialUnmerged]
  ring

section OriginalLabels
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable {N : RootedBinary V E X}

noncomputable def observedOriginalParents (H : Site → GProgram.G2.OriginalHybridParents N)
    (c : Color Site) : Site → E := fun i => (H i).parent (c i)

/-- Added route labels refer to the SAME original parent edges. Their genuine
observation distinguishes full bits without inventing compressed actuators. -/
theorem complete_original_parent_readout_injective
    (H : Site → GProgram.G2.OriginalHybridParents N) :
    Function.Injective (observedOriginalParents H) := by
  intro c d he
  funext i
  exact (H i).parent_injective (congrFun he i)
/-- ALL input counts, using actual ORIGINAL parent IDs and independent
finite first-merger clocks on the two original private arms. Here parent1
has x-survival and parent0 has y-survival, matching the reused true-bit table. -/
theorem original_all_input_arm_clock_likelihood
    (H : GProgram.G2.OriginalHybridParents N) (B : PositiveBigon)
    (n : Nat) (coin : Fin n → Bool) :
    let k1 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card
    let k0 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card
    (((GProgram.G4.PairClocks.pairClockMeasure k1).prod
        (GProgram.G4.PairClocks.pairClockMeasure k0))
      (GProgram.G4.PairClocks.noFirstMergeEvent k1 (-Real.log B.x) ×ˢ
       GProgram.G4.PairClocks.noFirstMergeEvent k0 (-Real.log B.y))).toReal =
      B.x ^ ((GProgram.G4.IndependentRouting.count1 coin).choose 2) *
      B.y ^ ((GProgram.G4.IndependentRouting.count0 coin).choose 2) := by
  dsimp only
  rw [GProgram.G4.IndependentRouting.actual_parent1_count H coin,
    GProgram.G4.IndependentRouting.actual_parent0_count H coin]
  rw [GProgram.G4.PairClocks.private_arms_no_first_merge _ _
      (le_of_lt (neg_pos.mpr (Real.log_neg B.x_positive B.x_below_one)))
      (le_of_lt (neg_pos.mpr (Real.log_neg B.y_positive B.y_below_one))),
    GProgram.G4.IndependentRouting.firstHoldingKernel_eq_power
      (le_of_lt (neg_pos.mpr (Real.log_neg B.x_positive B.x_below_one))),
    GProgram.G4.IndependentRouting.firstHoldingKernel_eq_power
      (le_of_lt (neg_pos.mpr (Real.log_neg B.y_positive B.y_below_one))),
    neg_neg,neg_neg,Real.exp_log B.x_positive,Real.exp_log B.y_positive]

/-- The recorded two-live-root branch survival is the special case of the
source's genuine all-input current-parent clock likelihood, not a fitted W. -/
theorem original_two_live_root_clock_branch
    (H : GProgram.G2.OriginalHybridParents N) (B : PositiveBigon) (a b : Bool) :
    let coin : Fin 2 → Bool := ![a,b]
    let k1 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card
    let k0 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card
    (((GProgram.G4.PairClocks.pairClockMeasure k1).prod
        (GProgram.G4.PairClocks.pairClockMeasure k0))
      (GProgram.G4.PairClocks.noFirstMergeEvent k1 (-Real.log B.x) ×ˢ
       GProgram.G4.PairClocks.noFirstMergeEvent k0 (-Real.log B.y))).toReal =
        pairRouteSurvival B.x B.y a b := by
  dsimp only
  rw [original_all_input_arm_clock_likelihood H B 2 ![a,b]]
  change B.x ^ ((GProgram.G4.IndependentRouting.count1
    (Fin.cons a (Fin.cons b (fun i : Fin 0 => Fin.elim0 i)))).choose 2) *
    B.y ^ ((GProgram.G4.IndependentRouting.count0
    (Fin.cons a (Fin.cons b (fun i : Fin 0 => Fin.elim0 i)))).choose 2) = _
  rw [GProgram.G4.IndependentRouting.count1_cons,GProgram.G4.IndependentRouting.count1_cons,
    GProgram.G4.IndependentRouting.count0_cons,GProgram.G4.IndependentRouting.count0_cons]
  cases a <;> cases b <;>
    norm_num [GProgram.G4.IndependentRouting.count0,GProgram.G4.IndependentRouting.count1,
      Fin.sum_univ_zero,pairRouteSurvival,Nat.choose]

end OriginalLabels

noncomputable def cycleDensity (p : Color Site → ℝ) (W : Color Site → Color Site → ℝ) : ℝ :=
  ∑ a : Color Site, ∑ b : Color Site, ∑ c : Color Site, ∑ d : Color Site,
    p a * p b * p c * p d * W a b * W b c * W c d * W d a

noncomputable def measuredC4 (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  cycleDensity (itineraryMass cells) (measuredKernel leading cells)

noncomputable def sourceC4 (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  cycleDensity (itineraryMass cells) (hiddenKernel leading cells)

/-- A finite rational expression in the actual one-root and two-root itinerary laws
returns hidden C4; no graph-density observation was assumed as a primitive. -/
theorem path_resolved_C4_reconstruction (leading : PositiveEdge) (cells : Site → Cell) :
    measuredC4 leading cells = sourceC4 leading cells := by
  simp only [measuredC4,sourceC4,cycleDensity]
  simp_rw [reconstructed_kernel_eq_original]

/-- The explicit two-type C4 factor, a specialization of finite weighted
edge/C4 forcing; no new graphon theorem is claimed. -/
noncomputable def bareC4 (B : PositiveBigon) : ℝ :=
  B.g^4 * B.x^4 + (1-B.g)^4 * B.y^4 +
    4*B.g^3*(1-B.g)*B.x^2 + 4*B.g*(1-B.g)^3*B.y^2 +
    4*B.g^2*(1-B.g)^2*B.x*B.y + 2*B.g^2*(1-B.g)^2

noncomputable def localCycle (C : Cell) (a b c d : Bool) : ℝ :=
  C.connector.survival^4 *
    (coinWeight C.bigon.g a * coinWeight C.bigon.g b *
      coinWeight C.bigon.g c * coinWeight C.bigon.g d *
      pairRouteSurvival C.bigon.x C.bigon.y a b *
      pairRouteSurvival C.bigon.x C.bigon.y b c *
      pairRouteSurvival C.bigon.x C.bigon.y c d *
      pairRouteSurvival C.bigon.x C.bigon.y d a)

lemma localCycle_sum (C : Cell) :
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, localCycle C a b c d) =
      C.connector.survival^4 * bareC4 C.bigon := by
  simp [localCycle,bareC4,coinWeight,pairRouteSurvival]
  ring

lemma cycle_term_factor (leading : PositiveEdge) (cells : Site → Cell)
    (a b c d : Color Site) :
    itineraryMass cells a * itineraryMass cells b * itineraryMass cells c *
      itineraryMass cells d * hiddenKernel leading cells a b * hiddenKernel leading cells b c *
      hiddenKernel leading cells c d * hiddenKernel leading cells d a =
        leading.survival^4 * ∏ i, localCycle (cells i) (a i) (b i) (c i) (d i) := by
  unfold itineraryMass hiddenKernel localCycle
  simp only [Finset.prod_mul_distrib,Finset.prod_pow]
  ring

lemma sum_four_site_products (f : Site → Bool → Bool → Bool → Bool → ℝ) :
    (∑ a : Color Site, ∑ b : Color Site, ∑ c : Color Site, ∑ d : Color Site,
      ∏ i, f i (a i) (b i) (c i) (d i)) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f i a b c d := by
  calc
    _ = ∑ a : Color Site, ∑ b : Color Site, ∑ c : Color Site,
        ∏ i, ∑ d : Bool, f i (a i) (b i) (c i) d := by
      simp_rw [← Fintype.prod_sum]
    _ = ∑ a : Color Site, ∑ b : Color Site,
        ∏ i, ∑ c : Bool, ∑ d : Bool, f i (a i) (b i) c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact (Fintype.prod_sum (fun (i : Site) (c : Bool) =>
        ∑ d : Bool, f i (a i) (b i) c d)).symm
    _ = ∑ a : Color Site, ∏ i, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f i (a i) b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Fintype.prod_sum (fun (i : Site) (b : Bool) =>
        ∑ c : Bool, ∑ d : Bool, f i (a i) b c d)).symm
    _ = _ := (Fintype.prod_sum (fun (i : Site) (a : Bool) =>
        ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f i a b c d)).symm

noncomputable def ordinaryScalar (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  leading.survival * ∏ i, (cells i).connector.survival

/-- Full tensor cycle density, not a separately postulated cell mark. -/
theorem sourceC4_word_factorization (leading : PositiveEdge) (cells : Site → Cell) :
    sourceC4 leading cells = (ordinaryScalar leading cells)^4 * ∏ i, bareC4 (cells i).bigon := by
  unfold sourceC4 cycleDensity
  simp_rw [cycle_term_factor]
  simp only [← Finset.mul_sum]
  rw [sum_four_site_products]
  simp only [localCycle_sum,Finset.prod_mul_distrib,Finset.prod_pow,ordinaryScalar,mul_pow]
  ring

/-- Strict weighted Gram/Cauchy inequality for every genuine positive original
binary cell. Its arm matrix cannot be constant: both arm survivals are <1. -/
theorem positive_bigon_C4_strict (B : PositiveBigon) : bareSurvival B ^ 4 < bareC4 B := by
  let g := B.g
  let h := 1-B.g
  let k00 := g*B.x^2+h
  let k01 := g*B.x+h*B.y
  let k11 := g+h*B.y^2
  let m := g^2*k00+2*g*h*k01+h^2*k11
  have hg : 0 < g := B.g_positive
  have hh : 0 < h := sub_pos.mpr B.g_below_one
  have hx2 : 0 < (B.x-1)^2 := sq_pos_of_ne_zero (by have := B.x_below_one; linarith)
  have hy2 : 0 < (B.y-1)^2 := sq_pos_of_ne_zero (by have := B.y_below_one; linarith)
  have hk : 0 < k00+k11-2*k01 := by
    have he : k00+k11-2*k01 = g*(B.x-1)^2+h*(B.y-1)^2 := by dsimp [k00,k01,k11]; ring
    rw [he]
    exact add_pos (mul_pos hg hx2) (mul_pos hh hy2)
  have hv : bareC4 B - m^2 = 2*g^3*h*(k00-k01)^2+
      g^2*h^2*(k00-k11)^2+2*g*h^3*(k01-k11)^2 := by
    dsimp [bareC4,m,k00,k01,k11,g,h]
    ring
  have hvpos : 0 < bareC4 B-m^2 := by
    rw [hv]
    have h1 : 0 ≤ 2*g^3*h*(k00-k01)^2 := by positivity
    have h2 : 0 ≤ g^2*h^2*(k00-k11)^2 := by positivity
    have h3 : 0 ≤ 2*g*h^3*(k01-k11)^2 := by positivity
    by_cases ha : k00=k01
    · have hb : k01-k11 ≠ 0 := by intro he; linarith
      have h3p : 0 < 2*g*h^3*(k01-k11)^2 := by positivity
      linarith
    · have ha' : k00-k01 ≠ 0 := sub_ne_zero.mpr ha
      have h1p : 0 < 2*g^3*h*(k00-k01)^2 := by positivity
      linarith
  have hm : bareSurvival B ^ 2 ≤ m := by
    have he : m-bareSurvival B^2 = g*h*((g*B.x+h)-(g+h*B.y))^2 := by
      rw [bareSurvival_eq]
      dsimp [m,k00,k01,k11,g,h]
      ring
    have hn : 0 ≤ g*h*((g*B.x+h)-(g+h*B.y))^2 := by positivity
    linarith
  have hm0 : 0 ≤ m := (sq_nonneg (bareSurvival B)).trans hm
  have hmul := mul_nonneg (sub_nonneg.mpr hm) (add_nonneg hm0 (sq_nonneg (bareSurvival B)))
  nlinarith

lemma ordinaryScalar_pos (leading : PositiveEdge) (cells : Site → Cell) :
    0 < ordinaryScalar leading cells :=
  mul_pos leading.positive (Finset.prod_pos (fun i _ => (cells i).connector.positive))

lemma totalNoMerger_factorization (leading : PositiveEdge) (cells : Site → Cell) :
    totalNoMerger leading cells = ordinaryScalar leading cells * ∏ i, bareSurvival (cells i).bigon := by
  unfold totalNoMerger ordinaryScalar cellSurvival
  rw [Finset.prod_mul_distrib]
  ring

/-- ANY finite nonempty private word is separated in the stronger menu. No
margin, known rival length bound or fitted hidden arm is assumed. -/
theorem sourceC4_strict_of_genuine_bigon [Nonempty Site]
    (leading : PositiveEdge) (cells : Site → Cell) :
    totalNoMerger leading cells ^ 4 < sourceC4 leading cells := by
  have hp : (∏ i, bareSurvival (cells i).bigon ^ 4) < ∏ i, bareC4 (cells i).bigon := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      exact pow_pos (bareSurvival_positive (cells i).bigon) 4
    · intro i _
      exact positive_bigon_C4_strict (cells i).bigon
    · exact Finset.univ_nonempty
  rw [Finset.prod_pow] at hp
  rw [sourceC4_word_factorization,totalNoMerger_factorization,mul_pow]
  exact mul_lt_mul_of_pos_left hp (pow_pos (ordinaryScalar_pos leading cells) 4)

noncomputable def sourceItineraryPMF (cells : Site → Cell) : PMF (Color Site) :=
  PMF.ofFintype (fun c => ENNReal.ofReal (itineraryMass cells c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => (itineraryMass_pos cells c).le),
      itineraryMass_normalized]
    norm_num)

noncomputable def oneRootData (cells : Site → Cell) (c : Color Site) : ℝ :=
  (sourceItineraryPMF cells c).toReal

noncomputable def twoRootJointData (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ := (sourcePairPMF leading cells (some (c,d))).toReal

lemma oneRootData_eq (cells : Site → Cell) (c : Color Site) :
    oneRootData cells c = itineraryMass cells c := by
  simp only [oneRootData,sourceItineraryPMF,PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (itineraryMass_pos cells c).le

lemma twoRootJointData_eq (leading : PositiveEdge) (cells : Site → Cell) (c d : Color Site) :
    twoRootJointData leading cells c d = observedPair leading cells c d := by
  simp only [twoRootJointData,sourcePairPMF,PMF.ofFintype_apply,outcomeMass]
  exact ENNReal.toReal_ofReal (outcomeMass_nonneg leading cells (some (c,d)))

/-- A formula consuming the NORMALIZED one-root and two-current-root PMF data. -/
noncomputable def dataKernel (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ :=
  twoRootJointData leading cells c d / (oneRootData cells c * oneRootData cells d)

noncomputable def dataC4 (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  cycleDensity (oneRootData cells) (dataKernel leading cells)

noncomputable def dataPairSurvival (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  ∑ c : Color Site, ∑ d : Color Site, twoRootJointData leading cells c d

theorem normalized_PMF_data_C4_reconstruction (leading : PositiveEdge) (cells : Site → Cell) :
    dataC4 leading cells = sourceC4 leading cells := by
  unfold dataC4 sourceC4 cycleDensity dataKernel
  simp_rw [oneRootData_eq,twoRootJointData_eq]
  change cycleDensity (itineraryMass cells) (measuredKernel leading cells) = _
  exact path_resolved_C4_reconstruction leading cells

lemma dataPairSurvival_eq (leading : PositiveEdge) (cells : Site → Cell) :
    dataPairSurvival leading cells = totalNoMerger leading cells := by
  unfold dataPairSurvival
  simp_rw [twoRootJointData_eq]
  exact complete_joint_no_merger_mass leading cells

/-- Complete success records satisfy the ACTUAL sequential live-pair branch
recursion. The leading edge is used once, and records never split merged roots. -/
theorem joint_record_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) (c d : Color (Fin (n+1))) :
    observedPair leading (Fin.cons C rest) c d =
      localPairMass C (c 0) (d 0) * observedPair leading rest (Fin.tail c) (Fin.tail d) := by
  unfold observedPair
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.tail]
  ring

/-- First merger is an absorbing OBSERVER outcome, even though the original
biological process may continue on its one opaque surviving ancestral root. -/
theorem failure_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) :
    outcomeMass leading (Fin.cons C rest) none = (1-leading.survival) +
      leading.survival * ((1-cellSurvival C) + cellSurvival C *
        (1-∏ i, cellSurvival (rest i))) := by
  simp only [outcomeMass,totalNoMerger,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

/-- Coherent changed-menu END THEOREM: the exact measured one-root and two-root joint
itinerary laws detect ordinary/no-independent-bigon words of UNKNOWN length.
The no-bigon scalar is the positive ordinary survival, not identity or time. -/
theorem path_resolved_ordinary_detection (leading : PositiveEdge) (cells : Site → Cell) :
    dataC4 leading cells = dataPairSurvival leading cells ^ 4 ↔ IsEmpty Site := by
  rw [normalized_PMF_data_C4_reconstruction,dataPairSurvival_eq]
  rcases isEmpty_or_nonempty Site with h | h
  · letI := h
    constructor
    · intro _
      exact h
    · intro _
      simp [sourceC4_word_factorization,totalNoMerger_factorization,ordinaryScalar]
  · letI := h
    constructor
    · intro he
      have ht := sourceC4_strict_of_genuine_bigon leading cells
      rw [he] at ht
      exact False.elim ((lt_irrefl _) ht)
    · intro hi
      obtain ⟨i⟩ := h
      exact False.elim (hi.false i)

/-- No-bigon does NOT mean zero population length. Its observable pair
survival is the original strictly positive finite leading ordinary scalar. -/
theorem ordinary_no_bigon_scalar [IsEmpty Site] (leading : PositiveEdge) (cells : Site → Cell) :
    dataPairSurvival leading cells = leading.survival ∧
      dataC4 leading cells = leading.survival ^ 4 := by
  rw [dataPairSurvival_eq,normalized_PMF_data_C4_reconstruction]
  simp [totalNoMerger,sourceC4_word_factorization,ordinaryScalar]

#print axioms original_all_input_arm_clock_likelihood
#print axioms original_two_live_root_clock_branch
#print axioms joint_record_cons_recursion
#print axioms failure_cons_recursion
#print axioms path_resolved_ordinary_detection
#print axioms normalized_PMF_data_C4_reconstruction
#print axioms sourceC4_strict_of_genuine_bigon
#print axioms ordinary_no_bigon_scalar
#print axioms sourceC4_word_factorization
#print axioms positive_bigon_C4_strict
#print axioms sourcePairPMF_joint_record
#print axioms all_input_edge_clock_survival
#print axioms observed_mass_cons_recursion
#print axioms complete_original_parent_readout_injective
#print axioms original_source_joint_itinerary_likelihood
#print axioms complete_joint_no_merger_mass
#print axioms reconstructed_kernel_eq_original
#print axioms path_resolved_C4_reconstruction
end GProgram.G4.PathResolved
