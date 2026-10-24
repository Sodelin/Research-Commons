import ResearchCommons.MSCI.JC69
import G2ChronologicalDecoration
import Mathlib.Data.Fintype.Pi

/-! Downstream formalization of the retained clock-JC forest Fourier law.
The tree and real graft decorations are the ORIGINAL source types. Conditional
sites share this same whole tree and all branch coordinates. This module does
not supply the metric-law/channel measure join, bounded exponential recurrence,
canonical MSci source admission, or the complete observation-equivalence claim.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
namespace ResearchCommons.MSCI.JC69Tree
open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration
open GProgram.G2.ChronologicalDecoration
open ResearchCommons.MSCI.JC69
open scoped BigOperators NNReal Classical
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- One base at each leaf OCCURRENCE of the original complete genealogy.
Well-labelled actual trees identify these occurrences with original copy IDs. -/
def Pattern : Genealogy Copy → Type
  | .leaf _ => Base
  | .graft a b => Pattern a × Pattern b

instance patternFintype : (t : Genealogy Copy) → Fintype (Pattern t)
  | .leaf _ => inferInstanceAs (Fintype Base)
  | .graft a b => by
      letI := patternFintype a
      letI := patternFintype b
      exact inferInstanceAs (Fintype (Pattern a × Pattern b))

/-- Numerical branch coordinates on the SAME original tree, in left/right
occurrence order. The clock encoder below derives them from the actual ages. -/
def Survivals : Genealogy Copy → Type
  | .leaf _ => PUnit
  | .graft a b => ℝ × ℝ × Survivals a × Survivals b

def Admitted : (t : Genealogy Copy) → Survivals t → Prop
  | .leaf _, _ => True
  | .graft a b, x =>
      (0 ≤ x.1 ∧ x.1 ≤ 1) ∧ (0 ≤ x.2.1 ∧ x.2.1 ≤ 1) ∧
        Admitted a x.2.2.1 ∧ Admitted b x.2.2.2

def likelihood : (t : Genealogy Copy) → Survivals t → Base → Pattern t → ℝ
  | .leaf _, _, a, p => if a = p then 1 else 0
  | .graft a b, x, c, p =>
      (∑ d : Base, probability x.1 c d * likelihood a x.2.2.1 d p.1) *
        (∑ d : Base, probability x.2.1 c d * likelihood b x.2.2.2 d p.2)

private theorem sum_product {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) :
    (∑ p : A × B, f p.1 * g p.2) = (∑ a : A, f a) * (∑ b : B, g b) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

private theorem message_sum {A : Type*} [Fintype A]
    (f : Base → A → ℝ) (h : ∀ b, (∑ p : A, f b p) = 1) (x : ℝ) (a : Base) :
    (∑ p : A, ∑ b : Base, probability x a b * f b p) = 1 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, h, mul_one]
  exact probability_row_sum x a

theorem likelihood_sum (t : Genealogy Copy) (x : Survivals t) (a : Base) :
    (∑ p : Pattern t, likelihood t x a p) = 1 := by
  induction t generalizing a with
  | leaf z => simp [likelihood, Pattern]
  | graft l r hl hr =>
      change (∑ p : Pattern l × Pattern r,
        (∑ b : Base, probability x.1 a b * likelihood l x.2.2.1 b p.1) *
        (∑ b : Base, probability x.2.1 a b * likelihood r x.2.2.2 b p.2)) = 1
      rw [sum_product
        (fun p => ∑ b : Base, probability x.1 a b * likelihood l x.2.2.1 b p)
        (fun p => ∑ b : Base, probability x.2.1 a b * likelihood r x.2.2.2 b p),
        message_sum _ (fun b => hl _ b),
        message_sum _ (fun b => hr _ b), one_mul]

theorem likelihood_nonnegative (t : Genealogy Copy) (x : Survivals t)
    (hx : Admitted t x) (a : Base) (p : Pattern t) :
    0 ≤ likelihood t x a p := by
  induction t generalizing a with
  | leaf z => simp only [likelihood]; split <;> norm_num
  | graft l r hl hr =>
      apply mul_nonneg
      · apply Finset.sum_nonneg
        intro b _
        exact mul_nonneg (probability_nonnegative hx.1.1 hx.1.2 a b)
          (hl _ hx.2.2.1 b p.1)
      · apply Finset.sum_nonneg
        intro b _
        exact mul_nonneg (probability_nonnegative hx.2.1.1 hx.2.1.2 a b)
          (hr _ hx.2.2.2 b p.2)

def kernel (t : Genealogy Copy) (x : Survivals t) (hx : Admitted t x) (a : Base) :
    PMF (Pattern t) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (likelihood t x a p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => likelihood_nonnegative t x hx a p),
      likelihood_sum]
    simp)

theorem kernel_probability (t : Genealogy Copy) (x : Survivals t)
    (hx : Admitted t x) (a : Base) (p : Pattern t) :
    (kernel t x hx a p).toReal = likelihood t x a p := by
  change (ENNReal.ofReal (likelihood t x a p)).toReal = _
  exact ENNReal.toReal_ofReal (likelihood_nonnegative t x hx a p)

def rootLikelihood (t : Genealogy Copy) (x : Survivals t) (p : Pattern t) : ℝ :=
  ∑ a : Base, (1/4 : ℝ) * likelihood t x a p

theorem root_likelihood_sum (t : Genealogy Copy) (x : Survivals t) :
    (∑ p : Pattern t, rootLikelihood t x p) = 1 := by
  unfold rootLikelihood
  rw [Finset.sum_comm]
  calc
    (∑ a : Base, ∑ p : Pattern t, (1/4 : ℝ) * likelihood t x a p) =
        ∑ a : Base, (1/4 : ℝ) * ∑ p : Pattern t, likelihood t x a p := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = 1 := by
      simp_rw [likelihood_sum, mul_one]
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]

theorem root_likelihood_nonnegative (t : Genealogy Copy) (x : Survivals t)
    (hx : Admitted t x) (p : Pattern t) : 0 ≤ rootLikelihood t x p := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (by norm_num) (likelihood_nonnegative t x hx a p)

def rootKernel (t : Genealogy Copy) (x : Survivals t) (hx : Admitted t x) :
    PMF (Pattern t) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (rootLikelihood t x p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => root_likelihood_nonnegative t x hx p),
      root_likelihood_sum]
    simp)

theorem root_kernel_probability (t : Genealogy Copy) (x : Survivals t)
    (hx : Admitted t x) (p : Pattern t) :
    (rootKernel t x hx p).toReal = rootLikelihood t x p := by
  change (ENNReal.ofReal (rootLikelihood t x p)).toReal = _
  exact ENNReal.toReal_ofReal (root_likelihood_nonnegative t x hx p)

def totalCharge (charges : Copy → Base) : Genealogy Copy → Base
  | .leaf c => charges c
  | .graft a b => totalCharge charges a + totalCharge charges b

def patternCharacter (charges : Copy → Base) :
    (t : Genealogy Copy) → Pattern t → ℝ
  | .leaf c, p => character (charges c) p
  | .graft a b, p => patternCharacter charges a p.1 * patternCharacter charges b p.2

def amplitude (charges : Copy → Base) : (t : Genealogy Copy) → Survivals t → ℝ
  | .leaf _, _ => 1
  | .graft a b, x =>
      ((if totalCharge charges a = 0 then 1 else x.1) * amplitude charges a x.2.2.1) *
        ((if totalCharge charges b = 0 then 1 else x.2.1) * amplitude charges b x.2.2.2)

/-- Original well-labelled source descendants, not old subtree leaf weights,
supply the current-block charge. -/
theorem totalCharge_eq_original_leaves (charges : Copy → Base) (t : Genealogy Copy)
    (ht : t.WellLabelled) :
    totalCharge charges t = ∑ c ∈ t.leaves, charges c := by
  induction t with
  | leaf c => simp [totalCharge, Genealogy.leaves]
  | graft a b ha hb =>
      rw [totalCharge, Genealogy.leaves, Finset.sum_union ht.2.2,
        ← ha ht.1, ← hb ht.2.1]

private theorem message_fourier {A : Type*} [Fintype A]
    (f : Base → A → ℝ) (chi : A → ℝ) (k : Base) (amp x : ℝ)
    (h : ∀ b, (∑ p : A, f b p * chi p) = amp * character k b) (a : Base) :
    (∑ p : A, (∑ b : Base, probability x a b * f b p) * chi p) =
      ((if k = 0 then 1 else x) * amp) * character k a := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, h]
  calc
    (∑ b : Base, probability x a b * (amp * character k b)) =
        amp * ∑ b : Base, probability x a b * character k b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [fourier_transfer]; ring

private theorem product_fourier {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) (c : A → ℝ) (d : B → ℝ) :
    (∑ p : A × B, (f p.1 * g p.2) * (c p.1 * d p.2)) =
      (∑ a : A, f a * c a) * (∑ b : B, g b * d b) := by
  calc
    _ = ∑ p : A × B, (f p.1 * c p.1) * (g p.2 * d p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := sum_product (fun a => f a * c a) (fun b => g b * d b)

/-- Complete all-finite-tree Fourier law of the constructed branch channel.
No conditional expectation or target Fourier identity is an input field. -/
theorem tree_fourier (t : Genealogy Copy) (x : Survivals t)
    (charges : Copy → Base) (a : Base) :
    (∑ p : Pattern t, likelihood t x a p * patternCharacter charges t p) =
      amplitude charges t x * character (totalCharge charges t) a := by
  induction t generalizing a with
  | leaf c => simp [Pattern, likelihood, patternCharacter, amplitude, totalCharge]
  | graft l r hl hr =>
      change (∑ p : Pattern l × Pattern r,
        ((∑ b : Base, probability x.1 a b * likelihood l x.2.2.1 b p.1) *
         (∑ b : Base, probability x.2.1 a b * likelihood r x.2.2.2 b p.2)) *
        (patternCharacter charges l p.1 * patternCharacter charges r p.2)) = _
      rw [product_fourier
        (fun p => ∑ b : Base, probability x.1 a b * likelihood l x.2.2.1 b p)
        (fun p => ∑ b : Base, probability x.2.1 a b * likelihood r x.2.2.2 b p)
        (patternCharacter charges l) (patternCharacter charges r),
        message_fourier _ _ _ _ _ (fun b => hl _ b),
        message_fourier _ _ _ _ _ (fun b => hr _ b)]
      rw [amplitude, totalCharge, character_add]
      ring

private theorem uniform_character (k : Base) :
    (∑ a : Base, (1/4 : ℝ) * character k a) = if k = 0 then 1 else 0 := by
  rcases k with ⟨k0,k1⟩
  fin_cases k0 <;> fin_cases k1 <;>
    norm_num [character, bitSign, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem root_fourier (t : Genealogy Copy) (x : Survivals t) (charges : Copy → Base) :
    (∑ p : Pattern t, rootLikelihood t x p * patternCharacter charges t p) =
      if totalCharge charges t = 0 then amplitude charges t x else 0 := by
  unfold rootLikelihood
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, tree_fourier]
  calc
    ((1/4 : ℝ) * ∑ a : Base,
      amplitude charges t x * character (totalCharge charges t) a) =
        amplitude charges t x * ∑ a : Base, (1/4 : ℝ) *
          character (totalCharge charges t) a := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [uniform_character]
      split <;> simp_all

/-- The original label assignment induces the SAME occurrence assignment.
A well-labelled tree has no duplicated original copy. -/
def labelPattern (t : Genealogy Copy) (p : Copy → Base) : Pattern t :=
  match t with
  | .leaf c => p c
  | .graft a b => (labelPattern a p, labelPattern b p)

theorem label_pattern_character (charges p : Copy → Base) (t : Genealogy Copy)
    (ht : t.WellLabelled) :
    patternCharacter charges t (labelPattern t p) =
      ∏ c ∈ t.leaves, character (charges c) (p c) := by
  induction t with
  | leaf c => simp [patternCharacter, labelPattern, Genealogy.leaves]
  | graft a b ha hb =>
      rw [patternCharacter, labelPattern, Genealogy.leaves,
        Finset.prod_union ht.2.2, ha ht.1, hb ht.2.1]

/-- A pattern is read at the ORIGINAL copy IDs. Values outside this tree's
leaf set are immaterial; a complete actual single-root source covers all IDs. -/
def patternLabels : (t : Genealogy Copy) → Pattern t → Copy → Base
  | .leaf _, p, _ => p
  | .graft a b, p, c =>
      if c ∈ a.leaves then patternLabels a p.1 c else patternLabels b p.2 c

private theorem label_pattern_congr (t : Genealogy Copy) (p q : Copy → Base)
    (h : ∀ c ∈ t.leaves, p c = q c) : labelPattern t p = labelPattern t q := by
  induction t with
  | leaf c => exact h c (Finset.mem_singleton_self c)
  | graft a b ha hb =>
      apply Prod.ext
      · exact ha (fun c hc => h c (Finset.mem_union.mpr (Or.inl hc)))
      · exact hb (fun c hc => h c (Finset.mem_union.mpr (Or.inr hc)))

theorem pattern_labels_label_pattern (t : Genealogy Copy) (p : Copy → Base)
    (c : Copy) (hc : c ∈ t.leaves) :
    patternLabels t (labelPattern t p) c = p c := by
  induction t with
  | leaf z =>
      have hz : c = z := Finset.mem_singleton.mp hc
      subst c
      rfl
  | graft a b ha hb =>
      by_cases hca : c ∈ a.leaves
      · simpa only [patternLabels, labelPattern, if_pos hca] using ha hca
      · have hcb := (Finset.mem_union.mp hc).resolve_left hca
        simpa only [patternLabels, labelPattern, if_neg hca] using hb hcb

theorem label_pattern_pattern_labels (t : Genealogy Copy) (ht : t.WellLabelled)
    (p : Pattern t) : labelPattern t (patternLabels t p) = p := by
  induction t with
  | leaf c => rfl
  | graft a b ha hb =>
      change (labelPattern a (patternLabels (.graft a b) p),
        labelPattern b (patternLabels (.graft a b) p)) = p
      apply Prod.ext
      · calc
          _ = labelPattern a (patternLabels a p.1) :=
            label_pattern_congr a _ _ (fun c hc => by
              simp only [patternLabels, if_pos hc])
          _ = p.1 := ha ht.1 p.1
      · calc
          _ = labelPattern b (patternLabels b p.2) :=
            label_pattern_congr b _ _ (fun c hc => by
              have hn : c ∉ a.leaves := fun h => Finset.disjoint_left.mp ht.2.2 h hc
              simp only [patternLabels, if_neg hn])
          _ = p.2 := hb ht.2.1 p.2

theorem original_pattern_readout_injective (t : Genealogy Copy) (ht : t.WellLabelled) :
    Function.Injective (patternLabels t) := by
  intro p q h
  have hh := congrArg (labelPattern t) h
  simpa only [label_pattern_pattern_labels t ht] using hh

theorem actual_single_root_covers_original_copies {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (hcard : s.live.card ≤ 1)
    (l : Copy) (hl : l ∈ s.live) : (s.genealogy l).leaves = Finset.univ := by
  ext c
  simp only [Finset.mem_univ, iff_true]
  apply (hs.leaf_fiber l hl c).mpr
  exact Finset.card_le_one.mp hcard (s.ancestor c) (hs.ancestor_live c) l hl

def clockSurvivals (leafAge : Copy → ℝ) :
    (t : Genealogy Copy) → Decoration t → Survivals t
  | .leaf _, _ => PUnit.unit
  | .graft a b, d =>
      (Real.exp (-((4/3 : ℝ) * (d.1 - rootAge leafAge a d.2.1))),
       Real.exp (-((4/3 : ℝ) * (d.1 - rootAge leafAge b d.2.2))),
       clockSurvivals leafAge a d.2.1, clockSurvivals leafAge b d.2.2)

theorem actual_clock_survivals_admitted (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (d : Decoration t) (hc : Chronological leafAge t d) :
    Admitted t (clockSurvivals leafAge t d) := by
  induction t with
  | leaf c => trivial
  | graft a b ha hb =>
      refine ⟨⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩,
        ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩,
        ha _ hc.1, hb _ hc.2.1⟩
      · have h := hc.2.2.1; nlinarith
      · have h := hc.2.2.2; nlinarith

/-- Genuine original SAME-matrix reconstruction. No new independent age fit,
chronological tree or desired channel equation is passed as a factory field. -/
theorem actual_decoded_chronology {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (leafAge : Copy → ℝ)
    (M : Copy → Copy → ℝ) (bound : ℝ) (hm : TimedBound leafAge M s bound)
    (l : Copy) (hl : l ∈ s.live) :
    Chronological leafAge (s.genealogy l) (decode M (s.genealogy l)) := by
  obtain ⟨d,hd,hc,_⟩ := hm l hl
  rw [decode_of_pair_agreement leafAge (s.genealogy l) (hs.wellLabelled l hl) d M hd]
  exact hc

def actualTreeKernel {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (bound : ℝ)
    (hm : TimedBound leafAge M s bound) (l : Copy) (hl : l ∈ s.live) :
    PMF (Pattern (s.genealogy l)) :=
  rootKernel (s.genealogy l) (clockSurvivals leafAge _ (decode M _))
    (actual_clock_survivals_admitted leafAge _ _
      (actual_decoded_chronology s hs leafAge M bound hm l hl))

theorem actual_tree_kernel_probability {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (bound : ℝ)
    (hm : TimedBound leafAge M s bound) (l : Copy) (hl : l ∈ s.live)
    (p : Pattern (s.genealogy l)) :
    (actualTreeKernel s hs leafAge M bound hm l hl p).toReal =
      rootLikelihood (s.genealogy l) (clockSurvivals leafAge _ (decode M _)) p :=
  root_kernel_probability _ _ _ _

/-- Concrete normalized original-label observation of this SAME decoded tree.
The actual full-source timed support supplies its valid state/chronology;
the unranked quotient and measure-level source mixing remain separate joins. -/
def actualLabelledTreeKernel {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (bound : ℝ)
    (hm : TimedBound leafAge M s bound) (l : Copy) (hl : l ∈ s.live) :
    PMF (Copy → Base) :=
  (actualTreeKernel s hs leafAge M bound hm l hl).map (patternLabels (s.genealogy l))

/-- Conditional sites share ONE whole genealogy and every clock coordinate.
Root bases are independently stationary per site, as in the retained theorem;
this is not a product of mixtures from separately drawn genealogies. -/
def locusLikelihood (L : Nat) (t : Genealogy Copy) (x : Survivals t)
    (p : Fin L → Pattern t) : ℝ := ∏ j, rootLikelihood t x (p j)

theorem locus_likelihood_sum (L : Nat) (t : Genealogy Copy) (x : Survivals t) :
    (∑ p : Fin L → Pattern t, locusLikelihood L t x p) = 1 := by
  unfold locusLikelihood
  rw [← Fintype.prod_sum]
  simp only [root_likelihood_sum, Finset.prod_const_one]

theorem locus_likelihood_nonnegative (L : Nat) (t : Genealogy Copy) (x : Survivals t)
    (hx : Admitted t x) (p : Fin L → Pattern t) : 0 ≤ locusLikelihood L t x p := by
  apply Finset.prod_nonneg
  intro j _
  exact root_likelihood_nonnegative t x hx (p j)

def locusKernel (L : Nat) (t : Genealogy Copy) (x : Survivals t) (hx : Admitted t x) :
    PMF (Fin L → Pattern t) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (locusLikelihood L t x p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun p _ => locus_likelihood_nonnegative L t x hx p), locus_likelihood_sum]
    simp)

theorem locus_fourier (L : Nat) (t : Genealogy Copy) (x : Survivals t)
    (charges : Fin L → Copy → Base) :
    (∑ p : Fin L → Pattern t,
      locusLikelihood L t x p * ∏ j, patternCharacter (charges j) t (p j)) =
      ∏ j, if totalCharge (charges j) t = 0 then amplitude (charges j) t x else 0 := by
  simp only [locusLikelihood, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ j : Fin L, ∑ p : Pattern t,
        rootLikelihood t x p * patternCharacter (charges j) t p :=
      (Fintype.prod_sum (fun (j : Fin L) (p : Pattern t) =>
        rootLikelihood t x p * patternCharacter (charges j) t p)).symm
    _ = _ := by simp_rw [root_fourier]

end ResearchCommons.MSCI.JC69Tree
