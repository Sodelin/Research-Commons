/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler, runtime or certificate.

An upstream exact-cover-by-triples to MSSC threshold bridge, composed with
the FULL all-refinements, actual-D_lambda, independent-cell-clade endpoint.
This does not replace that target by a triple-packing surrogate. Classical
X3C hardness and encoded polynomial machine/checker proofs remain separate.
No extra axioms or proof placeholders are intended.
-/
import PolytomyCladeRepresentation

namespace PolytomyReductionModel

noncomputable section

structure TripleCoverInstance (q m : ℕ) extends MSSCInstance (3 * q) m where
  triples : ∀ i, (sets i).card = 3

def ExactTripleCoverDecision {q m : ℕ} (D : TripleCoverInstance q m) : Prop :=
  ∃ J : Finset (Fin m), J.card = q ∧ J.biUnion D.sets = Finset.univ

def coverList {N m : ℕ} (D : MSSCInstance N m) : List (Fin m) → Finset (Fin N)
  | [] => ∅
  | i :: rest => D.sets i ∪ coverList D rest

theorem mem_coverList {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) (x : Fin N) :
    x ∈ coverList D order ↔ ∃ i ∈ order, x ∈ D.sets i := by
  induction order with
  | nil => simp [coverList]
  | cons i rest ih => simp [coverList, ih, or_and_right, exists_or]

theorem coverList_toFinset {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) : coverList D order = order.toFinset.biUnion D.sets := by
  ext x
  simp [mem_coverList]

theorem coverList_append {N m : ℕ} (D : MSSCInstance N m)
    (xs ys : List (Fin m)) :
    coverList D (xs ++ ys) = coverList D xs ∪ coverList D ys := by
  induction xs with
  | nil => simp [coverList]
  | cons i xs ih => simp [coverList, ih, Finset.union_assoc]

theorem coverList_mono {N m : ℕ} (D : MSSCInstance N m)
    {xs ys : List (Fin m)} (h : xs ⊆ ys) : coverList D xs ⊆ coverList D ys := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := (mem_coverList D xs x).mp hx
  exact (mem_coverList D ys x).mpr ⟨i, h hi, hxi⟩

theorem triple_coverList_card_le {q m : ℕ} (D : TripleCoverInstance q m)
    (order : List (Fin m)) :
    (coverList D.toMSSCInstance order).card ≤ 3 * order.length := by
  induction order with
  | nil => simp [coverList]
  | cons i rest ih =>
      have h := Finset.card_union_le (D.sets i) (coverList D.toMSSCInstance rest)
      rw [D.triples i] at h
      simp only [coverList, List.length_cons]
      omega

def prefixMissing {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) (t : ℕ) : ℕ :=
  (Finset.univ \ coverList D (order.take t)).card

theorem prefixMissing_add_covered {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) (t : ℕ) :
    prefixMissing D order t + (coverList D (order.take t)).card = N := by
  simpa [prefixMissing] using Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (coverList D (order.take t)))

theorem triple_prefixMissing_lower {q m : ℕ} (D : TripleCoverInstance q m)
    (order : List (Fin m)) (t : ℕ) :
    3 * q - 3 * t ≤ prefixMissing D.toMSSCInstance order t := by
  have hcap := triple_coverList_card_le D (order.take t)
  have hlen := List.length_take_le t order
  have hsum := prefixMissing_add_covered D.toMSSCInstance order t
  omega

theorem originalContinuation_prefix {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) (covered : Finset (Fin N)) :
    originalContinuation D covered order =
      ∑ t ∈ Finset.range order.length,
        (Finset.univ \ (covered ∪ coverList D (order.take (t + 1)))).card := by
  induction order generalizing covered with
  | nil => simp [originalContinuation]
  | cons i rest ih =>
      rw [originalContinuation, ih]
      simp only [List.length_cons, Finset.sum_range_succ', List.take_succ_cons,
        List.take_zero, coverList, Finset.union_empty, Finset.union_assoc]
      omega

theorem msscCost_prefix {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) :
    msscCost D order = N +
      ∑ t ∈ Finset.range order.length, prefixMissing D order (t + 1) := by
  have h := originalContinuation_firstCover D (∅ : Finset (Fin N)) order
  have hc : originalContinuation D ∅ order + N = msscCost D order := by
    rw [h]
    simp [msscCost, firstCover, Finset.sum_add_distrib]
  rw [originalContinuation_prefix] at hc
  simpa [prefixMissing, Nat.add_comm] using hc.symm

/-- A polynomially computable integer threshold. For q <= m this equals
    3*q*(q+1)/2; the finite sum avoids division in the proof interface. -/
def tripleThreshold (q m : ℕ) : ℕ :=
  3 * q + ∑ t ∈ Finset.range m, (3 * q - 3 * (t + 1))

theorem tripleThreshold_lower {q m : ℕ} (D : TripleCoverInstance q m)
    (order : List (Fin m)) (hlen : order.length = m) :
    tripleThreshold q m ≤ msscCost D.toMSSCInstance order := by
  rw [msscCost_prefix, hlen]
  exact Nat.add_le_add_left (Finset.sum_le_sum fun t ht =>
    triple_prefixMissing_lower D order (t + 1)) (3 * q)

theorem coverList_all {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m))
    (ho : order.Perm (Finset.univ : Finset (Fin m)).toList) :
    coverList D order = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := D.covers x
  exact (mem_coverList D order x).mpr ⟨i, ho.mem_iff.mpr (by simp), hi⟩

theorem triple_q_le_m {q m : ℕ} (D : TripleCoverInstance q m) : q ≤ m := by
  let order := (Finset.univ : Finset (Fin m)).toList
  have he := coverList_all D.toMSSCInstance order (List.Perm.refl _)
  have hc := triple_coverList_card_le D order
  rw [he] at hc
  simp [order] at hc
  omega

theorem tripleThreshold_bounds {q m : ℕ} (D : TripleCoverInstance q m) :
    3 * q ≤ tripleThreshold q m ∧ tripleThreshold q m ≤ m * (3 * q) := by
  constructor
  · simp [tripleThreshold]
  · let order := (Finset.univ : Finset (Fin m)).toList
    have hl := tripleThreshold_lower D order (by simp [order])
    have hu := (msscCost_bounds D.toMSSCInstance order (List.Perm.refl _)).2
    exact hl.trans hu

/-- Equality in the universal capacity bound forces the first q sets to
    cover all 3q elements. No restriction on the candidate ordering is added. -/
theorem low_cost_forces_prefix_cover {q m : ℕ} (D : TripleCoverInstance q m)
    (hq : 0 < q) (order : List (Fin m)) (hlen : order.length = m)
    (hcost : msscCost D.toMSSCInstance order ≤ tripleThreshold q m) :
    coverList D.toMSSCInstance (order.take q) = Finset.univ := by
  have hqm := triple_q_le_m D
  have hle : ∀ t ∈ Finset.range m,
      3 * q - 3 * (t + 1) ≤ prefixMissing D.toMSSCInstance order (t + 1) :=
    fun t ht => triple_prefixMissing_lower D order (t + 1)
  have hsumle := Finset.sum_le_sum hle
  rw [msscCost_prefix, hlen] at hcost
  unfold tripleThreshold at hcost
  have heq : (∑ t ∈ Finset.range m, (3 * q - 3 * (t + 1))) =
      ∑ t ∈ Finset.range m, prefixMissing D.toMSSCInstance order (t + 1) := by
    omega
  have hat := (Finset.sum_eq_sum_iff_of_le hle).mp heq (q - 1)
    (Finset.mem_range.mpr (by omega))
  have hpred : q - 1 + 1 = q := by omega
  rw [hpred, Nat.sub_self] at hat
  have hempty : Finset.univ \ coverList D.toMSSCInstance (order.take q) = ∅ :=
    Finset.card_eq_zero.mp hat.symm
  apply Finset.eq_univ_of_forall
  intro x
  by_contra hx
  have hm : x ∈ Finset.univ \ coverList D.toMSSCInstance (order.take q) := by
    simp [hx]
  rw [hempty] at hm
  simp at hm

/-- A covering q-prefix must attain every capacity bound before q and have
    no uncovered elements thereafter. This proves sufficiency, not only necessity. -/
theorem prefixMissing_exact_of_prefix_cover {q m : ℕ}
    (D : TripleCoverInstance q m) (order : List (Fin m))
    (hcover : coverList D.toMSSCInstance (order.take q) = Finset.univ)
    (t : ℕ) : prefixMissing D.toMSSCInstance order t = 3 * q - 3 * t := by
  by_cases hqt : q ≤ t
  · have hsub : order.take q ⊆ order.take t := by
      have he : (order.take t).take q = order.take q := by
        rw [List.take_take, Nat.min_eq_left hqt]
      rw [← he]
      exact List.take_subset q (order.take t)
    have hs := coverList_mono D.toMSSCInstance hsub
    rw [hcover] at hs
    have he : coverList D.toMSSCInstance (order.take t) = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) hs
    simp only [prefixMissing, he, Finset.sdiff_self, Finset.card_empty]
    omega
  · have htq : t ≤ q := by omega
    have he : order.take q = order.take t ++ (order.drop t).take (q - t) := by
      conv_lhs => rw [← Nat.add_sub_of_le htq]
      exact List.take_add
    have hcap := triple_coverList_card_le D ((order.drop t).take (q - t))
    have hlen := List.length_take_le (q - t) (order.drop t)
    have hunion := Finset.card_union_le
      (coverList D.toMSSCInstance (order.take t))
      (coverList D.toMSSCInstance ((order.drop t).take (q - t)))
    have huniv : coverList D.toMSSCInstance (order.take t) ∪
        coverList D.toMSSCInstance ((order.drop t).take (q - t)) = Finset.univ := by
      rw [← coverList_append, ← he]
      exact hcover
    rw [huniv] at hunion
    simp only [Finset.card_univ, Fintype.card_fin] at hunion
    have hsum := prefixMissing_add_covered D.toMSSCInstance order t
    have hlower := triple_prefixMissing_lower D order t
    omega

theorem prefix_cover_attains_threshold {q m : ℕ} (D : TripleCoverInstance q m)
    (order : List (Fin m)) (hlen : order.length = m)
    (hcover : coverList D.toMSSCInstance (order.take q) = Finset.univ) :
    msscCost D.toMSSCInstance order = tripleThreshold q m := by
  rw [msscCost_prefix, hlen]
  unfold tripleThreshold
  congr 1
  exact Finset.sum_congr rfl (fun t ht =>
    prefixMissing_exact_of_prefix_cover D order hcover (t + 1))

def chosenFirstOrder {m : ℕ} (J : Finset (Fin m)) : List (Fin m) :=
  J.toList ++ (Finset.univ \ J).toList

theorem chosenFirstOrder_perm {m : ℕ} (J : Finset (Fin m)) :
    (chosenFirstOrder J).Perm (Finset.univ : Finset (Fin m)).toList := by
  have hn : (chosenFirstOrder J).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨J.nodup_toList, (Finset.univ \ J).nodup_toList, ?_⟩
    intro i hi j hj heq
    subst j
    have hi' : i ∈ J := by simpa using hi
    have hj' : i ∉ J := by simpa using hj
    exact hj' hi'
  apply List.perm_of_nodup_nodup_toFinset_eq hn Finset.univ.nodup_toList
  ext i
  simp [chosenFirstOrder]

theorem chosenFirstOrder_take {q m : ℕ} (J : Finset (Fin m)) (hJ : J.card = q) :
    (chosenFirstOrder J).take q = J.toList := by
  have hlen : J.toList.length = q := by simpa using hJ
  rw [chosenFirstOrder, ← hlen, List.take_append_length]

/-- Exact-cover-by-triples is reduced to the genuine first-cover objective. -/
theorem exactTripleCover_iff_mssc {q m : ℕ} (D : TripleCoverInstance q m)
    (hq : 0 < q) :
    ExactTripleCoverDecision D ↔ MSSCDecision D.toMSSCInstance (tripleThreshold q m) := by
  constructor
  · rintro ⟨J, hcard, hcover⟩
    let order := chosenFirstOrder J
    have ho := chosenFirstOrder_perm J
    have hlen : order.length = m := by simpa [order] using ho.length_eq
    have hc : coverList D.toMSSCInstance (order.take q) = Finset.univ := by
      rw [chosenFirstOrder_take J hcard, coverList_toFinset]
      simpa using hcover
    exact ⟨order, ho, (prefix_cover_attains_threshold D order hlen hc).le⟩
  · rintro ⟨order, ho, hcost⟩
    have hlen : order.length = m := by simpa using ho.length_eq
    have hcover := low_cost_forces_prefix_cover D hq order hlen hcost
    have hn : order.Nodup := ho.nodup_iff.mpr Finset.univ.nodup_toList
    have htake : (order.take q).Nodup := List.Pairwise.take hn
    refine ⟨(order.take q).toFinset, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup htake, List.length_take_of_le]
      simpa [hlen] using triple_q_le_m D
    · rw [← coverList_toFinset]
      exact hcover

/-- FULL composed finite result: arbitrary standard cell-clade-preserving
    binary refinements with compatible labels and actual D_lambda. The target
    has NOT been restricted to caterpillars or exact-cover packing witnesses. -/
theorem full_exactTripleCover_carta_reduction {q m : ℕ}
    (D : TripleCoverInstance q m) (lambda : ℝ) (hq : 0 < q) (hm : 2 ≤ m) :
    ExactTripleCoverDecision D ↔
      StandardCanonicalCartaDecision D.toMSSCInstance lambda (tripleThreshold q m) := by
  have hb := tripleThreshold_bounds D
  exact (exactTripleCover_iff_mssc D hq).trans
    (full_standard_canonical_carta_reduction D.toMSSCInstance lambda
      (tripleThreshold q m) (by omega) hm hb.1 hb.2)

/- Still not a formal NP-hardness certificate: no encoded X3C-hardness
theorem, polynomial machine constructor, target checker, or elaboration is
claimed. The already complete hand all-refinement theorem is unchanged. -/

end
end PolytomyReductionModel
