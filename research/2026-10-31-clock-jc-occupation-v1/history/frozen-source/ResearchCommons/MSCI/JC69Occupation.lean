import ResearchCommons.MSCI.JC69Tree
import G2SourceGraftDecoration
import G2ActualDecorationFold

/-! Actual-tree charge exposure and actual-merge conservation.
Contributor: dot (OpenAI), 30 October 2026. UNCOMPILED development.
Separate from frozen recurrence inputs. No weighted source-law premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69Occupation
open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ChronologicalDecoration
open GProgram.G2.SourceGraftDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Tree
open scoped Classical BigOperators
variable {Copy V E : Type*} [Fintype Copy] [DecidableEq Copy]

def charged (q : Copy → Base) (t : Genealogy Copy) : ℝ :=
  if totalCharge q t = 0 then 0 else 1

/-- Exposure of completed edges plus the pending root branch up to T.
The single pending coefficient is the ACTUAL descendant charge. -/
def potential (q : Copy → Base) (leafAge : Copy → ℝ) :
    (t : Genealogy Copy) → Decoration t → ℝ → ℝ
  | .leaf x, _, T => charged q (.leaf x) * (T-leafAge x)
  | .graft a b, d, T =>
      potential q leafAge a d.2.1 d.1 + potential q leafAge b d.2.2 d.1 +
        charged q (.graft a b) * (T-d.1)

lemma potential_time_increment (q : Copy → Base) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (d : Decoration t) (T U : ℝ) :
    potential q leafAge t d U = potential q leafAge t d T + charged q t*(U-T) := by
  cases t <;> simp only [potential] <;> ring

lemma potential_graft_at_time (q : Copy → Base) (leafAge : Copy → ℝ)
    (a b : Genealogy Copy) (da : Decoration a) (db : Decoration b) (T : ℝ) :
    potential q leafAge (.graft a b) (T,da,db) T =
      potential q leafAge a da T + potential q leafAge b db T := by
  simp [potential]

lemma pending_branch_factor (q : Copy → Base) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (d : Decoration t) (T : ℝ) :
    (if totalCharge q t = 0 then 1 else Real.exp (-((4/3:ℝ)*(T-rootAge leafAge t d)))) *
      Real.exp (-((4/3:ℝ)*potential q leafAge t d (rootAge leafAge t d))) =
    Real.exp (-((4/3:ℝ)*potential q leafAge t d T)) := by
  rw [potential_time_increment q leafAge t d (rootAge leafAge t d) T]
  by_cases h : totalCharge q t = 0
  · simp [charged,h]
  · simp only [h,if_false,charged,one_mul]
    rw [← Real.exp_add]
    congr 1
    ring

/-- The EXISTING tree Fourier amplitude is exactly the actual decoded
charge exposure, not a newly postulated source likelihood. -/
theorem amplitude_eq_exposure (q : Copy → Base) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) : ∀ d : Decoration t,
    amplitude q t (clockSurvivals leafAge t d) =
      Real.exp (-((4/3:ℝ)*potential q leafAge t d (rootAge leafAge t d))) := by
  induction t with
  | leaf x =>
      intro d
      simp [amplitude,potential,rootAge]
  | graft a b ha hb =>
      intro d
      simp only [amplitude,clockSurvivals]
      rw [ha,hb,pending_branch_factor,pending_branch_factor,← Real.exp_add]
      congr 1
      simp only [potential,rootAge,sub_self,mul_zero,add_zero]
      ring

/-- Actual root Fourier formula, with no stem above the sample MRCA. -/
theorem root_fourier_exposure (q : Copy → Base) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (d : Decoration t) :
    (∑ p : Pattern t, rootLikelihood t (clockSurvivals leafAge t d) p *
      patternCharacter q t p) =
      if totalCharge q t = 0 then
        Real.exp (-((4/3:ℝ)*potential q leafAge t d (rootAge leafAge t d))) else 0 := by
  rw [root_fourier,amplitude_eq_exposure]

/-- Pair-matrix equality on an old subtree preserves its literal decoder.
No chosen replacement decoration or chronology assumption is required. -/
lemma decode_congr_on_leaves (t : Genealogy Copy) (M M' : Copy → Copy → ℝ)
    (h : ∀ x ∈ t.leaves, ∀ y ∈ t.leaves, M x y = M' x y) :
    decode M t = decode M' t := by
  induction t with
  | leaf x => rfl
  | graft a b ha hb =>
    have hr := h (witness a) (Finset.mem_union.mpr (Or.inl (witness_mem a)))
      (witness b) (Finset.mem_union.mpr (Or.inr (witness_mem b)))
    have hA := ha (fun x hx y hy => h x (Finset.mem_union.mpr (Or.inl hx))
      y (Finset.mem_union.mpr (Or.inl hy)))
    have hB := hb (fun x hx y hy => h x (Finset.mem_union.mpr (Or.inr hx))
      y (Finset.mem_union.mpr (Or.inr hy)))
    simp only [decode,hr,hA,hB]

lemma decode_old_live_after_merge (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) (M : Copy → Copy → ℝ) (T : ℝ)
    (l : Copy) (hl : l ∈ s.live) :
    decode (mergeAgeMatrix s a b T M) (s.genealogy l) = decode M (s.genealogy l) := by
  apply decode_congr_on_leaves
  intro x hx y hy
  exact same_operand_keeps_age s hm.different
    ((hs.leaf_fiber l hl x).mp hx) ((hs.leaf_fiber l hl y).mp hy)

/-- The new actual graft decodes to the real merger date and the two
UNCHANGED old operand decorations. -/
lemma decode_actual_graft (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) (M : Copy → Copy → ℝ) (T : ℝ) :
    decode (mergeAgeMatrix s a b T M) (.graft (s.genealogy a) (s.genealogy b)) =
      (T,decode M (s.genealogy a),decode M (s.genealogy b)) := by
  have ha := (hs.leaf_fiber a hm.first_live (witness (s.genealogy a))).mp
    (witness_mem (s.genealogy a))
  have hb := (hs.leaf_fiber b hm.second_live (witness (s.genealogy b))).mp
    (witness_mem (s.genealogy b))
  simp only [decode]
  rw [decode_old_live_after_merge s hs hm M T a hm.first_live,
    decode_old_live_after_merge s hs hm M T b hm.second_live]
  simp [mergeAgeMatrix,ha,hb]

def forestPotential (q : Copy → Base) (leafAge : Copy → ℝ)
    (s : State V E Copy) (M : Copy → Copy → ℝ) (T : ℝ) : ℝ :=
  ∑ l ∈ s.live, potential q leafAge (s.genealogy l) (decode M (s.genealogy l)) T

/-- Deterministic exact increment between events, before any integration. -/
theorem forest_potential_time_increment (q : Copy → Base) (leafAge : Copy → ℝ)
    (s : State V E Copy) (M : Copy → Copy → ℝ) (T U : ℝ) :
    forestPotential q leafAge s M U = forestPotential q leafAge s M T +
      (∑ l ∈ s.live, charged q (s.genealogy l)) * (U-T) := by
  simp only [forestPotential,potential_time_increment,Finset.sum_add_distrib,Finset.sum_mul]

/-- The pending-branch coefficient is the original current-block charge
count used by the already proved killed-rate inequalities (one site). -/
theorem actual_charge_coefficient (q : Copy → Base) (s : State V E Copy) (hs : Valid s) :
    (∑ l ∈ s.live, charged q (s.genealogy l)) =
      (activeChargeCount s (fun x (_ : Unit) => q x) : ℝ) := by
  unfold activeChargeCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have ht := totalCharge_eq_original_leaves q (s.genealogy l) (hs.wellLabelled l hl)
  simp [charged,rootChargeCount,currentCharge,nonzeroCharge,ht]

theorem actual_forest_occupation_increment (q : Copy → Base) (leafAge : Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) (M : Copy → Copy → ℝ) (T U : ℝ) :
    forestPotential q leafAge s M U = forestPotential q leafAge s M T +
      (activeChargeCount s (fun x (_ : Unit) => q x) : ℝ)*(U-T) := by
  rw [forest_potential_time_increment,actual_charge_coefficient q s hs]

/-- Actual legal merger conserves accumulated Fourier exposure at its date.
Cancellation of the new root charge does not erase either completed edge. -/
theorem actual_merge_potential_conserved (q : Copy → Base) (leafAge : Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) {a b : Copy} (hm : LegalMerge s a b)
    (M : Copy → Copy → ℝ) (T : ℝ) :
    forestPotential q leafAge (merge s a b) (mergeAgeMatrix s a b T M) T =
      forestPotential q leafAge s M T := by
  have ha : a ∈ s.live.erase b := Finset.mem_erase.mpr ⟨hm.different,hm.first_live⟩
  have hterm : ∀ l ∈ s.live.erase b,
      potential q leafAge ((merge s a b).genealogy l)
        (decode (mergeAgeMatrix s a b T M) ((merge s a b).genealogy l)) T =
      potential q leafAge (s.genealogy l) (decode M (s.genealogy l)) T +
        if l = a then potential q leafAge (s.genealogy b) (decode M (s.genealogy b)) T else 0 := by
    intro l hl
    by_cases he : l = a
    · subst l
      simp only [merge,if_pos rfl]
      rw [decode_actual_graft s hs hm M T,potential_graft_at_time]
    · simp only [merge,if_neg he,add_zero]
      rw [decode_old_live_after_merge s hs hm M T l (Finset.mem_erase.mp hl).2]
  change (∑ l ∈ s.live.erase b, _) = _
  rw [Finset.sum_congr rfl hterm,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',ha,if_true]
  exact Finset.sum_erase_add _ _ hm.second_live

/-- A routing boundary changes only source bookkeeping, never exposure. -/
theorem potential_transport (q : Copy → Base) (leafAge : Copy → ℝ)
    (s : State V E Copy) (place : Copy → Location V E) (event : SourceEvent V E Copy)
    (M : Copy → Copy → ℝ) (T : ℝ) :
    forestPotential q leafAge (transport s place event) M T =
      forestPotential q leafAge s M T := rfl

/-- Globally balanced characters have no pending branch above the final
sample MRCA. All original labelled copies, not a smaller panel, are used. -/
theorem balanced_complete_potential (q : Copy → Base) (leafAge : Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) (hcard : s.live.card ≤ 1)
    (l : Copy) (hl : l ∈ s.live) (hbal : ∑ x : Copy, q x = 0)
    (M : Copy → Copy → ℝ) (T : ℝ) :
    forestPotential q leafAge s M T =
      potential q leafAge (s.genealogy l) (decode M (s.genealogy l))
        (rootAge leafAge (s.genealogy l) (decode M (s.genealogy l))) := by
  have hq : totalCharge q (s.genealogy l) = 0 := by
    rw [totalCharge_eq_original_leaves q (s.genealogy l) (hs.wellLabelled l hl),
      actual_single_root_covers_original_copies s hs hcard l hl]
    exact hbal
  have hsum : forestPotential q leafAge s M T =
      potential q leafAge (s.genealogy l) (decode M (s.genealogy l)) T := by
    unfold forestPotential
    apply Finset.sum_eq_single l
    · intro x hx hxl
      exact False.elim (hxl (Finset.card_le_one.mp hcard x hx l hl))
    · intro hn
      exact False.elim (hn hl)
  rw [hsum,potential_time_increment q leafAge (s.genealogy l) _
    (rootAge leafAge (s.genealogy l) (decode M (s.genealogy l))) T]
  simp [charged,hq]

/-- The original shared-tree locus Fourier coefficient, not a new scalar
observable, is exactly the completed forest occupation weight. Completion
and balance are explicit here; chronological source support remains separate. -/
theorem balanced_complete_locus_fourier (L : ℕ) (q : Fin L → Copy → Base)
    (leafAge : Copy → ℝ) (s : State V E Copy) (hs : Valid s)
    (hcard : s.live.card ≤ 1) (l : Copy) (hl : l ∈ s.live)
    (hbal : ∀ j, ∑ x : Copy, q j x = 0) (M : Copy → Copy → ℝ) (T : ℝ) :
    (∑ p : Fin L → Pattern (s.genealogy l),
      locusLikelihood L (s.genealogy l)
        (clockSurvivals leafAge (s.genealogy l) (decode M (s.genealogy l))) p *
      ∏ j, patternCharacter (q j) (s.genealogy l) (p j)) =
    Real.exp (-((4/3:ℝ) * ∑ j, forestPotential (q j) leafAge s M T)) := by
  rw [locus_fourier]
  have hq : ∀ j, totalCharge (q j) (s.genealogy l) = 0 := by
    intro j
    rw [totalCharge_eq_original_leaves (q j) (s.genealogy l) (hs.wellLabelled l hl),
      actual_single_root_covers_original_copies s hs hcard l hl]
    exact hbal j
  simp_rw [hq,if_true,amplitude_eq_exposure,
    ← balanced_complete_potential _ leafAge s hs hcard l hl (hbal _) M T]
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_neg_distrib]

section Coded
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open GProgram.SourceForestKingmanPopulationProjection
variable {X : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

lemma snapshot_potential (q : Copy → Base) (leafAge : Copy → ℝ)
    (root : V) (s : State V E Copy) (hs : Valid s) (M : Copy → Copy → ℝ) (T : ℝ) :
    forestPotential q leafAge (decodeSnapshot root (encodeSnapshot s hs)) M T =
      forestPotential q leafAge s M T := by
  unfold forestPotential
  change (∑ l ∈ s.live, _) = _
  apply Finset.sum_congr rfl
  intro l hl
  rw [decode_encode_live_genealogy root s hs hl]

/-- Exact original coded merger and its inherited age-update operation.
No legal-merger, source-kernel or decoration identity is assumed externally. -/
theorem actual_coded_merger_potential (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (leafAge : Copy → ℝ) (s : Code N sample) (p : Choice N s)
    (M : Copy → Copy → ℝ) (T : ℝ) :
    forestPotential q leafAge (state (stepDestination N s (some p)))
      (codedAgeUpdate N s (stepDestination N s (some p)) T M) T =
      forestPotential q leafAge (state s) M T := by
  have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  rw [coded_update_is_actual_graft]
  change forestPotential q leafAge
    (decodeSnapshot N.root (encodeSnapshot (merge (state s) p.2.val.1 p.2.val.2)
      (merge_valid (state s) s.property.forest hm))) _ T = _
  rw [snapshot_potential]
  exact actual_merge_potential_conserved q leafAge (state s) s.property.forest hm M T
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualDecorationFold
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceMergerClockCatalogue

/-- Exact current-block single-site killing coefficient on the old source. -/
def codeCharge (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (s : Code N sample) : ℝ :=
  activeChargeCount (state s) (fun x (_ : Unit) => q x)

/-- Cost along the ORIGINAL literal clock compiler, including its total
failed-prefix convention. Only successful actual source support is later
interpreted as a complete epoch. No independent path is generated. -/
def literalOccupation (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) : (n : ℕ) → ℝ → (s : Code N sample) → (Choice N s → ℝ) → ℝ
  | 0,t,s,_ => codeCharge N q s*t
  | n+1,t,s,c =>
      if ∀ p : Choice N s, t < c p then codeCharge N q s*t else
      match selectedWinner c with
      | none => codeCharge N q s*t
      | some p => if c p ≤ t then
          codeCharge N q s*c p +
            literalOccupation N q n (t-c p) (stepDestination N s (some p))
              (fun u => c (destinationClockEmbedding N s p u).val-c p)
        else codeCharge N q s*t

/-- The actual chronological matrix fold has exactly the charge occupation
cost of the SAME original clocks. This discharges the deterministic
Fourier/path interface; no desired weighted expectation is a premise. -/
theorem actual_literal_occupation_identity (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (leafAge : Copy → ℝ) (n : ℕ) (s : Code N sample)
    (t offset : ℝ) (c : Choice N s → ℝ) (M : Copy → Copy → ℝ) :
    forestPotential q leafAge
      (state (traceEndpoint N n s (literalMarkedTrace N n t s c).2))
      (foldMatrix N n s offset M (literalMarkedTrace N n t s c).2) (offset+t) =
    forestPotential q leafAge (state s) M offset + literalOccupation N q n t s c := by
  induction n generalizing s t offset M with
  | zero =>
      simpa [literalMarkedTrace,traceEndpoint,foldMatrix,literalOccupation,codeCharge] using
        actual_forest_occupation_increment q leafAge (state s) s.property.forest M offset (offset+t)
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp only [literalMarkedTrace,literalOccupation,if_pos hstop,fold_empty,empty_trace_endpoint]
        simpa [codeCharge] using
          actual_forest_occupation_increment q leafAge (state s) s.property.forest M offset (offset+t)
      · simp only [literalMarkedTrace,literalOccupation,if_neg hstop]
        cases hw : selectedWinner c with
        | none =>
            simp only [fold_empty,empty_trace_endpoint]
            simpa [codeCharge] using
              actual_forest_occupation_increment q leafAge (state s) s.property.forest M offset (offset+t)
        | some p =>
            by_cases hp : c p ≤ t
            · simp only [if_pos hp,fold_prepend,prepend_trace_endpoint]
              have htime : offset+t = (offset+c p)+(t-c p) := by ring
              rw [htime,ih,actual_coded_merger_potential]
              rw [actual_forest_occupation_increment q leafAge (state s) s.property.forest M offset (offset+c p)]
              simp only [codeCharge,add_sub_cancel_left]
              ring
            · simp only [if_neg hp,fold_empty,empty_trace_endpoint]
              simpa [codeCharge] using
                actual_forest_occupation_increment q leafAge (state s) s.property.forest M offset (offset+t)

/-- All finite site columns share the SAME source clock record; sum exposures
before exponentiation/integration, rather than resampling the source per site. -/
theorem actual_literal_locus_occupation_identity {Site : Type*} [Fintype Site]
    (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Site → Base) (leafAge : Copy → ℝ) (n : ℕ) (s : Code N sample)
    (t offset : ℝ) (c : Choice N s → ℝ) (M : Copy → Copy → ℝ) :
    (∑ j : Site, forestPotential (fun x => q x j) leafAge
      (state (traceEndpoint N n s (literalMarkedTrace N n t s c).2))
      (foldMatrix N n s offset M (literalMarkedTrace N n t s c).2) (offset+t)) =
    (∑ j : Site, forestPotential (fun x => q x j) leafAge (state s) M offset) +
      ∑ j : Site, literalOccupation N (fun x => q x j) n t s c := by
  simp_rw [actual_literal_occupation_identity]
  exact Finset.sum_add_distrib

end Coded

#print axioms amplitude_eq_exposure
#print axioms root_fourier_exposure
#print axioms decode_actual_graft
#print axioms forest_potential_time_increment
#print axioms balanced_complete_potential
#print axioms balanced_complete_locus_fourier
#print axioms actual_charge_coefficient
#print axioms actual_forest_occupation_increment
#print axioms actual_merge_potential_conserved
#print axioms actual_coded_merger_potential
#print axioms actual_literal_occupation_identity
#print axioms actual_literal_locus_occupation_identity
end ResearchCommons.MSCI.JC69Occupation
