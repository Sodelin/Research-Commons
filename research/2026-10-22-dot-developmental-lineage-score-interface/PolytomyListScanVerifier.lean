/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler, runtime or machine certificate.

An explicit supplied-list implementation of the independent marked-star
target verifier. Algorithm definitions below use structural recursion,
list membership/deduplication and natural arithmetic. Finsets, universal
enumeration and real scores occur only in the specification/proofs.
The final theorem retains the whole actual-D_lambda encoded reduction.
This is not yet a TM2 realization or a formal running-time theorem.
-/
import PolytomyOutputSizeBound

namespace PolytomyReductionModel
universe u v

def scanLeaves {A : Type u} : BTree A → List A
  | .leaf a => [a]
  | .node l r => scanLeaves l ++ scanLeaves r

theorem scanLeaves_eq {A : Type u} (T : BTree A) : scanLeaves T = leaves T := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr => simp only [scanLeaves, leaves, ihl, ihr]

def scanSubset {A : Type u} [DecidableEq A] (xs ys : List A) : Bool :=
  xs.all (fun x => decide (x ∈ ys))

def scanSetEq {A : Type u} [DecidableEq A] (xs ys : List A) : Bool :=
  scanSubset xs ys && scanSubset ys xs

theorem scanSubset_spec {A : Type u} [DecidableEq A] (xs ys : List A) :
    scanSubset xs ys = true ↔ xs.toFinset ⊆ ys.toFinset := by
  simp only [scanSubset, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h x hx
    exact List.mem_toFinset.mpr (h x (List.mem_toFinset.mp hx))
  · intro h x hx
    exact List.mem_toFinset.mp (h (List.mem_toFinset.mpr hx))

theorem scanSetEq_spec {A : Type u} [DecidableEq A] (xs ys : List A) :
    scanSetEq xs ys = true ↔ xs.toFinset = ys.toFinset := by
  rw [scanSetEq, Bool.and_eq_true, scanSubset_spec, scanSubset_spec]
  exact ⟨fun h => Finset.Subset.antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

def scanDistinctCount {A : Type u} [DecidableEq A] (xs : List A) : ℕ :=
  xs.dedup.length

theorem scanDistinctCount_spec {A : Type u} [DecidableEq A] (xs : List A) :
    scanDistinctCount xs = xs.toFinset.card := (List.card_toFinset).symm

def scanClades {A : Type u} : BTree A → List (List A)
  | .leaf a => [[a]]
  | .node l r => (scanLeaves l ++ scanLeaves r) :: (scanClades l ++ scanClades r)

theorem scanLeaves_cellSet {A : Type u} [DecidableEq A] (T : BTree A) :
    (scanLeaves T).toFinset = cellSet T := by
  simp only [scanLeaves_eq, cellSet, observed_eq_leaves_image, List.map_id]

theorem scanClades_spec {A : Type u} [DecidableEq A] (T : BTree A) (C : Finset A) :
    (∃ xs ∈ scanClades T, xs.toFinset = C) ↔ CellClade C T := by
  induction T with
  | leaf a =>
      constructor
      · rintro ⟨xs, hxs, he⟩
        have hx : xs = [a] := by simpa [scanClades] using hxs
        subst xs
        rw [← he]
        simpa [cellSet, observed] using (CellClade.root (BTree.leaf a))
      · intro h
        cases h with
        | root => exact ⟨[a], by simp [scanClades], by simp [cellSet, observed]⟩
  | node l r ihl ihr =>
      rw [cellClade_node_iff]
      constructor
      · rintro ⟨xs, hxs, he⟩
        have hm : xs = scanLeaves l ++ scanLeaves r ∨
            xs ∈ scanClades l ∨ xs ∈ scanClades r := by
          simpa only [scanClades, List.mem_cons, List.mem_append] using hxs
        rcases hm with hx | hx | hx
        · left
          rw [← he, hx]
          exact scanLeaves_cellSet (.node l r)
        · exact Or.inr (Or.inl (ihl.mp ⟨xs, hx, he⟩))
        · exact Or.inr (Or.inr (ihr.mp ⟨xs, hx, he⟩))
      · rintro (he | hl | hr)
        · refine ⟨scanLeaves l ++ scanLeaves r, by simp [scanClades], ?_⟩
          rw [he]
          exact scanLeaves_cellSet (.node l r)
        · obtain ⟨xs, hx, he⟩ := ihl.mpr hl
          exact ⟨xs, by simp [scanClades, hx], he⟩
        · obtain ⟨xs, hx, he⟩ := ihr.mpr hr
          exact ⟨xs, by simp [scanClades, hx], he⟩

def scanRefines {A : Type u} [DecidableEq A] (R T : BTree A) : Bool :=
  (scanClades R).all (fun xs => (scanClades T).any (fun ys => scanSetEq xs ys))

theorem scanRefines_spec {A : Type u} [DecidableEq A] (R T : BTree A) :
    scanRefines R T = true ↔ CellRefines R T := by
  simp only [scanRefines, List.all_eq_true, List.any_eq_true, scanSetEq_spec]
  constructor
  · intro h C hC
    obtain ⟨xs, hx, he⟩ := (scanClades_spec R C).mpr hC
    obtain ⟨ys, hy, hxy⟩ := h xs hx
    exact (scanClades_spec T C).mp ⟨ys, hy, hxy.symm.trans he⟩
  · intro h xs hx
    have hc := (scanClades_spec R xs.toFinset).mp ⟨xs, hx, rfl⟩
    obtain ⟨ys, hy, he⟩ := (scanClades_spec T xs.toFinset).mpr (h _ hc)
    exact ⟨ys, hy, he.symm⟩

def scanTypeCount {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (T : BTree A) : ℕ :=
  scanDistinctCount ((scanLeaves T).map tip)

theorem scanTypeCount_spec {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (T : BTree A) :
    scanTypeCount tip T = (observed tip T).card := by
  simp only [scanTypeCount, scanDistinctCount_spec, scanLeaves_eq, observed_eq_leaves_image]

def scanMixed {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) : BTree A → Bool
  | .leaf _ => true
  | .node l r => decide (2 ≤ scanTypeCount tip (.node l r)) &&
      scanMixed tip l && scanMixed tip r

theorem scanMixed_spec {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (T : BTree A) :
    scanMixed tip T = true ↔ AllInternalMixed tip T := by
  induction T with
  | leaf a => simp [scanMixed, AllInternalMixed]
  | node l r ihl ihr =>
      simp only [scanMixed, Bool.and_eq_true, decide_eq_true_eq,
        scanTypeCount_spec, ihl, ihr, AllInternalMixed]
      tauto

def scanStarScore {A : Type u} {S : Type v} [DecidableEq S]
    (s : ℕ) (tip : A → S) : BTree A → ℕ
  | .leaf _ => 0
  | .node l r => scanStarScore s tip l + scanStarScore s tip r +
      (s - scanTypeCount tip (.node l r))

theorem scanStarScore_spec {A : Type u} {S : Type v} [Fintype S] [DecidableEq S]
    (tip : A → S) (T : BTree A) :
    scanStarScore (Fintype.card S) tip T = starScore Finset.univ tip T := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr =>
      simp only [scanStarScore, ihl, ihr, starScore, scanTypeCount_spec]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp only [Finset.card_univ, observed]

def scanRowLeaves {N m : ℕ} (R : RawTargetRows N m) : List (Cell N m) :=
  R.rows.flatMap scanLeaves

theorem scanRowLeaves_eq {N m : ℕ} (R : RawTargetRows N m) :
    scanRowLeaves R = rawTargetLeaves R := by
  simp only [scanRowLeaves, rawTargetLeaves, scanLeaves_eq]

def scanMarkers {N m : ℕ} (T : BTree (Cell N m)) : Bool :=
  decide ((Sum.inr (Sum.inr (0 : Fin 2)) : Terminal N m) ∈
    (scanLeaves T).map Prod.snd) &&
  decide ((Sum.inr (Sum.inr (1 : Fin 2)) : Terminal N m) ∈
    (scanLeaves T).map Prod.snd)

theorem scanMarkers_spec {N m : ℕ} (T : BTree (Cell N m)) :
    scanMarkers T = true ↔ markers N m ⊆ observed Prod.snd T := by
  simp only [scanMarkers, Bool.and_eq_true, decide_eq_true_eq, scanLeaves_eq]
  constructor
  · rintro ⟨h0, h1⟩ s hs
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
    fin_cases k
    · simpa [observed_eq_leaves_image] using h0
    · simpa [observed_eq_leaves_image] using h1
  · intro h
    constructor
    · have hx := h (show (Sum.inr (Sum.inr (0 : Fin 2)) : Terminal N m) ∈ markers N m by
        simp [markers])
      simpa [observed_eq_leaves_image] using hx
    · have hx := h (show (Sum.inr (Sum.inr (1 : Fin 2)) : Terminal N m) ∈ markers N m by
        simp [markers])
      simpa [observed_eq_leaves_image] using hx

def scanRawTargetValid {N m : ℕ} (R : RawTargetRows N m) : Bool :=
  decide (0 < N) && decide (2 ≤ m) && decide (R.rows.length = m + 1) &&
  decide ((scanRowLeaves R).Nodup) && R.rows.all (scanMixed Prod.snd) &&
  R.rows.all scanMarkers &&
  decide (scanDistinctCount ((scanRowLeaves R).map (fun a => terminalCode N m a.2)) =
    N + m * N + 3)

theorem scanRawTargetValid_spec {N m : ℕ} (R : RawTargetRows N m) :
    scanRawTargetValid R = true ↔ RawTargetRowsValid R := by
  rw [← rawTargetRowsValidBool_spec]
  simp only [scanRawTargetValid, rawTargetRowsValidBool, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, scanMixed_spec, checkTreeMixed_spec, scanMarkers_spec,
    scanRowLeaves_eq, scanDistinctCount_spec, rawTargetTypeCodes]

def scanRawCertificate {N m : ℕ} (R : RawTargetRows N m)
    (T : BTree (Cell N m)) : Bool :=
  decide ((scanLeaves T).Nodup) && scanSetEq (scanLeaves T) (scanRowLeaves R) &&
  R.rows.all (fun U => scanRefines U T) &&
  decide (scanStarScore (N + m * N + 3) Prod.snd T ≤ R.budget)

theorem scanRawCertificate_spec {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) (T : BTree (Cell N m)) :
    scanRawCertificate R T = true ↔
      StandardBlockRefinement (rawRowsToTarget R h).blocks T ∧
      starScore Finset.univ Prod.snd T ≤ R.budget := by
  have hscore : scanStarScore (N + m * N + 3) Prod.snd T =
      starScore Finset.univ Prod.snd T := by
    simpa only [terminal_card] using scanStarScore_spec Prod.snd T
  have hrows : (∀ U ∈ R.rows, CellRefines U T) ↔
      ∀ b : Block m, CellRefines ((rawRowsToTarget R h).blocks b) T := by
    constructor
    · intro hx b
      exact hx _ (rawRowsToTarget_mem R h b)
    · intro hx U hU
      obtain ⟨b, hb⟩ := rawRowsToTarget_hits R h U hU
      simpa only [hb] using hx b
  simp only [scanRawCertificate, Bool.and_eq_true, decide_eq_true_eq,
    scanSetEq_spec, scanLeaves_eq, scanRowLeaves_eq, List.all_eq_true,
    scanRefines_spec, hscore, hrows, StandardBlockRefinement,
    rawRowsToTarget_cellUnion]
  have hc : (leaves T).toFinset = cellSet T := by
    simpa only [scanLeaves_eq] using scanLeaves_cellSet T
  rw [hc]
  tauto

theorem scanRawCertificate_agrees {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) (T : BTree (Cell N m)) :
    scanRawCertificate R T = true ↔ checkBlockTarget (rawRowsToTarget R h) T = true := by
  rw [scanRawCertificate_spec R h, checkBlockTarget_spec]
  rfl

/-- Re-express the existing parser through computational definitions only.
    This is definitionally the SAME grammar, not a changed encoding. -/
def scanParseTargetPrefix (bits : List Bool) : Option (AnyRawTargetRows × List Bool) :=
  match readBinaryNatFrame bits with
  | none => none
  | some (N, r1) =>
      match readBinaryNatFrame r1 with
      | none => none
      | some (m, r2) =>
          match readBinaryNatFrame r2 with
          | none => none
          | some (budget, r3) =>
              match readFramedList (fun bs => parseBitPrefix N m bs.length bs) r3 with
              | none => none
              | some (rows, rest) => some (⟨N, m, ⟨budget, rows⟩⟩, rest)

def scanParseTarget (bits : List Bool) : Option AnyRawTargetRows :=
  match scanParseTargetPrefix bits with
  | some (R, []) => some R
  | _ => none

theorem scanParseTarget_eq (bits : List Bool) : scanParseTarget bits = parseRawTarget bits := rfl

def scanEncodedTarget (input cert : List Bool) : Bool :=
  match scanParseTarget input with
  | none => false
  | some ⟨N, m, R⟩ =>
      if scanRawTargetValid R then
        match parseBitTree N m cert with
        | none => false
        | some T => scanRawCertificate R T
      else false

theorem scanEncodedTarget_agrees (input cert : List Bool) :
    scanEncodedTarget input cert = true ↔ checkEncodedTarget input cert = true := by
  classical
  cases hp : parseRawTarget input with
  | none => simp [scanEncodedTarget, scanParseTarget_eq, hp, checkEncodedTarget, decodeTargetBits]
  | some R =>
      rcases R with ⟨N, m, R⟩
      by_cases hv : RawTargetRowsValid R
      · have hs := (scanRawTargetValid_spec R).mpr hv
        have hd := decodeRawTargetRows_valid R hv
        cases hc : parseBitTree N m cert with
        | none => simp [scanEncodedTarget, scanParseTarget_eq, hp, hs, hc,
            checkEncodedTarget, decodeTargetBits, hd, checkBlockTargetBits]
        | some T =>
            simpa [scanEncodedTarget, scanParseTarget_eq, hp, hs,
              hc, checkEncodedTarget, decodeTargetBits, hd, checkBlockTargetBits] using
              scanRawCertificate_agrees R hv T
      · have hs : scanRawTargetValid R = false := by
          cases hh : scanRawTargetValid R with
          | false => rfl
          | true => exact (hv ((scanRawTargetValid_spec R).mp hh)).elim
        have hr : rawTargetRowsValidBool R ≠ true := by
          intro hr
          exact hv ((rawTargetRowsValidBool_spec R).mp hr)
        have hd : decodeRawTargetRows R = none := by
          simp [decodeRawTargetRows, hr]
        simp [scanEncodedTarget, scanParseTarget_eq, hp, hs,
          checkEncodedTarget, decodeTargetBits, hd]

theorem scan_encoded_target_actual_iff_bounded (input : List Bool) (lambda : ℝ) :
    EncodedTargetCartaDecision input lambda ↔
      ∃ cert : List Bool, cert.length ≤ targetBitCertificateBound input.length ∧
        scanEncodedTarget input cert = true := by
  simp only [scanEncodedTarget_agrees]
  exact encoded_target_actual_iff_bounded input lambda

/-- The full encoded all-refinements/actual-label theorem is retained.
    The list algorithm is not a caterpillar-restricted or source-assisted check. -/
theorem full_encoded_source_scan_reduction (input : List Bool) (lambda : ℝ) :
    SourceBitMSSCDecision input ↔
      EncodedTargetCartaDecision (encodedSourceToTarget input) lambda ∧
      ∃ cert : List Bool,
        cert.length ≤ targetBitCertificateBound (encodedSourceToTarget input).length ∧
        scanEncodedTarget (encodedSourceToTarget input) cert = true := by
  have ha := full_encoded_source_actual_reduction input lambda
  have hb := scan_encoded_target_actual_iff_bounded (encodedSourceToTarget input) lambda
  tauto

/-- These are concrete intermediate-list SIZE bounds. They are not time
    certificates for either Lean evaluation or a Turing-machine execution. -/
theorem scanClades_length {A : Type u} (T : BTree A) :
    (scanClades T).length = vertexCount T := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr =>
      simp only [scanClades, List.length_cons, List.length_append, ihl, ihr, vertexCount]
      omega

theorem scanClade_length_le {A : Type u} (T : BTree A) :
    ∀ xs : List A, xs ∈ scanClades T → xs.length ≤ (scanLeaves T).length := by
  induction T with
  | leaf a =>
      intro xs h
      have hx : xs = [a] := by simpa [scanClades] using h
      simp [hx, scanLeaves]
  | node l r ihl ihr =>
      intro xs h
      have hm : xs = scanLeaves l ++ scanLeaves r ∨
          xs ∈ scanClades l ∨ xs ∈ scanClades r := by
        simpa only [scanClades, List.mem_cons, List.mem_append] using h
      simp only [scanLeaves, List.length_append]
      rcases hm with hx | hx | hx
      · simp [hx]
      · have hl := ihl xs hx
        omega
      · have hr := ihr xs hx
        omega

theorem scanListPayload_le {A : Type u} (xss : List (List A)) (k : ℕ)
    (h : ∀ xs ∈ xss, xs.length ≤ k) :
    (xss.map List.length).sum ≤ xss.length * k := by
  induction xss with
  | nil => simp
  | cons xs xss ih =>
      have hx := h xs (by simp)
      have ht := ih (fun ys hy => h ys (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem scanClades_payload_bound {A : Type u} (T : BTree A) :
    ((scanClades T).map List.length).sum ≤ vertexCount T * (leaves T).length := by
  simpa only [scanClades_length, scanLeaves_eq] using
    scanListPayload_le (scanClades T) (scanLeaves T).length (scanClade_length_le T)

theorem full_encoded_scan_reduction_with_size (input : List Bool) (lambda : ℝ) :
    (encodedSourceToTarget input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (encodedSourceToTarget input) lambda) ∧
      (EncodedTargetCartaDecision (encodedSourceToTarget input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (encodedSourceToTarget input).length ∧
          scanEncodedTarget (encodedSourceToTarget input) cert = true) := by
  exact ⟨encodedSourceToTarget_length_bound input,
    full_encoded_source_actual_reduction input lambda,
    scan_encoded_target_actual_iff_bounded (encodedSourceToTarget input) lambda⟩

/- Remaining: elaboration; a concrete finite-alphabet machine implementing
these list/natural operations and a BIT-cost/time theorem; a compatible
formal upstream hardness theorem/composition. No abstract list-cost model is
substituted for those obligations. This restricted marked-star checker is
not a claimed checker for arbitrary differentiation DAGs/rational weights. -/

end PolytomyReductionModel
