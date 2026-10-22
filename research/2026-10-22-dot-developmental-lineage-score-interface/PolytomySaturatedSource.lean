/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution, machine certificate or kernel check.

Polynomial-value saturation for the SAME total source constructor.
Raw binary fields may be enormous. Dimensions/identifiers use an L+1
overflow sentinel and the threshold uses (L+1)^2. Invalid inputs cannot
become valid, and the constructor's exact output bytes are unchanged.
This is an algorithmic/semantic bridge, not a supplied whole TM2 machine.
-/
import PolytomyBinaryWidthBounds

namespace PolytomyReductionModel
universe u v

def saturatedBinaryValue (cap : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: bits => min (Nat.bit b (saturatedBinaryValue cap bits)) cap

theorem min_bit_min (b : Bool) (n cap : ℕ) :
    min (Nat.bit b (min n cap)) cap = min (Nat.bit b n) cap := by
  cases b <;> simp only [Nat.bit] <;> omega

theorem saturatedBinaryValue_eq (cap : ℕ) (bits : List Bool) :
    saturatedBinaryValue cap bits = min (fromBinaryBits bits) cap := by
  induction bits with
  | nil => simp [saturatedBinaryValue, fromBinaryBits]
  | cons b bits ih =>
      change min (Nat.bit b (saturatedBinaryValue cap bits)) cap =
        min (Nat.bit b (fromBinaryBits bits)) cap
      rw [ih, min_bit_min]

theorem saturatedBinaryValue_le (cap : ℕ) (bits : List Bool) :
    saturatedBinaryValue cap bits ≤ cap := by
  rw [saturatedBinaryValue_eq]
  exact min_le_right _ _

/-- Before each saturation, even the transient arithmetic value is small. -/
theorem saturatedBinaryValue_step_bound (cap : ℕ) (b : Bool) (bits : List Bool) :
    Nat.bit b (saturatedBinaryValue cap bits) ≤ 2 * cap + 1 := by
  have h := saturatedBinaryValue_le cap bits
  cases b <;> simp only [Nat.bit] <;> omega

def readSaturatedBinaryNatFrame (cap : ℕ) (bits : List Bool) :
    Option (ℕ × List Bool) :=
  match readUnaryFrame bits with
  | none => none
  | some (width, rest) =>
      if width ≤ rest.length then
        some (saturatedBinaryValue cap (rest.take width), rest.drop width)
      else none

theorem readSaturatedBinaryNatFrame_eq (cap : ℕ) (bits : List Bool) :
    readSaturatedBinaryNatFrame cap bits =
      (readBinaryNatFrame bits).map (fun p => (min p.1 cap, p.2)) := by
  cases h : readUnaryFrame bits with
  | none => simp [readSaturatedBinaryNatFrame, readBinaryNatFrame, h]
  | some p =>
      rcases p with ⟨width, rest⟩
      by_cases hw : width ≤ rest.length <;>
        simp [readSaturatedBinaryNatFrame, readBinaryNatFrame, h, hw,
          saturatedBinaryValue_eq]

theorem readMany_map_values {A : Type u} {B : Type v}
    (readA : List Bool → Option (A × List Bool))
    (readB : List Bool → Option (B × List Bool)) (f : A → B)
    (hf : ∀ bits, readB bits = (readA bits).map (fun p => (f p.1, p.2)))
    (n : ℕ) : ∀ bits,
    readMany readB n bits = (readMany readA n bits).map (fun p => (p.1.map f, p.2)) := by
  induction n with
  | zero => intro bits; rfl
  | succ n ih =>
      intro bits
      cases hr : readA bits with
      | none => simp [readMany, hf, hr]
      | some p =>
          rcases p with ⟨a, rest⟩
          cases ht : readMany readA n rest with
          | none => simp [readMany, hf, hr, ih, ht]
          | some p =>
              rcases p with ⟨xs, after⟩
              simp [readMany, hf, hr, ih, ht]

theorem readFramedList_map_values {A : Type u} {B : Type v}
    (readA : List Bool → Option (A × List Bool))
    (readB : List Bool → Option (B × List Bool)) (f : A → B)
    (hf : ∀ bits, readB bits = (readA bits).map (fun p => (f p.1, p.2)))
    (bits : List Bool) :
    readFramedList readB bits =
      (readFramedList readA bits).map (fun p => (p.1.map f, p.2)) := by
  cases h : readUnaryFrame bits with
  | none => simp [readFramedList, h]
  | some p =>
      rcases p with ⟨n, rest⟩
      simpa only [readFramedList, h] using readMany_map_values readA readB f hf n rest

def clipSourceRows (L : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  rows.map (List.map (fun x => min x (L + 1)))

def clipSourceData (L : ℕ) (R : RawMSSCRecord) : RawMSSCRecord :=
  ⟨min R.N (L + 1), min R.declaredM (L + 1), R.K, clipSourceRows L R.rows⟩

def clipSourceBudget (cap : ℕ) (R : RawMSSCRecord) : RawMSSCRecord :=
  { R with K := min R.K cap }

def saturatedSourceRecord (L : ℕ) (R : RawMSSCRecord) : RawMSSCRecord :=
  clipSourceBudget ((L + 1) ^ 2) (clipSourceData L R)

theorem clipSourceRows_flatten (L : ℕ) (rows : List (List ℕ)) :
    (clipSourceRows L rows).flatten = rows.flatten.map (fun x => min x (L + 1)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simpa only [clipSourceRows, List.map_cons, List.flatten_cons, List.map_append] using
        congrArg (fun tail => row.map (fun x => min x (L + 1)) ++ tail) ih

theorem clipSourceData_size (L : ℕ) (R : RawMSSCRecord) :
    rawRecordSize (clipSourceData L R) = rawRecordSize R := by
  change (clipSourceRows L R.rows).length + (clipSourceRows L R.rows).flatten.length + 1 =
    R.rows.length + R.rows.flatten.length + 1
  rw [clipSourceRows_flatten]
  simp only [clipSourceRows, List.length_map]

theorem clipSourceRow_eq (L : ℕ) (row : List ℕ)
    (h : ∀ x ∈ row, x ≤ L) : row.map (fun x => min x (L + 1)) = row := by
  induction row with
  | nil => rfl
  | cons x row ih =>
      have hx : x ≤ L + 1 := (h x (by simp)).trans (by omega)
      have ht : ∀ y ∈ row, y ≤ L := fun y hy => h y (by simp [hy])
      simp only [List.map_cons, min_eq_left hx, ih ht]

theorem clipSourceRows_eq (L : ℕ) (rows : List (List ℕ))
    (h : ∀ x ∈ rows.flatten, x ≤ L) : clipSourceRows L rows = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hr : ∀ x ∈ row, x ≤ L := fun x hx => h x (by simp [hx])
      have ht : ∀ x ∈ rows.flatten, x ≤ L := fun x hx => h x (by simp [hx])
      simp only [clipSourceRows, List.map_cons, clipSourceRow_eq L row hr]
      exact congrArg (List.cons row) (ih ht)

theorem clipSourceData_eq_of_valid (L : ℕ) (R : RawMSSCRecord)
    (hs : rawRecordSize R ≤ L) (hv : RawMSSCValid R) : clipSourceData L R = R := by
  obtain ⟨hN, hm⟩ := raw_valid_dimensions_bounded R hv
  have hflat : R.rows.flatten.length ≤ L := by unfold rawRecordSize at hs; omega
  have hn : R.N ≤ L + 1 := by omega
  have hm' : R.declaredM ≤ L + 1 := by omega
  have hx : ∀ x ∈ R.rows.flatten, x ≤ L := by
    intro x hx
    have hr := hv.2.1 x hx
    omega
  have hr := clipSourceRows_eq L R.rows hx
  unfold clipSourceData
  rw [min_eq_left hn, min_eq_left hm', hr]
  cases R
  rfl

/-- The sentinel cannot conceal an out-of-range header or identifier.
    This reverse direction is essential, not merely preservation of valid inputs. -/
theorem clipSourceData_eq_of_clipped_valid (L : ℕ) (R : RawMSSCRecord)
    (hs : rawRecordSize R ≤ L) (hv : RawMSSCValid (clipSourceData L R)) :
    clipSourceData L R = R := by
  have hsize := clipSourceData_size L R
  obtain ⟨hn, hm⟩ := raw_valid_dimensions_bounded (clipSourceData L R) hv
  have hflat : R.rows.flatten.length ≤ L := by unfold rawRecordSize at hs; omega
  have hrows : R.rows.length ≤ L := by unfold rawRecordSize at hs; omega
  have hn' : min R.N (L + 1) ≤ L := by
    have hbase : min R.N (L + 1) ≤ R.rows.flatten.length := by
      simpa only [clipSourceData, clipSourceRows_flatten, List.length_map] using hn
    exact hbase.trans hflat
  have hN : R.N ≤ L := by omega
  have hm' : min R.declaredM (L + 1) ≤ L := by
    have hsC : rawRecordSize (clipSourceData L R) ≤ L := by
      rw [clipSourceData_size]
      exact hs
    simpa only [clipSourceData] using hm.trans hsC
  have hM : R.declaredM ≤ L := by omega
  have hx : ∀ x ∈ R.rows.flatten, x ≤ L := by
    intro x hx
    have hmemb : min x (L + 1) ∈ (clipSourceData L R).rows.flatten := by
      simp only [clipSourceData, clipSourceRows_flatten]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have hr := hv.2.1 (min x (L + 1)) hmemb
    change min x (L + 1) < min R.N (L + 1) at hr
    omega
  have hr := clipSourceRows_eq L R.rows hx
  have hnMin : min R.N (L + 1) = R.N := min_eq_left (by omega)
  have hmMin : min R.declaredM (L + 1) = R.declaredM := min_eq_left (by omega)
  unfold clipSourceData
  rw [hnMin, hmMin, hr]
  cases R
  rfl

theorem clipSourceData_valid_iff (L : ℕ) (R : RawMSSCRecord)
    (hs : rawRecordSize R ≤ L) :
    RawMSSCValid (clipSourceData L R) ↔ RawMSSCValid R := by
  constructor
  · intro hv
    simpa only [clipSourceData_eq_of_clipped_valid L R hs hv] using hv
  · intro hv
    simpa only [clipSourceData_eq_of_valid L R hs hv] using hv

theorem scanTotalRawTarget_clip_data (L : ℕ) (R : RawMSSCRecord)
    (hs : rawRecordSize R ≤ L) :
    scanTotalRawTarget (clipSourceData L R) = scanTotalRawTarget R := by
  by_cases hv : RawMSSCValid R
  · rw [clipSourceData_eq_of_valid L R hs hv]
  · have hc : ¬ RawMSSCValid (clipSourceData L R) :=
      fun h => hv ((clipSourceData_valid_iff L R hs).mp h)
    have hsR : scanSourceValid R ≠ true := fun h => hv ((scanSourceValid_spec R).mp h)
    have hsC : scanSourceValid (clipSourceData L R) ≠ true :=
      fun h => hc ((scanSourceValid_spec _).mp h)
    simp [scanTotalRawTarget, hsR, hsC]

theorem scanTotalMSSCTarget_min_budget {N m : ℕ} (D : MSSCInstance N m)
    (K cap : ℕ) (hN : N ≤ cap) (hmN : m * N ≤ cap) :
    scanTotalMSSCTarget D (min K cap) = scanTotalMSSCTarget D K := by
  by_cases hK : K ≤ cap
  · rw [min_eq_left hK]
  · have hcap : cap ≤ K := by omega
    have hNK : N ≤ K := hN.trans hcap
    have hmNK : m * N ≤ K := hmN.trans hcap
    rw [min_eq_right hcap]
    by_cases hz : N = 0
    · simp [scanTotalMSSCTarget, hz]
    · by_cases hm : m ≤ 1 <;>
        simp [scanTotalMSSCTarget, hz, hm, hN, hNK, hmN, hmNK,
          Nat.not_lt.mpr hN, Nat.not_lt.mpr hNK]

theorem clipSourceBudget_valid (cap : ℕ) (R : RawMSSCRecord) :
    RawMSSCValid (clipSourceBudget cap R) ↔ RawMSSCValid R := by
  rfl

theorem scanSourceModel_clip_budget (cap : ℕ) (R : RawMSSCRecord)
    (h : RawMSSCValid (clipSourceBudget cap R)) (hR : RawMSSCValid R) :
    scanSourceModel (clipSourceBudget cap R) h = scanSourceModel R hR := by
  apply msscInstance_eq_of_sets
  rfl

theorem scanTotalRawTarget_clip_budget (L : ℕ) (R : RawMSSCRecord)
    (hs : rawRecordSize R ≤ L) :
    scanTotalRawTarget (clipSourceBudget ((L + 1) ^ 2) R) = scanTotalRawTarget R := by
  let cap := (L + 1) ^ 2
  change scanTotalRawTarget (clipSourceBudget cap R) = scanTotalRawTarget R
  by_cases hv : RawMSSCValid R
  · have hc : RawMSSCValid (clipSourceBudget cap R) := (clipSourceBudget_valid cap R).mpr hv
    have hb := (scanSourceValid_spec R).mpr hv
    have hbC := (scanSourceValid_spec (clipSourceBudget cap R)).mpr hc
    obtain ⟨hNv, hm⟩ := raw_valid_dimensions_bounded R hv
    have hN : R.N ≤ L := by unfold rawRecordSize at hs; omega
    have hM : R.rows.length ≤ L := by unfold rawRecordSize at hs; omega
    have hcapN : R.N ≤ cap := by dsimp [cap]; nlinarith
    have hcapM : R.rows.length * R.N ≤ cap := by
      have hp := Nat.mul_le_mul hM hN
      dsimp [cap]
      nlinarith
    simp only [scanTotalRawTarget, dif_pos hb, dif_pos hbC]
    rw [scanSourceModel_clip_budget cap R _ hv]
    exact scanTotalMSSCTarget_min_budget (scanSourceModel R hv) R.K cap hcapN hcapM
  · have hc : ¬ RawMSSCValid (clipSourceBudget cap R) :=
      fun h => hv ((clipSourceBudget_valid cap R).mp h)
    have hb : scanSourceValid R ≠ true := fun h => hv ((scanSourceValid_spec R).mp h)
    have hbC : scanSourceValid (clipSourceBudget cap R) ≠ true :=
      fun h => hc ((scanSourceValid_spec _).mp h)
    simp [scanTotalRawTarget, hb, hbC]

theorem scanTotalRawTarget_saturated (L : ℕ) (R : RawMSSCRecord)
    (hs : rawRecordSize R ≤ L) :
    scanTotalRawTarget (saturatedSourceRecord L R) = scanTotalRawTarget R := by
  unfold saturatedSourceRecord
  rw [scanTotalRawTarget_clip_budget L (clipSourceData L R)
    (by simpa only [clipSourceData_size] using hs)]
  exact scanTotalRawTarget_clip_data L R hs

def parseSaturatedSourcePrefix (L : ℕ) (bits : List Bool) :
    Option (RawMSSCRecord × List Bool) :=
  match readSaturatedBinaryNatFrame (L + 1) bits with
  | none => none
  | some (N, r1) =>
      match readSaturatedBinaryNatFrame (L + 1) r1 with
      | none => none
      | some (m, r2) =>
          match readSaturatedBinaryNatFrame ((L + 1) ^ 2) r2 with
          | none => none
          | some (K, r3) =>
              match readFramedList (readFramedList (readSaturatedBinaryNatFrame (L + 1))) r3 with
              | none => none
              | some (rows, rest) => some (⟨N, m, K, rows⟩, rest)

theorem saturated_rows_reader_eq (L : ℕ) (bits : List Bool) :
    readFramedList (readFramedList (readSaturatedBinaryNatFrame (L + 1))) bits =
      (readFramedList (readFramedList readBinaryNatFrame) bits).map
        (fun p => (clipSourceRows L p.1, p.2)) := by
  exact readFramedList_map_values (readFramedList readBinaryNatFrame)
    (readFramedList (readSaturatedBinaryNatFrame (L + 1)))
    (List.map (fun x => min x (L + 1)))
    (readFramedList_map_values readBinaryNatFrame
      (readSaturatedBinaryNatFrame (L + 1)) (fun x => min x (L + 1))
      (readSaturatedBinaryNatFrame_eq (L + 1))) bits

theorem parseSaturatedSourcePrefix_eq (L : ℕ) (bits : List Bool) :
    parseSaturatedSourcePrefix L bits =
      (parseRawMSSCPrefix bits).map (fun p => (saturatedSourceRecord L p.1, p.2)) := by
  unfold parseSaturatedSourcePrefix parseRawMSSCPrefix
  rw [readSaturatedBinaryNatFrame_eq]
  cases h1 : readBinaryNatFrame bits with
  | none => rfl
  | some p =>
      rcases p with ⟨N, r1⟩
      simp only [Option.map_some]
      rw [readSaturatedBinaryNatFrame_eq]
      cases h2 : readBinaryNatFrame r1 with
      | none => rfl
      | some p =>
          rcases p with ⟨m, r2⟩
          simp only [Option.map_some]
          rw [readSaturatedBinaryNatFrame_eq]
          cases h3 : readBinaryNatFrame r2 with
          | none => rfl
          | some p =>
              rcases p with ⟨K, r3⟩
              simp only [Option.map_some]
              rw [saturated_rows_reader_eq]
              cases h4 : readFramedList (readFramedList readBinaryNatFrame) r3 with
              | none => rfl
              | some p => rcases p with ⟨rows, rest⟩; rfl

def parseSaturatedSource (bits : List Bool) : Option RawMSSCRecord :=
  match parseSaturatedSourcePrefix bits.length bits with
  | some (R, []) => some R
  | _ => none

theorem parseSaturatedSource_eq (bits : List Bool) :
    parseSaturatedSource bits = (parseRawMSSC bits).map (saturatedSourceRecord bits.length) := by
  unfold parseSaturatedSource parseRawMSSC
  rw [parseSaturatedSourcePrefix_eq]
  cases h : parseRawMSSCPrefix bits with
  | none => rfl
  | some p => rcases p with ⟨R, rest⟩; cases rest <;> rfl

def saturatedEncodedConstructor (bits : List Bool) : List Bool :=
  scanEncodeTarget (match parseSaturatedSource bits with
    | none => scanFixedNoTarget
    | some R => scanTotalRawTarget R)

/-- Exact output bytes for EVERY input, not merely satisfiability. -/
theorem saturatedEncodedConstructor_eq (bits : List Bool) :
    saturatedEncodedConstructor bits = scanEncodedConstructor bits := by
  unfold saturatedEncodedConstructor scanEncodedConstructor scanTotalSourceTarget
  rw [parseSaturatedSource_eq]
  cases h : parseRawMSSC bits with
  | none => rfl
  | some R =>
      simp only [Option.map_some]
      rw [scanTotalRawTarget_saturated bits.length R (parseRawMSSC_size_bound bits R h)]

theorem saturatedSourceRecord_bounds (L : ℕ) (R : RawMSSCRecord) :
    (saturatedSourceRecord L R).N ≤ L + 1 ∧
    (saturatedSourceRecord L R).declaredM ≤ L + 1 ∧
    (saturatedSourceRecord L R).K ≤ (L + 1) ^ 2 ∧
    ∀ x ∈ (saturatedSourceRecord L R).rows.flatten, x ≤ L + 1 := by
  refine ⟨min_le_right _ _, min_le_right _ _, min_le_right _ _, ?_⟩
  intro x hx
  change x ∈ (clipSourceRows L R.rows).flatten at hx
  rw [clipSourceRows_flatten] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact min_le_right _ _

theorem saturatedSourceRecord_size (L : ℕ) (R : RawMSSCRecord) :
    rawRecordSize (saturatedSourceRecord L R) = rawRecordSize R := by
  change rawRecordSize (clipSourceData L R) = rawRecordSize R
  exact clipSourceData_size L R

theorem parsed_saturated_source_bounds (bits : List Bool) (R : RawMSSCRecord)
    (h : parseSaturatedSource bits = some R) :
    rawRecordSize R ≤ bits.length ∧ R.N ≤ bits.length + 1 ∧
    R.declaredM ≤ bits.length + 1 ∧ R.K ≤ (bits.length + 1) ^ 2 ∧
    ∀ x ∈ R.rows.flatten, x ≤ bits.length + 1 := by
  rw [parseSaturatedSource_eq] at h
  cases hp : parseRawMSSC bits with
  | none => simp [hp] at h
  | some Q =>
      have he : saturatedSourceRecord bits.length Q = R := by simpa [hp] using h
      rw [← he]
      refine ⟨?_, saturatedSourceRecord_bounds bits.length Q⟩
      rw [saturatedSourceRecord_size]
      exact parseRawMSSC_size_bound bits Q hp

def sourceUnaryValueMass (R : RawMSSCRecord) : ℕ :=
  R.N + R.declaredM + R.K + R.rows.flatten.sum + rawRecordSize R

theorem list_sum_le_length_mul (xs : List ℕ) (cap : ℕ)
    (h : ∀ x ∈ xs, x ≤ cap) : xs.sum ≤ xs.length * cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith

/-- Even a unary representation of ALL parsed numeric values is polynomial.
    This concerns the saturated algorithm, not the original unbounded values. -/
theorem parsed_saturated_unary_mass (bits : List Bool) (R : RawMSSCRecord)
    (h : parseSaturatedSource bits = some R) :
    sourceUnaryValueMass R ≤ 3 * (bits.length + 1) ^ 2 := by
  obtain ⟨hs, hN, hm, hK, hx⟩ := parsed_saturated_source_bounds bits R h
  have hlen : R.rows.flatten.length ≤ bits.length := by
    unfold rawRecordSize at hs
    omega
  have hsum := list_sum_le_length_mul R.rows.flatten (bits.length + 1) hx
  have hprod := Nat.mul_le_mul hlen (le_refl (bits.length + 1))
  unfold sourceUnaryValueMass
  nlinarith

/-- Any actual polynomial machine for this exact bounded-value algorithm
    would inhabit the original constructor obligation, without a new target. -/
def originalConstructorMachineOfSaturated
    (h : Turing.TM2ComputableInPolyTime
      (fun bits : List Bool => bits) (fun bits : List Bool => bits)
      saturatedEncodedConstructor) : ConstructorMachineWitness := by
  have he : saturatedEncodedConstructor = scanEncodedConstructor :=
    funext saturatedEncodedConstructor_eq
  simpa only [he] using h

/-- The original full actual-D_lambda and independent-certificate endpoint
    is transferred through BYTE equality, not through a weakened objective. -/
theorem full_saturated_source_reduction (input : List Bool) (lambda : ℝ) :
    (saturatedEncodedConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (saturatedEncodedConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (saturatedEncodedConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (saturatedEncodedConstructor input).length ∧
          scanEncodedTarget (saturatedEncodedConstructor input) cert = true) := by
  simpa only [saturatedEncodedConstructor_eq] using full_explicit_encoded_reduction input lambda

/- The saturated decoder only combines values at most cap, with transient
values at most 2*cap+1. This is a mathematical bounded-value implementation,
not a complete finite-machine witness. Nested framing, source validation,
canonical block construction, serialization, actual whole-program bounds,
the independent target verifier, encoded source hardness and all kernel
checks remain required. No execution hold or original target is changed.
-/

end PolytomyReductionModel
