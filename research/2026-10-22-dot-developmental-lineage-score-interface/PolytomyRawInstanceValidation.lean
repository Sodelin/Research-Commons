/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Malformed-dimension-safe validation of explicit parsed MSSC records.
No enumeration of 0,...,N-1 occurs in the VALIDATOR. Only after its Boolean
guard succeeds does the adapter form finite-index source sets. These are
parsed records, not yet a source bit parser or a polynomial machine.
-/
import PolytomyBitCertificate

namespace PolytomyReductionModel

structure RawMSSCRecord where
  N : ℕ
  declaredM : ℕ
  K : ℕ
  rows : List (List ℕ)

def rawElements (R : RawMSSCRecord) : Finset ℕ := R.rows.flatten.toFinset

def RawMSSCValid (R : RawMSSCRecord) : Prop :=
  R.rows.length = R.declaredM ∧
  (∀ x ∈ R.rows.flatten, x < R.N) ∧
  (rawElements R).card = R.N

/-- Record/list-length work and binary-number comparisons precede any loop
    over the declared dimensions. Coverage is checked by distinct count. -/
def rawMSSCValidBool (R : RawMSSCRecord) : Bool :=
  decide (R.rows.length = R.declaredM) &&
  R.rows.flatten.all (fun x => decide (x < R.N)) &&
  decide ((rawElements R).card = R.N)

theorem rawMSSCValidBool_spec (R : RawMSSCRecord) :
    rawMSSCValidBool R = true ↔ RawMSSCValid R := by
  simp [rawMSSCValidBool, RawMSSCValid, List.all_eq_true, and_assoc]

/-- A declared universe is fully covered exactly because all observed
    indices are in its range and their distinct count equals N. -/
theorem rawElements_eq_range (R : RawMSSCRecord) (h : RawMSSCValid R) :
    rawElements R = Finset.range R.N := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_range.mpr (h.2.1 x (by simpa [rawElements] using hx))
  · simpa [h.2.2]

def rawRecordSize (R : RawMSSCRecord) : ℕ :=
  R.rows.length + R.rows.flatten.length + 1

theorem raw_valid_dimensions_bounded (R : RawMSSCRecord) (h : RawMSSCValid R) :
    R.N ≤ R.rows.flatten.length ∧ R.declaredM ≤ rawRecordSize R := by
  have hc := List.toFinset_card_le R.rows.flatten
  have hc' : (rawElements R).card ≤ R.rows.flatten.length := hc
  have hm := h.1
  have hn : R.N ≤ R.rows.flatten.length := by
    rwa [h.2.2] at hc'
  exact ⟨hn, by unfold rawRecordSize; omega⟩

/-- Only called AFTER validation. Enumerating Fin N here is then bounded by
    the number of explicitly supplied entries, including duplicated ones. -/
noncomputable def rawToMSSC (R : RawMSSCRecord) (h : RawMSSCValid R) :
    MSSCInstance R.N R.rows.length where
  sets i := Finset.univ.filter (fun x : Fin R.N => x.val ∈ R.rows.get i)
  covers x := by
    have hx : x.val ∈ rawElements R := by
      rw [rawElements_eq_range R h]
      exact Finset.mem_range.mpr x.isLt
    have hx' : x.val ∈ R.rows.flatten := by simpa [rawElements] using hx
    obtain ⟨row, hrow, hxr⟩ := List.mem_flatten.mp hx'
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
    refine ⟨i, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [hi] using hxr

theorem rawToMSSC_mem (R : RawMSSCRecord) (h : RawMSSCValid R)
    (i : Fin R.rows.length) (x : Fin R.N) :
    x ∈ (rawToMSSC R h).sets i ↔ x.val ∈ R.rows.get i := by
  simp [rawToMSSC]

/-- The dependent proof is obtained from the finite Boolean guard. An
    invalid parsed record returns none without constructing its universe. -/
noncomputable def decodeRawMSSC (R : RawMSSCRecord) :
    Option (MSSCInstance R.N R.rows.length) :=
  if h : rawMSSCValidBool R = true then
    some (rawToMSSC R ((rawMSSCValidBool_spec R).mp h))
  else none

theorem decodeRawMSSC_valid (R : RawMSSCRecord) (h : RawMSSCValid R) :
    decodeRawMSSC R = some (rawToMSSC R h) := by
  simp [decodeRawMSSC, (rawMSSCValidBool_spec R).mpr h]

theorem decodeRawMSSC_invalid (R : RawMSSCRecord) (h : ¬ RawMSSCValid R) :
    decodeRawMSSC R = none := by
  have hb : rawMSSCValidBool R ≠ true := by
    intro hb
    exact h ((rawMSSCValidBool_spec R).mp hb)
  simp [decodeRawMSSC, hb]

theorem decodeRawMSSC_success_iff (R : RawMSSCRecord) :
    (∃ D, decodeRawMSSC R = some D) ↔ RawMSSCValid R := by
  constructor
  · rintro ⟨D, hD⟩
    by_contra hn
    rw [decodeRawMSSC_invalid R hn] at hD
    cases hD
  · intro h
    exact ⟨rawToMSSC R h, decodeRawMSSC_valid R h⟩

def RawMSSCDecision (R : RawMSSCRecord) : Prop :=
  ∃ D : MSSCInstance R.N R.rows.length,
    decodeRawMSSC R = some D ∧ MSSCDecision D R.K

theorem rawMSSCDecision_valid_iff (R : RawMSSCRecord) (h : RawMSSCValid R) :
    RawMSSCDecision R ↔ MSSCDecision (rawToMSSC R h) R.K := by
  constructor
  · rintro ⟨D, hD, hK⟩
    rw [decodeRawMSSC_valid R h] at hD
    have he : rawToMSSC R h = D := Option.some.inj hD
    simpa only [he] using hK
  · intro hK
    exact ⟨rawToMSSC R h, decodeRawMSSC_valid R h, hK⟩

theorem rawMSSCDecision_invalid (R : RawMSSCRecord) (h : ¬ RawMSSCValid R) :
    ¬ RawMSSCDecision R := by
  rintro ⟨D, hD, hK⟩
  rw [decodeRawMSSC_invalid R h] at hD
  cases hD

/-- The parsed-record continuation composes with the ENTIRE original
    all-refinement, actual-label score reduction, not an ordering surrogate. -/
theorem full_rawMSSC_bit_reduction (R : RawMSSCRecord) (h : RawMSSCValid R)
    (hN : 0 < R.N) (hm : 2 ≤ R.rows.length)
    (hNK : R.N ≤ R.K) (hKmN : R.K ≤ R.rows.length * R.N) :
    RawMSSCDecision R ↔
      ∃ bits : List Bool, bits.length ≤ bitCertificateBound R.N R.rows.length ∧
        checkBlockTargetBits (canonicalBlockTarget (rawToMSSC R h) R.K) bits = true := by
  exact (rawMSSCDecision_valid_iff R h).trans
    (full_mssc_bit_reduction (rawToMSSC R h) R.K hN hm hNK hKmN)

/- Remaining: a concrete source/target instance bit codec and total machine
cost proofs. The nontrivial-branch theorem is not yet a total encoded many-one
map; directly decidable small/boundary cases are handled in the later
PolytomyTotalSourceReduction companion. That adapter is not assumed here. -/

end PolytomyReductionModel
