/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/machine certificate.

Ordinary-definition realization of the SAME total encoded constructor.
The source guard scans supplied lists before numerical-range enumeration.
The canonical sort and fixed combs are retained exactly. No minimizing
order, source-solution witness or arbitrary Finset.toList is computed.
Pointwise equality transfers the WHOLE prior all-refinement theorem.
Concrete finite-alphabet machines and bit-cost time bounds remain open.
-/
import PolytomyListScanVerifier

namespace PolytomyReductionModel

def scanSourceValid (R : RawMSSCRecord) : Bool :=
  decide (R.rows.length = R.declaredM) &&
  R.rows.flatten.all (fun x => decide (x < R.N)) &&
  decide (scanDistinctCount R.rows.flatten = R.N)

theorem scanSourceValid_spec (R : RawMSSCRecord) :
    scanSourceValid R = true ↔ RawMSSCValid R := by
  rw [← rawMSSCValidBool_spec]
  simp only [scanSourceValid, rawMSSCValidBool, scanDistinctCount_spec, rawElements]

/-- Fin N is enumerated only inside the already validated source branch.
    Its size is at most the number of explicitly supplied element records.
    A reference to the older model in the proof field is erased, not used
    as an algorithm for constructing the finite sets. -/
def scanSourceModel (R : RawMSSCRecord) (h : RawMSSCValid R) :
    MSSCInstance R.N R.rows.length where
  sets i := (List.finRange R.N).toFinset.filter (fun x => x.val ∈ R.rows.get i)
  covers x := by
    obtain ⟨i, hi⟩ := (rawToMSSC R h).covers x
    refine ⟨i, ?_⟩
    have hx := (rawToMSSC_mem R h i x).mp hi
    simpa using hx

theorem msscInstance_eq_of_sets {N m : ℕ} (D E : MSSCInstance N m)
    (h : D.sets = E.sets) : D = E := by
  cases D
  cases E
  cases h
  rfl

theorem scanSourceModel_eq (R : RawMSSCRecord) (h : RawMSSCValid R) :
    scanSourceModel R h = rawToMSSC R h := by
  apply msscInstance_eq_of_sets
  funext i
  ext x
  simp [scanSourceModel, rawToMSSC]

/-- The immutable block cost is computed by a concrete block-index list
    and the preceding descendant-distinct-count scanner. -/
def scanFixedCost {N m : ℕ} (blocks : Block m → BTree (Cell N m)) : ℕ :=
  ((blockIndexList m).map (fun b =>
    scanStarScore (N + m * N + 3) Prod.snd (blocks b))).sum

theorem scanFixedCost_eq {N m : ℕ} (blocks : Block m → BTree (Cell N m)) :
    scanFixedCost blocks = realizedFixedCost blocks := by
  have hp : (blockIndexList m).Perm (Finset.univ : Finset (Block m)).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq (blockIndexList_nodup m)
      Finset.univ.nodup_toList
    ext b
    simp [mem_blockIndexList]
  have hs : ∀ b : Block m, scanStarScore (N + m * N + 3) Prod.snd (blocks b) =
      starScore Finset.univ Prod.snd (blocks b) := by
    intro b
    simpa only [terminal_card] using scanStarScore_spec Prod.snd (blocks b)
  unfold scanFixedCost
  simp only [hs]
  rw [(hp.map (fun b => starScore Finset.univ Prod.snd (blocks b))).sum_eq,
    Finset.sum_map_toList]
  rfl

def scanCanonicalTarget {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : BlockTargetData N m where
  blocks := canonicalBlockTree D
  budget := scanFixedCost (canonicalBlockTree D) + K - N

theorem scanCanonicalTarget_eq {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    scanCanonicalTarget D K = canonicalBlockTarget D K := by
  apply blockTargetData_eq rfl
  exact congrArg (fun C => C + K - N) (scanFixedCost_eq (canonicalBlockTree D))

def scanFixedYesTarget : AnyBlockTarget := ⟨1, 2, scanCanonicalTarget fixedBoundarySource 1⟩

def scanFixedNoTarget : AnyBlockTarget :=
  ⟨1, 2, ⟨canonicalBlockTree fixedBoundarySource, 0⟩⟩

theorem scanFixedYesTarget_eq : scanFixedYesTarget = fixedYesTarget := by
  simp only [scanFixedYesTarget, fixedYesTarget, scanCanonicalTarget_eq]

theorem scanFixedNoTarget_eq : scanFixedNoTarget = fixedNoTarget := rfl

def scanTotalMSSCTarget {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : AnyBlockTarget :=
  if N = 0 then scanFixedYesTarget
  else if m ≤ 1 then (if N ≤ K then scanFixedYesTarget else scanFixedNoTarget)
  else if K < N then scanFixedNoTarget
  else if m * N ≤ K then scanFixedYesTarget
  else ⟨N, m, scanCanonicalTarget D K⟩

theorem scanTotalMSSCTarget_eq {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    scanTotalMSSCTarget D K = totalMSSCTarget D K := by
  simp only [scanTotalMSSCTarget, totalMSSCTarget, scanFixedYesTarget_eq,
    scanFixedNoTarget_eq, scanCanonicalTarget_eq]

/-- The data-dependent guard is evaluated BEFORE scanSourceModel is called. -/
def scanTotalRawTarget (R : RawMSSCRecord) : AnyBlockTarget :=
  if h : scanSourceValid R = true then
    scanTotalMSSCTarget (scanSourceModel R ((scanSourceValid_spec R).mp h)) R.K
  else scanFixedNoTarget

theorem scanTotalRawTarget_eq (R : RawMSSCRecord) :
    scanTotalRawTarget R = totalRawMSSCTarget R := by
  classical
  by_cases h : RawMSSCValid R
  · have hs := (scanSourceValid_spec R).mpr h
    have hd := decodeRawMSSC_valid R h
    simp [scanTotalRawTarget, hs, scanTotalMSSCTarget_eq, scanSourceModel_eq,
      totalRawMSSCTarget, hd]
  · have hs : scanSourceValid R ≠ true := by
      intro hs
      exact h ((scanSourceValid_spec R).mp hs)
    simp [scanTotalRawTarget, hs, totalRawMSSCTarget,
      decodeRawMSSC_invalid R h, scanFixedNoTarget_eq]

def scanTotalSourceTarget (input : List Bool) : AnyBlockTarget :=
  match parseRawMSSC input with
  | none => scanFixedNoTarget
  | some R => scanTotalRawTarget R

theorem scanTotalSourceTarget_eq (input : List Bool) :
    scanTotalSourceTarget input = totalSourceBitTarget input := by
  cases hp : parseRawMSSC input <;>
    simp [scanTotalSourceTarget, totalSourceBitTarget, hp,
      scanFixedNoTarget_eq, scanTotalRawTarget_eq]

/-- Direct serialization of the produced rows, with precisely the old
    header/payload grammar and concrete block-index ordering. -/
def scanEncodeTarget (G : AnyBlockTarget) : List Bool :=
  binaryNatFrame G.1 ++ binaryNatFrame G.2.1 ++ binaryNatFrame G.2.2.budget ++
    encodeFramedList treeBits ((blockIndexList G.2.1).map G.2.2.blocks)

theorem scanEncodeTarget_eq (G : AnyBlockTarget) :
    scanEncodeTarget G = encodeAnyTarget G := rfl

def scanEncodedConstructor (input : List Bool) : List Bool :=
  scanEncodeTarget (scanTotalSourceTarget input)

/-- Pointwise byte equality, not only equisatisfiability or a changed target. -/
theorem scanEncodedConstructor_eq (input : List Bool) :
    scanEncodedConstructor input = encodedSourceToTarget input := by
  simp only [scanEncodedConstructor, scanEncodeTarget_eq, scanTotalSourceTarget_eq,
    encodedSourceToTarget]

theorem full_explicit_encoded_reduction (input : List Bool) (lambda : ℝ) :
    (scanEncodedConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (scanEncodedConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (scanEncodedConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (scanEncodedConstructor input).length ∧
          scanEncodedTarget (scanEncodedConstructor input) cert = true) := by
  simpa only [scanEncodedConstructor_eq] using full_encoded_scan_reduction_with_size input lambda

/- This is a source-only intended computational realization, not compiled
code or a polynomial TM2 witness. The generic D-parameterized helpers do not
claim a uniform complexity bound on an arbitrary function D.sets. The total
bit constructor uses only the explicitly parsed-and-validated scanSourceModel.
Formal hardness/composition, machine-time bounds and all kernel checks remain
required. The full biological stochastic-identification problem stays open. -/

end PolytomyReductionModel
