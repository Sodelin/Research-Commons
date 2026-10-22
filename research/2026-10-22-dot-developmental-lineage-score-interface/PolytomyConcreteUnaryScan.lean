/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Concrete fixed finite port layout joins actual original-record replay,
physical headers and both rows loops. The physical query cap is supplied
explicitly. Record acceptance, query preparation and replay cleanup are
not silently assumed from this prefix composition.
-/
import PolytomyUnaryRowsCounterBounds
import PolytomyCopiedHeaderCaller

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive UnaryScanPort where
  | original | copyTemp | headerN | headerM | headerK
  | observed | swapTemp | residual | right | inner | outer | savedCount | queries
  deriving DecidableEq, Fintype

def scanVisitPorts : UnaryVisitPorts UnaryScanPort where
  m := .observed
  t := .swapTemp
  l := .residual
  r := .right
  hmt := by decide
  hlm := by decide
  hlt := by decide
  hlr := by decide
  hrm := by decide
  hrt := by decide

def scanRowsPorts : UnaryRowsPorts UnaryScanPort where
  p := scanVisitPorts
  c := .inner
  d := .outer
  saved := .savedCount
  hc := by decide
  hd := by decide
  hs := by decide
  hcd := by decide
  hsc := by decide
  hsd := by decide

def scanHeaderPorts : InternalHeaderPorts (NumericStack UnaryScanPort) where
  source := .inl .source
  n := .inr .headerN
  m := .inr .headerM
  k := .inr .headerK
  hsn := by decide
  hsm := by decide
  hsk := by decide
  hnm := by decide
  hnk := by decide
  hmk := by decide

def scanWorkExtras : List UnaryScanPort :=
  [.copyTemp, .headerN, .headerM, .headerK, .observed, .swapTemp, .residual, .right, .inner, .outer, .savedCount]

variable {F : Type}

structure UnaryScanReady (C L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) F) : Prop where
  numeric : NumericLoopInv C L s
  source_empty : s.stk (.inl .source) = []
  empty : ∀ k ∈ scanWorkExtras, s.stk (.inr k) = []
  original_bound : (s.stk (.inr .original)).length ≤ L

def scanHeaderEval (s : CountdownStore (NumericStack UnaryScanPort) F) :=
  copiedHeaderEval (.inr .original) scanHeaderPorts s

def scanHeaderRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState F) :=
  copiedHeaderRoutine (.inr .original) (.inr .copyTemp) scanHeaderPorts

theorem scanHeader_executes (C L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) F)
    (hs : UnaryScanReady C L s) : ∃ n ≤ 9 * L + 16,
      scanHeaderRoutine.Executes s (scanHeaderEval s) n ∧
      internalHeaderObservation scanHeaderPorts (scanHeaderEval s) =
        readInternalHeaderPrefix (s.stk (.inr .original)) ∧
      ((scanHeaderEval s).stk (.inl .source)).length ≤ L ∧
      ((scanHeaderEval s).stk (.inr .headerN)).length ≤ L ∧
      ((scanHeaderEval s).stk (.inr .headerM)).length ≤ L ∧
      ((scanHeaderEval s).stk (.inr .headerK)).length ≤ L := by
  obtain ⟨n, hn, he, ho, hsrc, hN, hM, hK⟩ := copiedHeader_executes
    (.inr .original : NumericStack UnaryScanPort) (.inr .copyTemp) scanHeaderPorts
    (by decide) (by decide) (by decide) s (hs.empty .copyTemp (by simp [scanWorkExtras]))
    hs.source_empty (hs.empty .headerN (by simp [scanWorkExtras]))
    (hs.empty .headerM (by simp [scanWorkExtras])) (hs.empty .headerK (by simp [scanWorkExtras]))
  have hL := hs.original_bound
  exact ⟨n, by omega, he, ho, hsrc.trans hL, hN.trans hL, hM.trans hL, hK.trans hL⟩

theorem scanHeader_numeric_extra (s : CountdownStore (NumericStack UnaryScanPort) F)
    (port : NumericPort) (h : port ≠ .source) :
    (scanHeaderEval s).stk (.inl port) = s.stk (.inl port) := by
  exact copiedHeader_extra (.inr .original) scanHeaderPorts (.inl port)
    (by simpa [scanHeaderPorts] using h) (by simp [scanHeaderPorts])
    (by simp [scanHeaderPorts]) (by simp [scanHeaderPorts]) s

theorem scanHeader_extra (s : CountdownStore (NumericStack UnaryScanPort) F) (k : UnaryScanPort)
    (hN : k ≠ .headerN) (hM : k ≠ .headerM) (hK : k ≠ .headerK) :
    (scanHeaderEval s).stk (.inr k) = s.stk (.inr k) := by
  exact copiedHeader_extra (.inr .original) scanHeaderPorts (.inr k)
    (by simp [scanHeaderPorts]) (by simpa [scanHeaderPorts] using hN)
    (by simpa [scanHeaderPorts] using hM) (by simpa [scanHeaderPorts] using hK) s

theorem scanHeader_rows_ready (C L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) F)
    (hs : UnaryScanReady C L s) :
    UnaryVisitInv scanVisitPorts C L (scanHeaderEval s) ∧
      (scanHeaderEval s).stk (.inr .inner) = [] ∧
      (scanHeaderEval s).stk (.inr .outer) = [] ∧
      (scanHeaderEval s).stk (.inr .savedCount) = [] := by
  obtain ⟨n, hn, he, ho, hsrc, hN, hM, hK⟩ := scanHeader_executes C L s hs
  have hwork : ∀ k ∈ [UnaryScanPort.observed, .swapTemp, .residual, .right, .inner, .outer, .savedCount],
      (scanHeaderEval s).stk (.inr k) = [] := by
    intro k hk
    have hN : k ≠ .headerN := by cases k <;> simp_all
    have hM : k ≠ .headerM := by cases k <;> simp_all
    have hK : k ≠ .headerK := by cases k <;> simp_all
    rw [scanHeader_extra s k hN hM hK]
    exact hs.empty k (by simp only [scanWorkExtras, List.mem_cons, List.not_mem_nil, or_false] at *; tauto)
  refine ⟨⟨?_, hwork .observed (by simp), hwork .swapTemp (by simp),
    hwork .residual (by simp), hwork .right (by simp)⟩,
    hwork .inner (by simp), hwork .outer (by simp), hwork .savedCount (by simp)⟩
  refine ⟨?_, ?_, ?_, ?_, hsrc⟩
  · rw [scanHeader_numeric_extra s .payload (by decide)]; exact hs.numeric.1
  · rw [scanHeader_numeric_extra s .work (by decide)]; exact hs.numeric.2.1
  · rw [scanHeader_numeric_extra s .output (by decide)]; exact hs.numeric.2.2.1
  · rw [scanHeader_numeric_extra s .cap (by decide)]; exact hs.numeric.2.2.2.1

def unaryScanPrefixRoutine (mode : UnaryVisitMode) (bump : F → Bool → F) :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState F) :=
  RoutineComposition.seq scanHeaderRoutine (unaryRowsRoutine scanRowsPorts mode bump)

def unaryScanPrefixEval (mode : UnaryVisitMode) (bump : F → Bool → F) (C : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) :=
  unaryRowsEval scanRowsPorts mode bump C (scanHeaderEval s)

def unaryScanPrefixBound (C L : ℕ) := 9 * L + 16 + unaryRowsBound C L

theorem unaryScanPrefix_executes (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    ∃ n ≤ unaryScanPrefixBound C L,
      (unaryScanPrefixRoutine mode bump).Executes s (unaryScanPrefixEval mode bump C s) n ∧
      UnaryRowsInv scanVisitPorts .inner C L (unaryScanPrefixEval mode bump C s) := by
  obtain ⟨n, hn, hhead, ho, hsrc, hN, hM, hK⟩ := scanHeader_executes C L s hs
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  obtain ⟨m, hm, hrows, hout, hg, hclear⟩ := unaryRows_executes scanRowsPorts mode bump C L
    (scanHeaderEval s) hi hc hd hz
  exact ⟨n + m, by unfold unaryScanPrefixBound; omega,
    RoutineComposition.seq_executes scanHeaderRoutine (unaryRowsRoutine scanRowsPorts mode bump) hhead hrows, hout⟩

def unaryScanReadFold (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C : ℕ) (acc : F) (bits : List Bool) : Option (List Bool × F) :=
  match readInternalHeaderPrefix bits with
  | none => none
  | some (_, rest) => (readFramedList (readFramedList readUnaryFrame) rest).map
      (fun z => (z.2, z.1.foldl (fun a row => row.foldl (unaryVisitStep mode bump C) a) acc))

theorem unaryScanPrefix_observation (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    unaryVisitObservation (unaryScanPrefixEval mode bump C s) =
      unaryScanReadFold mode bump C s.state.1.1 (s.stk (.inr .original)) := by
  obtain ⟨n, hn, he, ho, hsrc, hN, hM, hK⟩ := scanHeader_executes C L s hs
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  rw [unaryScanPrefixEval, unaryRows_observation scanRowsPorts mode bump C L (scanHeaderEval s) hi hc]
  have hframe := copiedHeader_frame (.inr .original : NumericStack UnaryScanPort) scanHeaderPorts s
  have hf : (scanHeaderEval s).state.1.1 = s.state.1.1 := congrArg Prod.fst hframe
  cases hp : readInternalHeaderPrefix (s.stk (.inr .original)) with
  | none =>
      have hflag : (scanHeaderEval s).state.2 = false := by
        cases hh : (scanHeaderEval s).state.2 <;> simp [internalHeaderObservation, hh, hp] at ho ⊢
      simp [unaryScanReadFold, hp, hflag]
  | some z =>
      rcases z with ⟨⟨N, M, K⟩, rest⟩
      have hflag : (scanHeaderEval s).state.2 = true := by
        cases hh : (scanHeaderEval s).state.2 <;> simp [internalHeaderObservation, hh, hp] at ho ⊢
      have hrest : (scanHeaderEval s).stk (.inl .source) = rest := by
        simpa [internalHeaderObservation, hflag, hp, scanHeaderPorts] using congrArg (Option.map Prod.snd) ho
      simp only [hflag, ↓reduceIte, hrest, hf, unaryScanReadFold, hp]

theorem unaryScanPrefix_record_preserved (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    (unaryScanPrefixEval mode bump C s).stk (.inr .original) = s.stk (.inr .original) := by
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  rw [unaryScanPrefixEval, unaryRows_extra scanRowsPorts .original (by decide) (by decide) (by decide)
    mode bump C L (scanHeaderEval s) hi hc]
  exact scanHeader_extra s .original (by decide) (by decide) (by decide)

theorem unaryScanPrefix_queries_preserved (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    (unaryScanPrefixEval mode bump C s).stk (.inr .queries) = s.stk (.inr .queries) := by
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  rw [unaryScanPrefixEval, unaryRows_extra scanRowsPorts .queries (by decide) (by decide) (by decide)
    mode bump C L (scanHeaderEval s) hi hc]
  exact scanHeader_extra s .queries (by decide) (by decide) (by decide)

end PolytomyReductionModel
