/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Original input-length-derived physical caps and actual prefix composition.
The input word is restored bit-for-bit; success is initialized explicitly.
There is no supplied-cap assumption at this entry. Finish remains open.
-/
import PolytomyPhysicalCapSquare

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def prepareCapsStartOp : Op (NumericStack K) Bool (CountdownState F) :=
  .load (fun s => ((s.1.1, false), true))

def prepareCapsRoutine (p : PrefixPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine prepareCapsStartOp)
    (RoutineComposition.seq smallCapRoutine (capSquareRoutine p.b p.d))

def preparedCapsStore (p : PrefixPorts K) (bits : List Bool)
    (base : K → List Bool) (frame : F) : CountdownStore (NumericStack K) F :=
  numericStore (Function.update base p.b (List.replicate ((bits.length + 1) ^ 2) true))
    (frame, false) true bits [] (List.replicate (bits.length + 1) true) [] []

def prepareCapsStepBound (L : ℕ) : ℕ := 3 * (L + 1) ^ 2 + 9 * (L + 1) + 2 * L + 10

theorem prepareCaps_executes (p : PrefixPorts K) (bits : List Bool) (base : K → List Bool)
    (hb : base p.b = []) (hd : base p.d = []) (frame : F) (guard flag : Bool) :
    ∃ n ≤ prepareCapsStepBound bits.length,
      (prepareCapsRoutine p).Executes (numericStore base (frame, guard) flag bits [] [] [] [])
        (preparedCapsStore p bits base frame) n := by
  let s := numericStore base (frame, guard) flag bits [] [] [] []
  let u := numericStore base (frame, false) true bits [] [] [] []
  have h1 : (Atom.routine (prepareCapsStartOp (K := K) (F := F))).Executes s u 1 :=
    Atom.executes prepareCapsStartOp s
  have h2 := smallCap_executes bits base frame false true [] []
  obtain ⟨n, hn, h3⟩ := capSquare_executes p.b p.d (Ne.symm p.hdb)
    (bits.length + 1) bits.length bits (le_refl _) base hb hd frame false
  have h23 := RoutineComposition.seq_executes smallCapRoutine (capSquareRoutine p.b p.d) h2 h3
  have hall := RoutineComposition.seq_executes (Atom.routine prepareCapsStartOp)
    (RoutineComposition.seq smallCapRoutine (capSquareRoutine p.b p.d)) h1 h23
  refine ⟨1 + ((2 * bits.length + 3) + n), ?_, hall⟩
  unfold prepareCapsStepBound
  omega

theorem preparedCaps_ready (p : PrefixPorts K) (bits : List Bool) (base : K → List Bool)
    (hc : base p.c = []) (hd : base p.d = []) (ht : base p.t = []) (frame : F) :
    PrefixReady p (bits.length + 1) ((bits.length + 1) ^ 2) bits.length
      (preparedCapsStore p bits base frame) := by
  simp [PrefixReady, RowsReady, NumericLoopInv, preparedCapsStore, numericStore, numericStacks,
    p.hcb, p.hdb, Ne.symm p.hbt, hc, hd, ht]

def originalSourcePrefixRoutine (p : PrefixPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (prepareCapsRoutine p) (providedCapPrefixRoutine p)

def originalSourcePrefixEval (p : PrefixPorts K) (bits : List Bool)
    (base : K → List Bool) (frame : F) : CountdownStore (NumericStack K) F :=
  providedCapPrefixEval p (bits.length + 1) ((bits.length + 1) ^ 2)
    (preparedCapsStore p bits base frame)

def originalSourcePrefixStepBound (L : ℕ) : ℕ :=
  prepareCapsStepBound L + providedCapPrefixStepBound L (L + 1) ((L + 1) ^ 2)

theorem originalSourcePrefixStepBound_expansion (L : ℕ) :
    originalSourcePrefixStepBound L = 6 * L ^ 4 + 28 * L ^ 3 + 70 * L ^ 2 + 122 * L + 115 := by
  rw [originalSourcePrefixStepBound, originalPrefixStepBound_expansion]
  unfold prepareCapsStepBound
  ring

theorem originalSourcePrefix_observation (p : PrefixPorts K) (bits : List Bool)
    (base : K → List Bool) (frame : F) :
    numericListObservation p.r (originalSourcePrefixEval p bits base frame) =
      (parseSaturatedSourcePrefix bits.length bits).map
        (fun q => (q.2, (encodeUnaryRaw q.1).reverse ++ base p.r)) := by
  have h := providedCapPrefix_original_observation p bits.length (preparedCapsStore p bits base frame) rfl
  simpa only [originalSourcePrefixEval, preparedCapsStore, numericStore, numericStacks,
    Function.update_of_ne p.hrb] using h

/-- Entire original PREFIX execution now creates its physical caps from
    the input. Only owned scratch/counter/cache emptiness is assumed. -/
theorem originalSourcePrefix_executes (p : PrefixPorts K) (bits : List Bool)
    (base : K → List Bool) (hc : base p.c = []) (hd : base p.d = [])
    (hb : base p.b = []) (ht : base p.t = []) (frame : F) (guard flag : Bool) :
    ∃ n ≤ originalSourcePrefixStepBound bits.length,
      (originalSourcePrefixRoutine p).Executes
        (numericStore base (frame, guard) flag bits [] [] [] [])
        (originalSourcePrefixEval p bits base frame) n ∧
      numericListObservation p.r (originalSourcePrefixEval p bits base frame) =
        (parseSaturatedSourcePrefix bits.length bits).map
          (fun q => (q.2, (encodeUnaryRaw q.1).reverse ++ base p.r)) ∧
      PrefixReturned p (bits.length + 1) ((bits.length + 1) ^ 2) bits.length
        (originalSourcePrefixEval p bits base frame) ∧
      ((originalSourcePrefixEval p bits base frame).stk (.inr p.r)).length ≤
        (base p.r).length + bits.length ^ 3 + 4 * bits.length ^ 2 + 6 * bits.length + 7 := by
  obtain ⟨n1, hn1, h1⟩ := prepareCaps_executes p bits base hb hd frame guard flag
  have hi := preparedCaps_ready p bits base hc hd ht frame
  obtain ⟨n2, hn2, h2, ho, hfinal, hr⟩ := providedCapPrefix_original_executes
    p bits.length (preparedCapsStore p bits base frame) hi rfl
  have hall := RoutineComposition.seq_executes (prepareCapsRoutine p) (providedCapPrefixRoutine p) h1 h2
  refine ⟨n1 + n2, by unfold originalSourcePrefixStepBound; omega, hall,
    originalSourcePrefix_observation p bits base frame, hfinal, ?_⟩
  have hexp := originalPrefixRecordBound_expansion bits.length
  have hbase : ((preparedCapsStore p bits base frame).stk (.inr p.r)).length = (base p.r).length := by
    simp [preparedCapsStore, numericStore, numericStacks, p.hrb]
  rw [hbase] at hr
  change ((providedCapPrefixEval p (bits.length + 1) ((bits.length + 1) ^ 2)
    (preparedCapsStore p bits base frame)).stk (.inr p.r)).length ≤ _
  omega

theorem originalSourcePrefix_extra (p : PrefixPorts K) (k : K)
    (hkr : k ≠ p.r) (hkc : k ≠ p.c) (hkd : k ≠ p.d) (hkb : k ≠ p.b) (hkt : k ≠ p.t)
    (bits : List Bool) (base : K → List Bool) (frame : F) :
    (originalSourcePrefixEval p bits base frame).stk (.inr k) = base k := by
  unfold originalSourcePrefixEval
  rw [providedCapPrefix_extra p k hkr hkc hkd hkb hkt]
  simp [preparedCapsStore, numericStore, numericStacks, hkb]

theorem originalSourcePrefix_frame (p : PrefixPorts K) (bits : List Bool)
    (base : K → List Bool) (frame : F) :
    (originalSourcePrefixEval p bits base frame).state.1.1 = frame := by
  unfold originalSourcePrefixEval
  rw [providedCapPrefix_frame]
  rfl

/- Cap creation no longer remains an assumed physical precondition at
this actual original-prefix entry. The success flag is initialized by an
explicit atom, not by a theorem-only promise. Still missing: final-suffix
rejection, reversal/tagging, all owned-stack cleanup, standalone complete
normalizer and original downstream constructor/checker, compatible closed
hardness and every elaboration/kernel/dependency check. No new target.
-/

end PolytomyReductionModel
