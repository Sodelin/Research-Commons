/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Entire original source NORMALIZER as an actual multiport routine:
physical cap creation, original full prefix, suffix rejection, exact tagged
output and unconditional cleanup. Not the downstream reduction constructor.
-/
import PolytomyPartialCounterBounds

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def originalNormalizerRoutine (p : PrefixPorts K) (o : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (originalSourcePrefixRoutine p) (finishRoutine p o)

def originalNormalizerEval (p : PrefixPorts K) (o : K) (bits : List Bool)
    (base : K → List Bool) (frame : F) : CountdownStore (NumericStack K) F :=
  finishEval p o (originalSourcePrefixEval p bits base frame)

def originalNormalizerStepBound (L : ℕ) : ℕ :=
  6 * L ^ 4 + 30 * L ^ 3 + 79 * L ^ 2 + 140 * L + 146

theorem output_not_owned_iff (p : PrefixPorts K) (o : K) :
    (.inr o : NumericStack K) ∉ prefixOwned p ↔
      o ≠ p.r ∧ o ≠ p.c ∧ o ≠ p.d ∧ o ≠ p.b ∧ o ≠ p.t := by
  simp [prefixOwned, not_or]

theorem originalNormalizer_output (p : PrefixPorts K) (o : K)
    (ho : (.inr o : NumericStack K) ∉ prefixOwned p)
    (bits : List Bool) (base : K → List Bool) (hr : base p.r = []) (hout : base o = []) (frame : F) :
    (originalNormalizerEval p o bits base frame).stk (.inr o) = normalizedSource bits := by
  have hone := (output_not_owned_iff p o).mp ho
  have hempty : (originalSourcePrefixEval p bits base frame).stk (.inr o) = [] :=
    (originalSourcePrefix_extra p o hone.1 hone.2.1 hone.2.2.1 hone.2.2.2.1 hone.2.2.2.2 bits base frame).trans hout
  unfold originalNormalizerEval
  rw [finish_output p o ho _ hempty, originalSourcePrefix_observation]
  simpa only [hr, List.append_nil] using completedLog_original bits

theorem originalNormalizer_owned_clear (p : PrefixPorts K) (o : K) (k : NumericStack K)
    (hk : k ∈ prefixOwned p) (bits : List Bool) (base : K → List Bool) (frame : F) :
    (originalNormalizerEval p o bits base frame).stk k = [] :=
  finish_owned_clear p o k hk (originalSourcePrefixEval p bits base frame)

theorem originalNormalizer_frame (p : PrefixPorts K) (o : K)
    (bits : List Bool) (base : K → List Bool) (frame : F) :
    (originalNormalizerEval p o bits base frame).state.1.1 = frame := by
  unfold originalNormalizerEval
  rw [finish_frame, originalSourcePrefix_frame]

theorem originalNormalizer_extra (p : PrefixPorts K) (o k : K)
    (hk : (.inr k : NumericStack K) ∉ prefixOwned p) (hko : k ≠ o)
    (bits : List Bool) (base : K → List Bool) (frame : F) :
    (originalNormalizerEval p o bits base frame).stk (.inr k) = base k := by
  have hne := (output_not_owned_iff p k).mp hk
  unfold originalNormalizerEval
  rw [finish_outside p o (.inr k) hk (by simpa using hko)]
  exact originalSourcePrefix_extra p k hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2 bits base frame

/-- All-input operational normalizer with exact tagged output, explicit
    original-length polynomial bound and unconditional cleanup. The
    finite standalone-machine wrapper and downstream machines are separate. -/
theorem originalNormalizer_executes (p : PrefixPorts K) (o : K)
    (ho : (.inr o : NumericStack K) ∉ prefixOwned p)
    (bits : List Bool) (base : K → List Bool)
    (hr : base p.r = []) (hc : base p.c = []) (hd : base p.d = [])
    (hb : base p.b = []) (ht : base p.t = []) (hout : base o = [])
    (frame : F) (guard flag : Bool) :
    ∃ n ≤ originalNormalizerStepBound bits.length,
      (originalNormalizerRoutine p o).Executes
        (numericStore base (frame, guard) flag bits [] [] [] [])
        (originalNormalizerEval p o bits base frame) n ∧
      (originalNormalizerEval p o bits base frame).stk (.inr o) = normalizedSource bits ∧
      (∀ k ∈ prefixOwned p, (originalNormalizerEval p o bits base frame).stk k = []) ∧
      (originalNormalizerEval p o bits base frame).state.1.1 = frame := by
  let L := bits.length
  let s := originalSourcePrefixEval p bits base frame
  obtain ⟨n1, hn1, h1, hobs, hInv, hrec⟩ := originalSourcePrefix_executes
    p bits base hc hd hb ht frame guard flag
  have hi := preparedCaps_ready p bits base hc hd ht frame
  have hcounts := providedCapPrefix_counter_bounds p (L + 1) ((L + 1) ^ 2) L
    (preparedCapsStore p bits base frame) hi
  have hrec' : (s.stk (.inr p.r)).length ≤ L ^ 3 + 4 * L ^ 2 + 6 * L + 7 := by
    simpa only [hr, List.length_nil, Nat.zero_add] using hrec
  have hmass := prefixReturned_mass_bound p (L + 1) ((L + 1) ^ 2) L
    (L ^ 3 + 4 * L ^ 2 + 6 * L + 7) s hInv hcounts.1 hcounts.2 hrec'
  have hone := (output_not_owned_iff p o).mp ho
  obtain ⟨n2, hn2, h2⟩ := finish_executes p o (Ne.symm hone.1) ho s
  have hall := RoutineComposition.seq_executes (originalSourcePrefixRoutine p) (finishRoutine p o) h1 h2
  refine ⟨n1 + n2, ?_, hall, originalNormalizer_output p o ho bits base hr hout frame,
    fun k hk => originalNormalizer_owned_clear p o k hk bits base frame,
    originalNormalizer_frame p o bits base frame⟩
  rw [originalSourcePrefixStepBound_expansion] at hn1
  change n1 + n2 ≤ originalNormalizerStepBound L
  unfold originalNormalizerStepBound
  nlinarith

/- This closes the proposed actual ROUTINE normalizer component, including
malformed strings, zero counts/values, trailing garbage, partial logs and
failed counters. It does not close the ORIGINAL reduction constructor:
normalRecordConstructor still needs a concrete polynomial machine. The
independent checker, finite standalone wrapper/composition, compatible
closed encoded hardness and every kernel/dependency check remain open.
Original biological/general-DAG obligations remain open and unchanged.
-/

end PolytomyReductionModel
