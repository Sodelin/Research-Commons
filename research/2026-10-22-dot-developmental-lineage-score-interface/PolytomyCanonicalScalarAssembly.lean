/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual five restoring copies and four constant bit pushes create the
alphabet, marker threshold and outer countdown from physical N,m,Nm.
-/
import PolytomyCanonicalGlobalProduct

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def pushThreeTrueRoutine (k : CanonicalGlobalStack) :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (Atom.routine (prependBitOp k true))
    (RoutineComposition.seq (Atom.routine (prependBitOp k true)) (Atom.routine (prependBitOp k true)))

def pushThreeTrueEval (k : CanonicalGlobalStack) (s : CanonicalGlobalStore) :=
  (prependBitOp k true).apply ((prependBitOp k true).apply ((prependBitOp k true).apply s))

theorem pushThreeTrue_executes (k : CanonicalGlobalStack) (s : CanonicalGlobalStore) :
    (pushThreeTrueRoutine k).Executes s (pushThreeTrueEval k s) 3 := by
  exact RoutineComposition.seq_executes _ _ (Atom.executes _ s)
    (RoutineComposition.seq_executes _ _ (Atom.executes _ _) (Atom.executes _ _))

def globalScalarStage1 (s : CanonicalGlobalStore) := wordDuplicateEval (.inr .universe) (.inr .alphabet) s
def globalScalarStage2 (s : CanonicalGlobalStore) := wordDuplicateEval (globalScanPort (.inr .savedCount)) (.inr .alphabet) (globalScalarStage1 s)
def globalScalarStage3 (s : CanonicalGlobalStore) := pushThreeTrueEval (.inr .alphabet) (globalScalarStage2 s)
def globalScalarStage4 (s : CanonicalGlobalStore) := wordDuplicateEval (.inr .universe) (.inr .markerThreshold) (globalScalarStage3 s)
def globalScalarStage5 (s : CanonicalGlobalStore) := wordDuplicateEval (globalScanPort (.inr .savedCount)) (.inr .markerThreshold) (globalScalarStage4 s)
def globalScalarStage6 (s : CanonicalGlobalStore) := (prependBitOp (.inr .markerThreshold) true).apply (globalScalarStage5 s)
def canonicalScalarAssemblyEval (s : CanonicalGlobalStore) := wordDuplicateEval (.inr .rowCount) (.inr .blockCounter) (globalScalarStage6 s)

def canonicalScalarAssemblyRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (wordDuplicateRoutine (.inr .universe) (globalScanPort (.inr .copyTemp)) (.inr .alphabet))
  (RoutineComposition.seq (wordDuplicateRoutine (globalScanPort (.inr .savedCount)) (globalScanPort (.inr .copyTemp)) (.inr .alphabet))
  (RoutineComposition.seq (pushThreeTrueRoutine (.inr .alphabet))
  (RoutineComposition.seq (wordDuplicateRoutine (.inr .universe) (globalScanPort (.inr .copyTemp)) (.inr .markerThreshold))
  (RoutineComposition.seq (wordDuplicateRoutine (globalScanPort (.inr .savedCount)) (globalScanPort (.inr .copyTemp)) (.inr .markerThreshold))
  (RoutineComposition.seq (Atom.routine (prependBitOp (.inr .markerThreshold) true))
    (wordDuplicateRoutine (.inr .rowCount) (globalScanPort (.inr .copyTemp)) (.inr .blockCounter)))))))

theorem canonicalScalarAssembly_executes (C D P : ℕ) (s : CanonicalGlobalStore)
    (hC : s.stk (.inr .universe) = List.replicate C true)
    (hD : s.stk (.inr .rowCount) = List.replicate D true)
    (hP : s.stk (globalScanPort (.inr .savedCount)) = List.replicate P true)
    (ht : s.stk (globalScanPort (.inr .copyTemp)) = []) :
    canonicalScalarAssemblyRoutine.Executes s (canonicalScalarAssemblyEval s) (6 * C + 6 * P + 3 * D + 19) := by
  have h1 := wordDuplicate_executes (.inr CanonicalGlobalPort.universe : CanonicalGlobalStack)
    (globalScanPort (.inr .copyTemp)) (.inr .alphabet) (by decide) (by decide) (by decide) s ht
  rw [hC, List.length_replicate] at h1
  have ht1 : (globalScalarStage1 s).stk (globalScanPort (.inr .copyTemp)) = [] := by
    simp [globalScalarStage1, wordDuplicateEval, globalScanPort, ht]
  have h2 := wordDuplicate_executes (globalScanPort (.inr .savedCount)) (globalScanPort (.inr .copyTemp))
    (.inr .alphabet) (by decide) (by decide) (by decide) (globalScalarStage1 s) ht1
  have h2' : (wordDuplicateRoutine (globalScanPort (.inr .savedCount)) (globalScanPort (.inr .copyTemp))
      (.inr .alphabet)).Executes (globalScalarStage1 s) (globalScalarStage2 s) (3 * P + 3) := by
    simpa [globalScalarStage1, wordDuplicateEval, globalScanPort, hP] using h2
  have h3 := pushThreeTrue_executes (.inr .alphabet) (globalScalarStage2 s)
  have ht3 : (globalScalarStage3 s).stk (globalScanPort (.inr .copyTemp)) = [] := by
    simp [globalScalarStage3, globalScalarStage2, globalScalarStage1, pushThreeTrueEval,
      prependBitOp, Op.apply, wordDuplicateEval, globalScanPort, ht]
  have h4 := wordDuplicate_executes (.inr CanonicalGlobalPort.universe : CanonicalGlobalStack)
    (globalScanPort (.inr .copyTemp)) (.inr .markerThreshold) (by decide) (by decide) (by decide)
    (globalScalarStage3 s) ht3
  have h4' : (wordDuplicateRoutine (.inr CanonicalGlobalPort.universe : CanonicalGlobalStack)
      (globalScanPort (.inr .copyTemp)) (.inr .markerThreshold)).Executes
      (globalScalarStage3 s) (globalScalarStage4 s) (3 * C + 3) := by
    simpa [globalScalarStage3, globalScalarStage2, globalScalarStage1, pushThreeTrueEval,
      prependBitOp, Op.apply, wordDuplicateEval, globalScanPort, hC] using h4
  have ht4 : (globalScalarStage4 s).stk (globalScanPort (.inr .copyTemp)) = [] := by
    simpa [globalScalarStage4, wordDuplicateEval, globalScanPort] using ht3
  have h5 := wordDuplicate_executes (globalScanPort (.inr .savedCount)) (globalScanPort (.inr .copyTemp))
    (.inr .markerThreshold) (by decide) (by decide) (by decide) (globalScalarStage4 s) ht4
  have h5' : (wordDuplicateRoutine (globalScanPort (.inr .savedCount)) (globalScanPort (.inr .copyTemp))
      (.inr .markerThreshold)).Executes (globalScalarStage4 s) (globalScalarStage5 s) (3 * P + 3) := by
    simpa [globalScalarStage4, globalScalarStage3, globalScalarStage2, globalScalarStage1,
      pushThreeTrueEval, prependBitOp, Op.apply, wordDuplicateEval, globalScanPort, hP] using h5
  have h6 := Atom.executes (prependBitOp (.inr CanonicalGlobalPort.markerThreshold : CanonicalGlobalStack) true)
    (globalScalarStage5 s)
  have ht6 : (globalScalarStage6 s).stk (globalScanPort (.inr .copyTemp)) = [] := by
    simpa [globalScalarStage6, globalScalarStage5, prependBitOp, Op.apply, wordDuplicateEval, globalScanPort] using ht4
  have h7 := wordDuplicate_executes (.inr CanonicalGlobalPort.rowCount : CanonicalGlobalStack)
    (globalScanPort (.inr .copyTemp)) (.inr .blockCounter) (by decide) (by decide) (by decide)
    (globalScalarStage6 s) ht6
  have h7' : (wordDuplicateRoutine (.inr CanonicalGlobalPort.rowCount : CanonicalGlobalStack)
      (globalScanPort (.inr .copyTemp)) (.inr .blockCounter)).Executes
      (globalScalarStage6 s) (canonicalScalarAssemblyEval s) (3 * D + 3) := by
    simpa [globalScalarStage6, globalScalarStage5, globalScalarStage4, globalScalarStage3,
      globalScalarStage2, globalScalarStage1, pushThreeTrueEval, prependBitOp, Op.apply,
      wordDuplicateEval, globalScanPort, hD] using h7
  have hall := RoutineComposition.seq_executes _ _ h1
    (RoutineComposition.seq_executes _ _ h2' (RoutineComposition.seq_executes _ _ h3
    (RoutineComposition.seq_executes _ _ h4' (RoutineComposition.seq_executes _ _ h5'
    (RoutineComposition.seq_executes _ _ h6 h7')))))
  convert hall using 1 <;> omega

theorem canonicalScalarAssembly_values (C D P : ℕ) (s : CanonicalGlobalStore)
    (hC : s.stk (.inr .universe) = List.replicate C true)
    (hD : s.stk (.inr .rowCount) = List.replicate D true)
    (hP : s.stk (globalScanPort (.inr .savedCount)) = List.replicate P true)
    (hA : s.stk (.inr .alphabet) = []) (hT : s.stk (.inr .markerThreshold) = [])
    (hB : s.stk (.inr .blockCounter) = []) :
    (canonicalScalarAssemblyEval s).stk (.inr .alphabet) = List.replicate (C + P + 3) true ∧
      (canonicalScalarAssemblyEval s).stk (.inr .markerThreshold) = List.replicate (C + P + 1) true ∧
      (canonicalScalarAssemblyEval s).stk (.inr .blockCounter) = List.replicate D true := by
  simp [canonicalScalarAssemblyEval, globalScalarStage6, globalScalarStage5, globalScalarStage4,
    globalScalarStage3, globalScalarStage2, globalScalarStage1, pushThreeTrueEval,
    prependBitOp, Op.apply, wordDuplicateEval, globalScanPort, hC, hD, hP, hA, hT, hB,
    capReplicate_append, List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem canonicalScalarAssembly_extra (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (hA : k ≠ .inr .alphabet) (hT : k ≠ .inr .markerThreshold) (hB : k ≠ .inr .blockCounter) :
    (canonicalScalarAssemblyEval s).stk k = s.stk k := by
  simp [canonicalScalarAssemblyEval, globalScalarStage6, globalScalarStage5, globalScalarStage4,
    globalScalarStage3, globalScalarStage2, globalScalarStage1, pushThreeTrueEval,
    prependBitOp, Op.apply, wordDuplicateEval, hA, hT, hB]

theorem canonicalScalarAssembly_state (s : CanonicalGlobalStore) :
    (canonicalScalarAssemblyEval s).state = s.state := rfl

/- C,D,P here describe actual input words; the previous real multiplier
supplies P=C*D. Header extraction, multiplication, this assembly and actual
old-work cleanup must be sequenced for complete physical initialization.
No scalar is allocated for free and no final machine is claimed here.
-/

end PolytomyReductionModel
