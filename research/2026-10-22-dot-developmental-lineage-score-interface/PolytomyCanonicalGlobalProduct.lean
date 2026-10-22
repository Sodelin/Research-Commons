/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual physical copies of global N,m into the old arithmetic operands,
actual pinned multiplier call, exact result and preserved global data.
-/
import PolytomyCanonicalGlobalHeader

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def canonicalGlobalNumeric (s : CanonicalGlobalStore) := selectedCallerBase (canonicalGlobalBase s)

def globalProductPrepareEval (s : CanonicalGlobalStore) :=
  wordDuplicateEval (.inr .rowCount) (globalScanPort (.inr .headerM))
    (wordDuplicateEval (.inr .universe) (globalScanPort (.inl .cap)) s)

def globalProductPrepareRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq
    (wordDuplicateRoutine (.inr .universe) (globalScanPort (.inr .copyTemp)) (globalScanPort (.inl .cap)))
    (wordDuplicateRoutine (.inr .rowCount) (globalScanPort (.inr .copyTemp)) (globalScanPort (.inr .headerM)))

def globalProductCallRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  extraPortsRoutine (E := CanonicalGlobalPort)
    (extraPortsRoutine (E := CanonicalFilterPort)
      (preservingUnaryProductRoutine UnaryScanPort.headerM .swapTemp .savedCount .outer))

def canonicalGlobalProductRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq globalProductPrepareRoutine globalProductCallRoutine

def canonicalGlobalProductEval (C D : ℕ) (s : CanonicalGlobalStore) : CanonicalGlobalStore :=
  ⟨((s.state.1.1, false), true), Function.update
    (Function.update (Function.update s.stk (globalScanPort (.inl .cap)) (List.replicate C true))
      (globalScanPort (.inr .headerM)) (List.replicate D true))
    (globalScanPort (.inr .savedCount)) (List.replicate (C * D) true)⟩

theorem globalProductPrepare_executes (s : CanonicalGlobalStore)
    (ht : s.stk (globalScanPort (.inr .copyTemp)) = []) :
    globalProductPrepareRoutine.Executes s (globalProductPrepareEval s)
      (3 * (s.stk (.inr .universe)).length + 3 * (s.stk (.inr .rowCount)).length + 6) := by
  let u := wordDuplicateEval (.inr CanonicalGlobalPort.universe) (globalScanPort (.inl .cap)) s
  have h1 := wordDuplicate_executes (.inr CanonicalGlobalPort.universe : CanonicalGlobalStack)
    (globalScanPort (.inr .copyTemp)) (globalScanPort (.inl .cap))
    (by decide) (by decide) (by decide) s ht
  have hu : u.stk (globalScanPort (.inr .copyTemp)) = [] := by simp [u, wordDuplicateEval, globalScanPort, ht]
  have h2 := wordDuplicate_executes (.inr CanonicalGlobalPort.rowCount : CanonicalGlobalStack)
    (globalScanPort (.inr .copyTemp)) (globalScanPort (.inr .headerM))
    (by decide) (by decide) (by decide) u hu
  have hrow : u.stk (.inr .rowCount) = s.stk (.inr .rowCount) := by simp [u, wordDuplicateEval, globalScanPort]
  rw [hrow] at h2
  simpa only [globalProductPrepareRoutine, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using RoutineComposition.seq_executes _ _ h1 h2

theorem globalProductPrepared_numeric (C D L : ℕ) (s : CanonicalGlobalStore)
    (hs : NumericLoopInv 0 L (canonicalGlobalNumeric s))
    (hC : s.stk (.inr .universe) = List.replicate C true)
    (hD : s.stk (.inr .rowCount) = List.replicate D true) :
    NumericLoopInv C L (canonicalGlobalNumeric (globalProductPrepareEval s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort] using hs.1
  · simpa [canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort] using hs.2.1
  · simpa [canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort] using hs.2.2.1
  · have hcap : s.stk (globalScanPort (.inl .cap)) = [] := by simpa using hs.2.2.2.1
    simp [canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort, hC, hcap]
  · simpa [canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort] using hs.2.2.2.2

theorem canonicalGlobalProduct_executes (C D L : ℕ) (s : CanonicalGlobalStore)
    (hs : NumericLoopInv 0 L (canonicalGlobalNumeric s)) (hf : s.state.2 = true)
    (hC : s.stk (.inr .universe) = List.replicate C true)
    (hD : s.stk (.inr .rowCount) = List.replicate D true)
    (ht : s.stk (globalScanPort (.inr .copyTemp)) = [])
    (hm : s.stk (globalScanPort (.inr .headerM)) = [])
    (hswap : s.stk (globalScanPort (.inr .swapTemp)) = [])
    (hb : s.stk (globalScanPort (.inr .savedCount)) = [])
    (hd : s.stk (globalScanPort (.inr .outer)) = []) :
    ∃ n ≤ 3 * C * D + 6 * C + 15 * D + 18,
      canonicalGlobalProductRoutine.Executes s (canonicalGlobalProductEval C D s) n := by
  let p := globalProductPrepareEval s
  let u := canonicalGlobalNumeric p
  have hi := globalProductPrepared_numeric C D L s hs hC hD
  have hum : u.stk (.inr .headerM) = List.replicate D true := by
    simp [u, p, canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort, hD, hm]
  have hut : u.stk (.inr .swapTemp) = [] := by
    simpa [u, p, canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort] using hswap
  have hub : u.stk (.inr .savedCount) = [] := by
    simpa [u, p, canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort] using hb
  have hud : u.stk (.inr .outer) = [] := by
    simpa [u, p, canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
      globalProductPrepareEval, wordDuplicateEval, globalScanPort] using hd
  obtain ⟨n, hn, he⟩ := preservingUnaryProduct_store UnaryScanPort.headerM .swapTemp .savedCount .outer
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    C D L u hi hf hum hut hub hud
  have hl1 := extraPorts_executes (E := CanonicalFilterPort)
    (preservingUnaryProductRoutine UnaryScanPort.headerM .swapTemp .savedCount .outer)
    u (preservingProductStoreEval .savedCount C D u)
    (selectedCallerExtra (canonicalGlobalBase p)) n he
  have hl2 := extraPorts_executes (E := CanonicalGlobalPort) _ _ _ (canonicalGlobalExtra p) n hl1
  rw [selectedCaller_split, canonicalGlobal_split] at hl2
  have hcap : s.stk (globalScanPort (.inl .cap)) = [] := by simpa using hs.2.2.2.1
  have heff : extraPortsStore
      (extraPortsStore (preservingProductStoreEval .savedCount C D u) (selectedCallerExtra (canonicalGlobalBase p)))
      (canonicalGlobalExtra p) = canonicalGlobalProductEval C D s := by
    apply countdownStore_ext
    · rfl
    · funext k
      cases k with
      | inr k => simp [extraPortsStore, canonicalGlobalExtra, canonicalGlobalProductEval, globalScanPort,
          p, globalProductPrepareEval, wordDuplicateEval]
      | inl k =>
          cases k with
          | inr k => simp [extraPortsStore, selectedCallerExtra, canonicalGlobalBase,
              canonicalGlobalProductEval, globalScanPort, p, globalProductPrepareEval, wordDuplicateEval]
          | inl k =>
              cases k with
              | inl k => cases k <;> simp [extraPortsStore, preservingProductStoreEval, u, p,
                  canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
                  canonicalGlobalProductEval, globalProductPrepareEval, wordDuplicateEval, globalScanPort, hC, hcap]
              | inr k => cases k <;> simp [extraPortsStore, preservingProductStoreEval, u, p,
                  canonicalGlobalNumeric, selectedCallerBase, canonicalGlobalBase,
                  canonicalGlobalProductEval, globalProductPrepareEval, wordDuplicateEval, globalScanPort, hD, hm]
  rw [heff] at hl2
  have hp := globalProductPrepare_executes s ht
  rw [hC, hD, List.length_replicate, List.length_replicate] at hp
  have hall := RoutineComposition.seq_executes _ _ hp hl2
  exact ⟨(3 * C + 3 * D + 6) + n, by omega, hall⟩

theorem canonicalGlobalProduct_extra (C D : ℕ) (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (hc : k ≠ globalScanPort (.inl .cap)) (hm : k ≠ globalScanPort (.inr .headerM))
    (hb : k ≠ globalScanPort (.inr .savedCount)) :
    (canonicalGlobalProductEval C D s).stk k = s.stk k := by
  simp [canonicalGlobalProductEval, hc, hm, hb]

/- The multiplier now really reads caller-preserved original scalar
words through actual copies. Its product and both operands have explicit
physical locations; global N,m,K and every canonical output/cost tape
survive. Alphabet/marker construction and cleanup remain to join.
-/

end PolytomyReductionModel
