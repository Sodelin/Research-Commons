import G1CanonicalOwnProtocolSignature

/-! Exact emitted blocks of the EXISTING finite promotion algorithm. The
fuel bound counts nonempty safe blocks and literal own interfaces; it is
derived from the operation-list length rather than a supplied trace. -/
namespace G1ActualOwnerBlockEmission
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

def safeBlockCost (ops : List (AsyncOperation I S Base)) : ℕ := if ops = [] then 0 else 1

noncomputable def emittedSafeBlock (owner : I) (ops : List (AsyncOperation I S Base)) :
    List (AsyncOperation I S Base) :=
  if ops = [] then [] else
    .localStep owner (actorWordKernel (ownerKernels owner ops)) :: outsideOperations owner ops

lemma safe_block_cost_le_length (ops : List (AsyncOperation I S Base)) : safeBlockCost ops ≤ ops.length := by
  cases ops <;> simp [safeBlockCost]

lemma take_safe_prefix_own_interface (owner : I) (first : List (AsyncOperation I S Base))
    (hs : ∀ op ∈ first, InteriorSafe owner op) (kernel : Base × S → PMF (Base × S))
    (later : List (AsyncOperation I S Base)) :
    (first ++ .interface owner kernel :: later).takeWhile (fun op => decide (InteriorSafe owner op)) = first := by
  induction first with
  | nil => simp [InteriorSafe]
  | cons op first ih =>
    have ho := hs op List.mem_cons_self
    have ht := fun q hq => hs q (List.mem_cons_of_mem op hq)
    simpa [ho] using ih ht

lemma drop_safe_prefix_own_interface (owner : I) (first : List (AsyncOperation I S Base))
    (hs : ∀ op ∈ first, InteriorSafe owner op) (kernel : Base × S → PMF (Base × S))
    (later : List (AsyncOperation I S Base)) :
    (first ++ .interface owner kernel :: later).dropWhile (fun op => decide (InteriorSafe owner op)) =
      .interface owner kernel :: later := by
  induction first with
  | nil => simp [InteriorSafe]
  | cons op first ih =>
    have ho := hs op List.mem_cons_self
    have ht := fun q hq => hs q (List.mem_cons_of_mem op hq)
    simpa [ho] using ih ht

lemma take_all_safe (owner : I) (ops : List (AsyncOperation I S Base))
    (hs : ∀ op ∈ ops, InteriorSafe owner op) :
    ops.takeWhile (fun op => decide (InteriorSafe owner op)) = ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    have ho := hs op List.mem_cons_self
    simpa [ho] using ih (fun q hq => hs q (List.mem_cons_of_mem op hq))

lemma drop_all_safe (owner : I) (ops : List (AsyncOperation I S Base))
    (hs : ∀ op ∈ ops, InteriorSafe owner op) :
    ops.dropWhile (fun op => decide (InteriorSafe owner op)) = [] := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    have ho := hs op List.mem_cons_self
    simpa [ho] using ih (fun q hq => hs q (List.mem_cons_of_mem op hq))

lemma actual_emit_whole_safe_block (owner : I) (ops : List (AsyncOperation I S Base))
    (hs : ∀ op ∈ ops, InteriorSafe owner op) (fuel : ℕ) (hf : safeBlockCost ops ≤ fuel) :
    promoteOwnerBlocks owner fuel ops = emittedSafeBlock owner ops := by
  cases ops with
  | nil => cases fuel <;> rfl
  | cons op ops =>
    have ho := hs op List.mem_cons_self
    have hn : 1 ≤ fuel := by simpa [safeBlockCost] using hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [promoteOwnerBlocks,if_pos ho,
        take_all_safe owner (op::ops) hs,drop_all_safe owner (op::ops) hs]
      have he : promoteOwnerBlocks owner fuel ([] : List (AsyncOperation I S Base)) = [] := by cases fuel <;> rfl
      simpa [emittedSafeBlock,he]

lemma actual_emit_safe_prefix_and_interface (owner : I) (first : List (AsyncOperation I S Base))
    (hs : ∀ op ∈ first, InteriorSafe owner op) (kernel : Base × S → PMF (Base × S))
    (later : List (AsyncOperation I S Base)) (fuel : ℕ) (hf : safeBlockCost first + 1 ≤ fuel) :
    promoteOwnerBlocks owner fuel (first ++ .interface owner kernel :: later) =
      emittedSafeBlock owner first ++ .interface owner kernel ::
        promoteOwnerBlocks owner (fuel - (safeBlockCost first + 1)) later := by
  cases first with
  | nil =>
    have hn : 1 ≤ fuel := by simpa [safeBlockCost] using hf
    cases fuel with
    | zero => omega
    | succ fuel => simp [promoteOwnerBlocks,InteriorSafe,emittedSafeBlock,safeBlockCost]
  | cons op ops =>
    have ho := hs op List.mem_cons_self
    have hn : 2 ≤ fuel := by simpa [safeBlockCost] using hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
        have ht : (op :: (ops ++ .interface owner kernel :: later)).takeWhile
            (fun q => decide (InteriorSafe owner q)) = op::ops := by
          simpa only [List.cons_append] using take_safe_prefix_own_interface owner (op::ops) hs kernel later
        have hd : (op :: (ops ++ .interface owner kernel :: later)).dropWhile
            (fun q => decide (InteriorSafe owner q)) = .interface owner kernel :: later := by
          simpa only [List.cons_append] using drop_safe_prefix_own_interface owner (op::ops) hs kernel later
        rw [List.cons_append,promoteOwnerBlocks,if_pos ho]
        simp only [ht,hd]
        simp [promoteOwnerBlocks,InteriorSafe,emittedSafeBlock,safeBlockCost]

/-- Two actual own interfaces delimit exactly one meaningful fused word.
Outside chunks may emit only their empty-word identity when their original
owner kernel list is empty; no interface or exterior checkpoint is crossed. -/
theorem actual_two_interface_block_emission (owner : I)
    (before interior future : List (AsyncOperation I S Base))
    (hb : ∀ op ∈ before, InteriorSafe owner op)
    (hi : ∀ op ∈ interior, InteriorSafe owner op)
    (hf : ∀ op ∈ future, InteriorSafe owner op)
    (opening closing : Base × S → PMF (Base × S))
    (fuel : ℕ) (hbound : safeBlockCost before + 1 + safeBlockCost interior + 1 + safeBlockCost future ≤ fuel) :
    promoteOwnerBlocks owner fuel (before ++ .interface owner opening ::
      (interior ++ .interface owner closing :: future)) =
      emittedSafeBlock owner before ++ .interface owner opening ::
      (emittedSafeBlock owner interior ++ .interface owner closing :: emittedSafeBlock owner future) := by
  rw [actual_emit_safe_prefix_and_interface owner before hb opening _ fuel (by omega),
    actual_emit_safe_prefix_and_interface owner interior hi closing _ _ (by omega),
    actual_emit_whole_safe_block owner future hf _ (by omega)]

/-- The existing interpreter's own list-length fuel is sufficient; no
extra controller bound is assumed. -/
theorem actual_two_interface_length_fuel_emission (owner : I)
    (before interior future : List (AsyncOperation I S Base))
    (hb : ∀ op ∈ before, InteriorSafe owner op)
    (hi : ∀ op ∈ interior, InteriorSafe owner op)
    (hf : ∀ op ∈ future, InteriorSafe owner op)
    (opening closing : Base × S → PMF (Base × S)) :
    promoteOwnerBlocks owner (before ++ .interface owner opening ::
      (interior ++ .interface owner closing :: future)).length
      (before ++ .interface owner opening :: (interior ++ .interface owner closing :: future)) =
      emittedSafeBlock owner before ++ .interface owner opening ::
      (emittedSafeBlock owner interior ++ .interface owner closing :: emittedSafeBlock owner future) := by
  apply actual_two_interface_block_emission owner before interior future hb hi hf
  have hb := safe_block_cost_le_length before
  have hi := safe_block_cost_le_length interior
  have hf := safe_block_cost_le_length future
  simp only [List.length_append,List.length_cons]
  omega

#print axioms actual_two_interface_length_fuel_emission
end G1ActualOwnerBlockEmission
