import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
Concrete SCFG2 runtime-child normalization adapter at PKProbDesign
27afdd054272dbda8a74c8aad156970a44c23cd8. Rule/nonterminal enums and key
validity are transcribed from the exact pinned public headers. Forward lookup
resets the aliased VP_DIRECT key's secondary coordinates; traceback only
changes its nonterminal. Valid active children force those coordinates to -1,
so both routes use the identical key. This is not C++ extraction, IEEE
arithmetic verification, grammar completeness, or physical energy fidelity.
-/
namespace E8SCFG2RuntimeChildAdapter

inductive NonTerminal
  | W
  | WI
  | V
  | VM
  | WMv
  | WMp
  | WM
  | WIP
  | VPL
  | VPR
  | VP_CLOSED
  | VP
  | VP_DIRECT
  | WMBW
  | WMBP
  | WMB
  | BE
  deriving DecidableEq

inductive RuleId
  | V_HAIRPIN
  | V_INTERNAL
  | V_VM
  | WI_BASE_SINGLE
  | WI_SPLIT_V
  | WI_SPLIT_WMB
  | WI_EXTEND_UNPAIRED
  | W_EXTEND_UNPAIRED
  | W_SPLIT_V
  | W_SPLIT_WMB
  | W_ROOT_WMB_DECOMPOSITION
  | VM_SPLIT_WM_WMv
  | VM_SPLIT_WM_WMp
  | VM_SPLIT_WMp_BASE
  | VM_SCALE2
  | WMv_STEM_V
  | WMp_STEM_WMB
  | WMv_EXTEND_UNPAIRED
  | WMp_EXTEND_UNPAIRED
  | WM_START_V
  | WM_START_WMB
  | WM_SPLIT_V
  | WM_SPLIT_WMB
  | WM_EXTEND_UNPAIRED
  | WIP_BASE_V
  | WIP_BASE_WMB
  | WIP_SPLIT_V
  | WIP_SPLIT_WMB
  | WIP_BASEPAIR_V
  | WIP_BASEPAIR_WMB
  | WIP_EXTEND_UNPAIRED
  | VPL_SPLIT_VP
  | VPR_SPLIT_VP_WIP
  | VPR_SPLIT_VP_BASEPAIR
  | VP_WI_CASE1
  | VP_WI_CASE2
  | VP_WI_CASE3
  | VP_STACK
  | VP_INTERNAL_LOOP
  | VP_WIP_VP_LEFT
  | VP_VP_WIP_RIGHT
  | VP_WIP_VPR
  | VP_VPL_WIP
  | WMBW_SPLIT_WMBP_WI
  | WMBP_SPLIT_BE_WMBP_VP
  | WMBP_SPLIT_BE_WMBW_VP
  | WMBP_DIRECT_VP
  | WMBP_SPLIT_BE_WI_VP
  | WMB_SPLIT_BE_WMBP_WI
  | WMB_DIRECT_WMBP
  | WMB_EMPTY
  | BE_BASE_SAMEPAIR
  | BE_STACK
  | BE_INTERNAL_LOOP
  | BE_WIP_WIP
  | BE_WIP_BASEPAIR
  | BE_BASEPAIR_WIP
  deriving DecidableEq

structure ItemKey where
  nonterminal : NonTerminal
  i : ℤ
  j : ℤ
  ip : ℤ
  jp : ℤ
  deriving DecidableEq

def ValidItemKey (key : ItemKey) : Prop :=
  1 ≤ key.i ∧ key.i ≤ key.j ∧
    if key.nonterminal = .BE then
      key.i ≤ key.ip ∧ key.ip < key.jp ∧ key.jp ≤ key.j
    else key.ip = -1 ∧ key.jp = -1

structure RuleSplit where
  k : ℤ
  l : ℤ
  p : ℤ
  q : ℤ
  deriving DecidableEq

structure Deduction where
  parent : ItemKey
  rule : RuleId
  split : RuleSplit
  children : Fin 3 → ItemKey
  child_count : ℕ

def ValidDeduction (d : Deduction) : Prop :=
  ValidItemKey d.parent ∧ d.child_count ≤ 3 ∧
    ∀ idx : Fin 3, idx.val < d.child_count → ValidItemKey (d.children idx)

def aliasesDirect (rule : RuleId) (child : ItemKey) : Prop :=
  rule = .WMBP_DIRECT_VP ∧ child.nonterminal = .VP_DIRECT

instance (rule : RuleId) (child : ItemKey) : Decidable (aliasesDirect rule child) :=
  inferInstanceAs (Decidable (rule = .WMBP_DIRECT_VP ∧ child.nonterminal = .VP_DIRECT))

/-- Key constructed by runtime_child_total_for_deduction. -/
def forwardChildKey (rule : RuleId) (child : ItemKey) : ItemKey :=
  if aliasesDirect rule child then
    ⟨.VP, child.i, child.j, -1, -1⟩
  else child

/-- Per-active-child update performed by runtime_traceback_deduction. -/
def tracebackChildKey (rule : RuleId) (child : ItemKey) : ItemKey :=
  if aliasesDirect rule child then { child with nonterminal := .VP } else child

def runtimeTracebackDeduction (d : Deduction) : Deduction :=
  { d with children := fun idx =>
      if idx.val < d.child_count then tracebackChildKey d.rule (d.children idx)
      else d.children idx }

theorem valid_primary_secondary_defaults (child : ItemKey)
    (hvalid : ValidItemKey child) (hprimary : child.nonterminal ≠ .BE) :
    child.ip = -1 ∧ child.jp = -1 := by
  simpa only [if_neg hprimary] using hvalid.2.2

theorem valid_child_normalization_agrees (rule : RuleId) (child : ItemKey)
    (hvalid : ValidItemKey child) :
    forwardChildKey rule child = tracebackChildKey rule child := by
  by_cases h : aliasesDirect rule child
  · have hprimary : child.nonterminal ≠ .BE := by
      rw [h.2]
      decide
    obtain ⟨hip, hjp⟩ := valid_primary_secondary_defaults child hvalid hprimary
    cases child
    simp_all [forwardChildKey, tracebackChildKey]
  · simp [forwardChildKey, tracebackChildKey, h]

theorem active_runtime_child_key_agrees (d : Deduction) (hvalid : ValidDeduction d)
    (idx : Fin 3) (hactive : idx.val < d.child_count) :
    forwardChildKey d.rule (d.children idx) = (runtimeTracebackDeduction d).children idx := by
  simp only [runtimeTracebackDeduction, if_pos hactive]
  exact valid_child_normalization_agrees d.rule (d.children idx) (hvalid.2.2 idx hactive)

theorem active_runtime_child_lookup_agrees {Value : Type*} (chart : ItemKey → Value)
    (d : Deduction) (hvalid : ValidDeduction d) (idx : Fin 3)
    (hactive : idx.val < d.child_count) :
    chart (forwardChildKey d.rule (d.children idx)) =
      chart ((runtimeTracebackDeduction d).children idx) := by
  rw [active_runtime_child_key_agrees d hvalid idx hactive]

/-- Array indices are traversed in source order, omitting inactive slots. -/
def orderedForwardValues {Value : Type*} (chart : ItemKey → Value) (d : Deduction) : List Value :=
  (List.finRange 3).filterMap fun idx =>
    if idx.val < d.child_count then some (chart (forwardChildKey d.rule (d.children idx))) else none

def orderedTracebackValues {Value : Type*} (chart : ItemKey → Value) (d : Deduction) : List Value :=
  (List.finRange 3).filterMap fun idx =>
    if idx.val < d.child_count then some (chart ((runtimeTracebackDeduction d).children idx)) else none

theorem ordered_runtime_values_agree {Value : Type*} (chart : ItemKey → Value)
    (d : Deduction) (hvalid : ValidDeduction d) :
    orderedForwardValues chart d = orderedTracebackValues chart d := by
  unfold orderedForwardValues orderedTracebackValues
  congr 1
  funext idx
  by_cases hactive : idx.val < d.child_count
  · simp only [if_pos hactive]
    congr 1
    exact active_runtime_child_lookup_agrees chart d hvalid idx hactive
  · simp only [if_neg hactive]

/-- The ordered lookup streams agree before applying any multiplication.
Even a non-associative accumulator operation sees identical arguments/order.
The theorem still does not assert extraction fidelity or float-law accuracy. -/
theorem ordered_runtime_fold_agrees {Value Accumulator : Type*}
    (chart : ItemKey → Value) (step : Accumulator → Value → Accumulator)
    (initial : Accumulator) (d : Deduction) (hvalid : ValidDeduction d) :
    (orderedForwardValues chart d).foldl step initial =
      (orderedTracebackValues chart d).foldl step initial := by
  rw [ordered_runtime_values_agree chart d hvalid]

/-- Exact mathematical contribution equality uses the same active-child list.
No assertion about rounded floating multiplication or local energy is hidden. -/
theorem active_runtime_product_agrees {Value : Type*} [CommMonoid Value]
    (chart : ItemKey → Value) (localWeight : Value) (d : Deduction) (hvalid : ValidDeduction d) :
    localWeight * (∏ idx ∈ (Finset.univ.filter (fun idx : Fin 3 => idx.val < d.child_count)),
      chart (forwardChildKey d.rule (d.children idx))) =
    localWeight * (∏ idx ∈ (Finset.univ.filter (fun idx : Fin 3 => idx.val < d.child_count)),
      chart ((runtimeTracebackDeduction d).children idx)) := by
  congr 1
  apply Finset.prod_congr rfl
  intro idx hidx
  exact active_runtime_child_lookup_agrees chart d hvalid idx (Finset.mem_filter.mp hidx).2

theorem runtime_metadata_preserved (d : Deduction) :
    (runtimeTracebackDeduction d).parent = d.parent ∧
    (runtimeTracebackDeduction d).rule = d.rule ∧
    (runtimeTracebackDeduction d).split = d.split ∧
    (runtimeTracebackDeduction d).child_count = d.child_count := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end E8SCFG2RuntimeChildAdapter

#print axioms E8SCFG2RuntimeChildAdapter.valid_primary_secondary_defaults
#print axioms E8SCFG2RuntimeChildAdapter.valid_child_normalization_agrees
#print axioms E8SCFG2RuntimeChildAdapter.active_runtime_child_key_agrees
#print axioms E8SCFG2RuntimeChildAdapter.active_runtime_child_lookup_agrees
#print axioms E8SCFG2RuntimeChildAdapter.ordered_runtime_values_agree
#print axioms E8SCFG2RuntimeChildAdapter.ordered_runtime_fold_agrees
#print axioms E8SCFG2RuntimeChildAdapter.active_runtime_product_agrees
#print axioms E8SCFG2RuntimeChildAdapter.runtime_metadata_preserved

