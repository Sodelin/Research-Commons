import Mathlib.Algebra.Order.Ring.Int
import Lean.Elab.Tactic.Omega

/-!
Actual-source interval/phase arithmetic for PRISM Sample_* call sites at
87a88715282d279fc361eb56de27153a321359be. Mathematical integer expressions
idealize source indices without overflow. This is not exhaustive coverage of
scaffold-border helper calls, total continuation fuel, or grammar/energy fidelity.
Call-stack height and total stochastic production count are different bounds.
-/
namespace E8TracebackCallRanks
inductive Kind
  | W | V | VM | WM | WMV | WMP | WMB | WMBW | WMBP
  | WI | WIP | VP | VPL | VPR | BE
  deriving DecidableEq

def phase : Kind → ℕ
  | .W => 4
  | .WM | .WMP | .WI | .WIP => 3
  | .WMV | .WMB => 2
  | .V | .WMBP => 1
  | .VM | .WMBW | .VP | .VPL | .VPR | .BE => 0

structure Call where
  kind : Kind
  i : ℤ
  j : ℤ

def rank (s : Call) : ℕ := 8 * (s.j - s.i).toNat + phase s.kind

theorem phase_lt_eight (k : Kind) : phase k < 8 := by
  cases k <;> decide

theorem rank_of_smaller_span (parent child : Call)
    (hpositive : 0 < parent.j - parent.i)
    (hsmaller : child.j - child.i < parent.j - parent.i) : rank child < rank parent := by
  have hp := phase_lt_eight parent.kind
  have hc := phase_lt_eight child.kind
  unfold rank
  omega

theorem rank_endpoint_stripping (kind : Kind) (i j j' : ℤ) (hj : j' ≤ j) :
    rank ⟨kind, i, j'⟩ ≤ rank ⟨kind, i, j⟩ := by
  change 8 * (j' - i).toNat + phase kind ≤ 8 * (j - i).toNat + phase kind
  omega

/-- These same-interval calls occur in the pinned source; not an exhaustive
relation for all recursive calls. -/
inductive Wrapper : Kind → Kind → Prop
  | w_v : Wrapper .W .V
  | w_wmb : Wrapper .W .WMB
  | wm_v : Wrapper .WM .V
  | wm_wmb : Wrapper .WM .WMB
  | wmv_v : Wrapper .WMV .V
  | wmp_wmb : Wrapper .WMP .WMB
  | wmb_wmbp : Wrapper .WMB .WMBP
  | wmbp_vp : Wrapper .WMBP .VP
  | wi_v : Wrapper .WI .V
  | wi_wmb : Wrapper .WI .WMB
  | wip_v : Wrapper .WIP .V
  | wip_wmb : Wrapper .WIP .WMB
  | v_vm : Wrapper .V .VM

theorem wrapper_rank_decreases {parent child : Kind} (i j : ℤ) (h : Wrapper parent child) :
    rank ⟨child, i, j⟩ < rank ⟨parent, i, j⟩ := by
  cases h <;> simp [rank, phase]

/-- Literal Sample_V inner-loop lower limit over mathematical integers. -/
def sampleVMinL (i j k turn maxloop : ℤ) : ℤ :=
  max (k + turn + 1 + maxloop + 2) (k + j - i) - maxloop - 2

theorem sampleV_loop_lower_bound (i j k turn maxloop : ℤ) :
    k + turn + 1 ≤ sampleVMinL i j k turn maxloop := by
  have h := le_max_left (k + turn + 1 + maxloop + 2) (k + j - i)
  unfold sampleVMinL
  omega

theorem sampleV_internal_rank (i j k l turn maxloop : ℤ)
    (hturn : 0 ≤ turn) (hk : i + 1 ≤ k)
    (hlower : sampleVMinL i j k turn maxloop ≤ l) (hupper : l ≤ j - 1) :
    rank ⟨.V, k, l⟩ < rank ⟨.V, i, j⟩ := by
  have hl := sampleV_loop_lower_bound i j k turn maxloop
  apply rank_of_smaller_span
  · change 0 < j - i
    omega
  · change l - k < j - i
    omega

theorem sampleVM_left_rank (i j k : ℤ) (hparent : i < j) (hk : k ≤ j) :
    rank ⟨.WM, i + 1, k - 1⟩ < rank ⟨.VM, i, j⟩ := by
  apply rank_of_smaller_span
  · change 0 < j - i
    omega
  · change (k - 1) - (i + 1) < j - i
    omega

theorem sampleVM_right_rank (i j k : ℤ) (hparent : i < j) (hk : i ≤ k) :
    rank ⟨.WMV, k, j - 1⟩ < rank ⟨.VM, i, j⟩ ∧
      rank ⟨.WMP, k, j - 1⟩ < rank ⟨.VM, i, j⟩ := by
  constructor <;> apply rank_of_smaller_span
  all_goals dsimp
  all_goals omega
end E8TracebackCallRanks
#print axioms E8TracebackCallRanks.rank_of_smaller_span
#print axioms E8TracebackCallRanks.wrapper_rank_decreases
#print axioms E8TracebackCallRanks.sampleV_loop_lower_bound
#print axioms E8TracebackCallRanks.sampleV_internal_rank
#print axioms E8TracebackCallRanks.sampleVM_left_rank
#print axioms E8TracebackCallRanks.sampleVM_right_rank
