import E8SCFG2RuntimeChildAdapter
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
Source-specific all-family child-boundary interface for PKProbDesign
27afdd054272dbda8a74c8aad156970a44c23cd8, expand_basic.hh and the three
exact-generator overrides in generate_exact_basic.hh. The source enums and
normalizer are reused. This is one structural admission contract, not a new
engine or a claim that the old span-first schedule is a DAG on all cache keys.

SourceGuard records local loop/helper inequalities, rather than assuming the
desired child-predecessor conclusion. RuleFamily records the actual factory's
parent family. Their C++/parser/exact-generated-list refinement remains an
explicit obligation. These facts feed preserved-execution ROOT-carrier proof;
full RNA support, physical weights, outputs, floating arithmetic remain open.
Prior contracts: established weighted-hypergraph DP/AFP schedule invariants;
the concrete use here is the pinned generator's all57 ordered child schemas.
-/
namespace E8SCFG2ProviderBoundaryContract
open E8SCFG2RuntimeChildAdapter

def primary (nt : NonTerminal) (i j : ℤ) : ItemKey := ⟨nt, i, j, -1, -1⟩
def band (i j ip jp : ℤ) : ItemKey := ⟨.BE, i, j, ip, jp⟩

def recursiveVP (p : ItemKey) : NonTerminal :=
  if p.nonterminal = .VP_CLOSED then .VP_CLOSED
  else if p.nonterminal = .VP_DIRECT then .VP_DIRECT else .VP

def prefixSpan (nt : NonTerminal) (i k : ℤ) : List ItemKey :=
  if i < k then [primary nt i (k - 1)] else []
def optionalSpan (nt : NonTerminal) (i j : ℤ) : List ItemKey :=
  if i ≤ j then [primary nt i j] else []

/-- Ordered active children of the exact selected factory, including its
manual WMBP carrier overrides and the W(i,i) zero-child exception. -/
def sourceChildren (partner : ℤ → ℤ) (p : ItemKey) (r : RuleId) (s : RuleSplit) : List ItemKey :=
  match r with
  | .V_HAIRPIN | .WI_BASE_SINGLE | .WMB_EMPTY | .BE_BASE_SAMEPAIR | .VM_SCALE2 => []
  | .V_INTERNAL => [primary .V s.k s.l]
  | .V_VM => [primary .VM p.i p.j]
  | .W_EXTEND_UNPAIRED => if p.i = p.j then [] else [primary .W p.i (p.j-1)]
  | .WI_EXTEND_UNPAIRED => [primary .WI p.i (p.j-1)]
  | .WM_EXTEND_UNPAIRED => [primary .WM p.i (p.j-1)]
  | .WMv_EXTEND_UNPAIRED => [primary .WMv p.i (p.j-1)]
  | .WMp_EXTEND_UNPAIRED => [primary .WMp p.i (p.j-1)]
  | .WIP_EXTEND_UNPAIRED => [primary .WIP p.i (p.j-1)]
  | .W_SPLIT_V => prefixSpan .W p.i s.k ++ [primary .V s.k p.j]
  | .W_SPLIT_WMB => prefixSpan .W p.i s.k ++ [primary .WMB s.k p.j]
  | .WI_SPLIT_V => prefixSpan .WI p.i s.k ++ [primary .V s.k p.j]
  | .WI_SPLIT_WMB => prefixSpan .WI p.i s.k ++ [primary .WMB s.k p.j]
  | .WM_SPLIT_V => prefixSpan .WM p.i s.k ++ [primary .V s.k p.j]
  | .WM_SPLIT_WMB => prefixSpan .WM p.i s.k ++ [primary .WMB s.k p.j]
  | .WIP_SPLIT_V => prefixSpan .WIP p.i s.k ++ [primary .V s.k p.j]
  | .WIP_SPLIT_WMB => prefixSpan .WIP p.i s.k ++ [primary .WMB s.k p.j]
  | .W_ROOT_WMB_DECOMPOSITION =>
      [primary .W p.i (s.p-1), primary .WMB s.p s.k, primary .W (s.k+1) p.j]
  | .VM_SPLIT_WM_WMv => prefixSpan .WM (p.i+1) s.k ++ [primary .WMv s.k (p.j-1)]
  | .VM_SPLIT_WM_WMp => prefixSpan .WM (p.i+1) s.k ++ [primary .WMp s.k (p.j-1)]
  | .VM_SPLIT_WMp_BASE => [primary .WMp s.k (p.j-1)]
  | .WM_START_V | .WIP_BASEPAIR_V => [primary .V s.k p.j]
  | .WM_START_WMB | .WIP_BASEPAIR_WMB => [primary .WMB s.k p.j]
  | .WMv_STEM_V | .WIP_BASE_V => [primary .V p.i p.j]
  | .WMp_STEM_WMB | .WIP_BASE_WMB => [primary .WMB p.i p.j]
  | .VPL_SPLIT_VP => [primary .VP s.k p.j]
  | .VPR_SPLIT_VP_WIP => [primary .VP p.i s.k, primary .WIP (s.k+1) p.j]
  | .VPR_SPLIT_VP_BASEPAIR => [primary .VP p.i s.k]
  | .VP_WI_CASE1 | .VP_WI_CASE2 =>
      optionalSpan .WI (p.i+1) (s.p-1) ++ optionalSpan .WI (s.q+1) (p.j-1)
  | .VP_WI_CASE3 =>
      optionalSpan .WI (p.i+1) (s.p-1) ++ optionalSpan .WI (s.q+1) (s.k-1) ++
        optionalSpan .WI (s.l+1) (p.j-1)
  | .VP_STACK => [primary (recursiveVP p) (p.i+1) (p.j-1)]
  | .VP_INTERNAL_LOOP => [primary (recursiveVP p) s.k s.l]
  | .VP_WIP_VP_LEFT => [primary .WIP (p.i+1) (s.k-1), primary (recursiveVP p) s.k (p.j-1)]
  | .VP_VP_WIP_RIGHT => [primary (recursiveVP p) (p.i+1) s.k, primary .WIP (s.k+1) (p.j-1)]
  | .VP_WIP_VPR => [primary .WIP (p.i+1) (s.k-1), primary .VPR s.k (p.j-1)]
  | .VP_VPL_WIP => [primary .VPL (p.i+1) s.k, primary .WIP (s.k+1) (p.j-1)]
  | .BE_STACK =>
      let reset := p.i = p.ip ∧ p.j = p.jp
      [band (p.i+1) (p.j-1) (if reset then p.i+1 else p.ip) (if reset then p.j-1 else p.jp)]
  | .BE_INTERNAL_LOOP => [band s.k s.l p.ip p.jp]
  | .BE_WIP_WIP =>
      [primary .WIP (p.i+1) (s.k-1), band s.k s.l p.ip p.jp, primary .WIP (s.l+1) (p.j-1)]
  | .BE_WIP_BASEPAIR => [primary .WIP (p.i+1) (s.k-1), band s.k s.l p.ip p.jp]
  | .BE_BASEPAIR_WIP => [band s.k s.l p.ip p.jp, primary .WIP (s.l+1) (p.j-1)]
  | .WMBW_SPLIT_WMBP_WI => [primary .WMBP p.i s.k, primary .WI (s.k+1) p.j]
  | .WMBP_SPLIT_BE_WMBP_VP =>
      [band s.p s.q s.l (partner s.l), primary .WMBP p.i (s.k-1), primary .VP s.k p.j]
  | .WMBP_SPLIT_BE_WMBW_VP =>
      [band s.p s.q s.l (partner s.l), primary .WMBW p.i (s.k-1), primary .VP s.k p.j]
  | .WMBP_DIRECT_VP => [primary .VP_DIRECT p.i p.j]
  | .WMBP_SPLIT_BE_WI_VP =>
      [band p.i (partner p.i) s.k s.l] ++ optionalSpan .WI (s.k+1) (s.p-1) ++ [primary .VP s.p p.j]
  | .WMB_SPLIT_BE_WMBP_WI =>
      [band s.p p.j s.q s.l, primary .WMBP p.i s.k] ++ optionalSpan .WI (s.k+1) (s.l-1)
  | .WMB_DIRECT_WMBP => [primary .WMBP p.i p.j]

def phase : NonTerminal → ℕ
  | .VM => 0 | .V => 1 | .WMv => 2 | .VP_CLOSED => 3 | .VP => 4
  | .VP_DIRECT => 5 | .BE => 6 | .VPL => 7 | .VPR => 8 | .WMBP => 9
  | .WMBW => 10 | .WMB => 11 | .WMp => 12 | .WM => 13 | .WIP => 14
  | .WI => 15 | .W => 16

/-- Factory parent-family dispatch, with the public/closed/direct VP variants. -/
def RuleFamily (r : RuleId) (nt : NonTerminal) : Prop :=
  match r with
  | .V_HAIRPIN | .V_INTERNAL | .V_VM => nt = .V
  | .WI_BASE_SINGLE | .WI_SPLIT_V | .WI_SPLIT_WMB | .WI_EXTEND_UNPAIRED => nt = .WI
  | .W_EXTEND_UNPAIRED | .W_SPLIT_V | .W_SPLIT_WMB | .W_ROOT_WMB_DECOMPOSITION => nt = .W
  | .VM_SPLIT_WM_WMv | .VM_SPLIT_WM_WMp | .VM_SPLIT_WMp_BASE | .VM_SCALE2 => nt = .VM
  | .WMv_STEM_V | .WMv_EXTEND_UNPAIRED => nt = .WMv
  | .WMp_STEM_WMB | .WMp_EXTEND_UNPAIRED => nt = .WMp
  | .WM_START_V | .WM_START_WMB | .WM_SPLIT_V | .WM_SPLIT_WMB | .WM_EXTEND_UNPAIRED => nt = .WM
  | .WIP_BASE_V | .WIP_BASE_WMB | .WIP_SPLIT_V | .WIP_SPLIT_WMB |
      .WIP_BASEPAIR_V | .WIP_BASEPAIR_WMB | .WIP_EXTEND_UNPAIRED => nt = .WIP
  | .VPL_SPLIT_VP => nt = .VPL
  | .VPR_SPLIT_VP_WIP | .VPR_SPLIT_VP_BASEPAIR => nt = .VPR
  | .VP_WI_CASE1 | .VP_WI_CASE2 | .VP_WI_CASE3 | .VP_STACK | .VP_INTERNAL_LOOP |
      .VP_WIP_VP_LEFT | .VP_VP_WIP_RIGHT | .VP_WIP_VPR | .VP_VPL_WIP =>
        nt = .VP_CLOSED ∨ nt = .VP ∨ nt = .VP_DIRECT
  | .BE_BASE_SAMEPAIR | .BE_STACK | .BE_INTERNAL_LOOP | .BE_WIP_WIP |
      .BE_WIP_BASEPAIR | .BE_BASEPAIR_WIP => nt = .BE
  | .WMBW_SPLIT_WMBP_WI => nt = .WMBW
  | .WMBP_SPLIT_BE_WMBP_VP | .WMBP_SPLIT_BE_WMBW_VP | .WMBP_DIRECT_VP |
      .WMBP_SPLIT_BE_WI_VP => nt = .WMBP
  | .WMB_SPLIT_BE_WMBP_WI | .WMB_DIRECT_WMBP | .WMB_EMPTY => nt = .WMB

/-- Named local numeric obligations coming from literal split loops,
positive border upper bounds and the pseudoloop partner gate. They are not
the desired child-boundary conclusion or an all-child-DAG premise. -/
def SourceGuard (partner : ℤ → ℤ) (p : ItemKey) (r : RuleId) (s : RuleSplit) : Prop :=
  match r with
  | .V_INTERNAL | .VP_INTERNAL_LOOP => s.l < p.j
  | .W_SPLIT_V | .W_SPLIT_WMB | .WI_SPLIT_V | .WI_SPLIT_WMB |
      .WM_SPLIT_V | .WM_SPLIT_WMB | .WIP_SPLIT_V | .WIP_SPLIT_WMB |
      .WM_START_V | .WM_START_WMB => p.i ≤ s.k ∧ s.k ≤ p.j
  | .WIP_BASEPAIR_V | .WIP_BASEPAIR_WMB | .VPL_SPLIT_VP => p.i < s.k
  | .W_ROOT_WMB_DECOMPOSITION => s.p ≤ p.j ∧ s.k ≤ p.j ∧ p.i ≤ s.k
  | .VM_SPLIT_WM_WMv | .VM_SPLIT_WM_WMp => s.k ≤ p.j
  | .VPR_SPLIT_VP_WIP | .VPR_SPLIT_VP_BASEPAIR => p.i ≤ s.k ∧ s.k < p.j
  | .VP_WI_CASE1 | .VP_WI_CASE2 => s.p ≤ p.j
  | .VP_WI_CASE3 => s.p ≤ p.j ∧ s.k ≤ p.j
  | .VP_WIP_VP_LEFT | .VP_WIP_VPR => s.k ≤ p.j
  | .VP_VP_WIP_RIGHT | .VP_VPL_WIP => s.k < p.j
  | .BE_INTERNAL_LOOP | .BE_WIP_WIP | .BE_WIP_BASEPAIR | .BE_BASEPAIR_WIP => s.k ≤ p.j ∧ s.l < p.j
  | .WMBW_SPLIT_WMBP_WI => p.i < s.k ∧ s.k < p.j
  | .WMBP_SPLIT_BE_WMBP_VP | .WMBP_SPLIT_BE_WMBW_VP => p.i < s.k ∧ s.k ≤ p.j ∧ s.q ≤ p.j
  | .WMBP_SPLIT_BE_WI_VP => p.i < s.p ∧ s.p ≤ p.j ∧ partner p.i ≤ p.j
  | .WMB_SPLIT_BE_WMBP_WI => s.k < p.j ∧ s.l ≤ p.j
  | _ => True

def RightProgress (p c : ItemKey) : Prop :=
  c.j < p.j ∨ (c.j = p.j ∧
    (c.nonterminal = .BE ∨ p.i < c.i ∨ phase c.nonterminal < phase p.nonterminal))

private theorem raw_source_child_progress (partner : ℤ → ℤ) (p : ItemKey)
    (r : RuleId) (s : RuleSplit) (hf : RuleFamily r p.nonterminal)
    (hg : SourceGuard partner p r s) (c : ItemKey) (hc : c ∈ sourceChildren partner p r s) :
    RightProgress p c := by
  cases r <;>
    simp_all [sourceChildren, SourceGuard, RuleFamily, prefixSpan, optionalSpan, primary, band,
      RightProgress, phase, List.mem_append, List.mem_cons, List.mem_singleton]
  all_goals
    repeat' first
    | split at hc
    | (rcases hc with hc | hc)
    | (rcases hc with ⟨h, hc⟩)
    | subst c
  all_goals simp_all [primary, band, RightProgress, phase]
  all_goals omega

def normalizedChildren (partner : ℤ → ℤ) (p : ItemKey) (r : RuleId) (s : RuleSplit) : List ItemKey :=
  (sourceChildren partner p r s).map (forwardChildKey r)

private theorem forward_coordinates (r : RuleId) (c : ItemKey) :
    (forwardChildKey r c).i = c.i ∧ (forwardChildKey r c).j = c.j := by
  unfold forwardChildKey
  split <;> exact ⟨rfl,rfl⟩

private theorem forward_phase_le (r : RuleId) (c : ItemKey) :
    phase (forwardChildKey r c).nonterminal ≤ phase c.nonterminal := by
  by_cases h : aliasesDirect r c
  · simp [forwardChildKey, h, h.2, phase]
  · simp [forwardChildKey, h]

private theorem forward_band_preserved (r : RuleId) (c : ItemKey) (h : c.nonterminal = .BE) :
    (forwardChildKey r c).nonterminal = .BE := by
  have hn : ¬aliasesDirect r c := by
    intro ha
    have he := ha.2
    rw [h] at he
    cases he
  simp [forwardChildKey, hn, h]

/-- All seventeen parent families / fifty-seven source RuleIds. No raw span
containment of BE is inferred, and no new schedule is adopted. -/
theorem source_normalized_child_progress (partner : ℤ → ℤ) (p : ItemKey)
    (r : RuleId) (s : RuleSplit) (hf : RuleFamily r p.nonterminal)
    (hg : SourceGuard partner p r s) (c : ItemKey) (hc : c ∈ normalizedChildren partner p r s) :
    RightProgress p c := by
  obtain ⟨raw, hm, rfl⟩ := List.mem_map.mp hc
  have hh := raw_source_child_progress partner p r s hf hg raw hm
  have hi := (forward_coordinates r raw).1
  have hj := (forward_coordinates r raw).2
  have hp := forward_phase_le r raw
  rcases hh with hlt | ⟨heq, hb | hs | hphase⟩
  · exact Or.inl (hj ▸ hlt)
  · exact Or.inr ⟨hj.trans heq, Or.inl (forward_band_preserved r raw hb)⟩
  · exact Or.inr ⟨hj.trans heq, Or.inr (Or.inl (hi ▸ hs))⟩
  · exact Or.inr ⟨hj.trans heq, Or.inr (Or.inr (lt_of_le_of_lt hp hphase))⟩

theorem source_normalized_child_right_bound (partner : ℤ → ℤ) (p : ItemKey)
    (r : RuleId) (s : RuleSplit) (hf : RuleFamily r p.nonterminal)
    (hg : SourceGuard partner p r s) (c : ItemKey) (hc : c ∈ normalizedChildren partner p r s) :
    c.j ≤ p.j := by
  rcases source_normalized_child_progress partner p r s hf hg c hc with h | h
  · exact le_of_lt h
  · exact le_of_eq h.1

end E8SCFG2ProviderBoundaryContract
#print axioms E8SCFG2ProviderBoundaryContract.source_normalized_child_progress
#print axioms E8SCFG2ProviderBoundaryContract.source_normalized_child_right_bound
