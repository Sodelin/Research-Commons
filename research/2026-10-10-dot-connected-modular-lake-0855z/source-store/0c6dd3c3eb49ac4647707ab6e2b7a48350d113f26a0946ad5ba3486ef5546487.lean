import E8ScheduledObserverFrame
import Mathlib.Data.List.FinRange
import Lean.Elab.Tactic.Omega

/-!
Parametric finite scheduled-hypergraph interpreter correctness, not a cap
ladder. Items are indexed by their proposed schedule position; deductions and
ordered runtime-normalized children are arbitrary finite lists, with arbitrary
factor assignments. The structural prerequisite is that every child's index
is smaller than its parent's. The computed chart equals the complete finite
recurrence expansion and its unique solution. Together with the observer frame
contract, this applies once for all valid provider instances and parameters.
Actual SCFG2 all-input index/provider/observer laws, RNA multiplicity/energy,
C++ refinement and numerical semantics are separate required admissions.
Prior contract: AFP Monad_Memo_DP cached-value invariant and weighted-acyclic
hypergraph evaluation (Ponty-Saule); no new general DP principle is claimed.
-/
namespace E8ScheduledHypergraphCorrectness
open E8ScheduledObserverFrame

variable {Item Deduction Value : Type*}
variable [Zero Value] [Add Value] [Mul Value] [DecidableEq Value]
    (children : Deduction → List Item) (semantic : SemanticView Item Deduction Value)

private theorem ordered_fold_congr (items : List Item) (left right : Item → Value)
    (h : ∀ item ∈ items, left item = right item) (initial : Value) :
    items.foldl (fun total item => total * left item) initial =
      items.foldl (fun total item => total * right item) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    simp only [List.foldl_cons]
    rw [h item (List.mem_cons_self)]
    exact ih (fun child hc => h child (List.mem_cons_of_mem item hc)) _

theorem orderedContribution_congr (left right : Item → Value) (d : Deduction)
    (h : ∀ child ∈ children d, left child = right child) :
    orderedContribution children semantic left d = orderedContribution children semantic right d :=
  ordered_fold_congr (children d) left right h (semantic.localWeight d)

theorem pureScan_congr (left right : Item → Value) (pending : List Deduction)
    (h : ∀ d ∈ pending, ∀ child ∈ children d, left child = right child) (initial : Value) :
    pureScan children semantic left pending initial = pureScan children semantic right pending initial := by
  induction pending generalizing initial with
  | nil => rfl
  | cons d pending ih =>
    have hc := orderedContribution_congr children semantic left right d (h d List.mem_cons_self)
    have ht : ∀ d' ∈ pending, ∀ child ∈ children d', left child = right child :=
      fun d' hd' => h d' (List.mem_cons_of_mem d hd')
    by_cases ha : semantic.allowed d = true
    · by_cases hz : semantic.localWeight d = 0
      · simpa only [pureScan, List.foldl_cons, ha, hz, if_true] using ih ht initial
      · simpa only [pureScan, List.foldl_cons, ha, hz, if_true, if_false, hc] using
          ih ht (initial + orderedContribution children semantic right d)
    · have haf : semantic.allowed d = false := Bool.eq_false_iff.mpr ha
      simpa only [pureScan, List.foldl_cons, haf, Bool.false_eq_true, if_false] using ih ht initial

def cellValue (chart : Item → Value) (parent : Item) : Value :=
  pureScan children semantic chart (semantic.provider parent) 0

theorem cellValue_congr (left right : Item → Value) (parent : Item)
    (h : ∀ d ∈ semantic.provider parent, ∀ child ∈ children d, left child = right child) :
    cellValue children semantic left parent = cellValue children semantic right parent :=
  pureScan_congr children semantic left right (semantic.provider parent) h 0

def finiteExpansion : ℕ → Item → Value
  | 0, _ => 0
  | depth + 1, parent => cellValue children semantic (finiteExpansion depth) parent

/-- Operational dependency condition: only already computed cells are read. -/
def Topological : List Item → List Item → Prop
  | _, [] => True
  | completed, parent :: pending =>
      (∀ d ∈ semantic.provider parent, ∀ child ∈ children d, child ∈ completed) ∧
      Topological (parent :: completed) pending

variable [DecidableEq Item]

private theorem pureRun_invariant (reference : Item → Value)
    (completed pending : List Item) (chart : Item → Value)
    (hchart : ∀ item ∈ completed, chart item = reference item)
    (hequation : ∀ item ∈ pending, cellValue children semantic reference item = reference item)
    (htopo : Topological children semantic completed pending) :
    ∀ item ∈ completed ++ pending, pureRun children semantic pending chart item = reference item := by
  induction pending generalizing completed chart with
  | nil =>
    intro item hi
    exact hchart item (by simpa using hi)
  | cons parent pending ih =>
    have hc : cellValue children semantic chart parent = reference parent :=
      (cellValue_congr children semantic chart reference parent
        (fun d hd child hchild => hchart child (htopo.1 d hd child hchild))).trans
        (hequation parent List.mem_cons_self)
    have hupdated : ∀ item ∈ parent :: completed,
        (Function.update chart parent (cellValue children semantic chart parent)) item = reference item := by
      intro item hi
      by_cases heq : item = parent
      · subst item
        simp [hc]
      · have himem : item ∈ completed := (List.mem_cons.mp hi).resolve_left heq
        simp [Function.update_of_ne heq, hchart item himem]
    have hh := ih (parent :: completed)
      (Function.update chart parent (cellValue children semantic chart parent)) hupdated
      (fun item hi => hequation item (List.mem_cons_of_mem parent hi)) htopo.2
    intro item hi
    have himem : item ∈ (parent :: completed) ++ pending := by
      simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hi
    exact hh item himem

section IndexedGraph
variable {n : ℕ} (children : Deduction → List (Fin n))
    (semantic : SemanticView (Fin n) Deduction Value)

/-- Schedule-position law; it is not an assumption of the desired RNA result. -/
def EarlierChildren : Prop :=
  ∀ parent, ∀ d ∈ semantic.provider parent, ∀ child ∈ children d, child.val < parent.val

theorem expansion_stabilizes (hearlier : EarlierChildren children semantic)
    (depth : ℕ) (parent : Fin n) (hdepth : parent.val < depth) :
    finiteExpansion children semantic (depth + 1) parent =
      finiteExpansion children semantic depth parent := by
  induction depth generalizing parent with
  | zero => omega
  | succ depth ih =>
    simp only [finiteExpansion]
    apply cellValue_congr children semantic
    intro d hd child hchild
    apply ih child
    have hp := hearlier parent d hd child hchild
    omega

theorem fullExpansion_equation (hearlier : EarlierChildren children semantic) (parent : Fin n) :
    cellValue children semantic (finiteExpansion children semantic n) parent =
      finiteExpansion children semantic n parent :=
  expansion_stabilizes children semantic hearlier n parent parent.isLt

private theorem topological_of_coverage (hearlier : EarlierChildren children semantic)
    (completed pending : List (Fin n))
    (horder : pending.Pairwise (fun left right => left.val < right.val))
    (hcover : ∀ item : Fin n, item ∈ completed ++ pending) :
    Topological children semantic completed pending := by
  induction pending generalizing completed with
  | nil => trivial
  | cons parent pending ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    constructor
    · intro d hd child hchild
      have hlt := hearlier parent d hd child hchild
      have hm := hcover child
      simp only [List.mem_append, List.mem_cons] at hm
      rcases hm with hc | heq | ht
      · exact hc
      · subst child
        omega
      · have hgt := hhead child ht
        omega
    · apply ih (parent :: completed) htail
      intro item
      have hm := hcover item
      simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm

theorem indexed_schedule_topological (hearlier : EarlierChildren children semantic) :
    Topological children semantic [] (List.finRange n) := by
  apply topological_of_coverage children semantic hearlier
  · exact (List.pairwise_lt_finRange n).imp (fun h => h)
  · intro item
    simp

/-- The once-for-all pure scheduled interpreter theorem. No parameter or
sequence-length cap is fixed in its statement. -/
theorem scheduled_chart_eq_complete_expansion
    (hearlier : EarlierChildren children semantic) (parent : Fin n) :
    pureRun children semantic (List.finRange n) (fun _ => 0) parent =
      finiteExpansion children semantic n parent := by
  apply pureRun_invariant children semantic (finiteExpansion children semantic n) [] (List.finRange n)
    (fun _ => 0) (by simp) (fun item _ => fullExpansion_equation children semantic hearlier item)
    (indexed_schedule_topological children semantic hearlier)
  simp

/-- Acyclicity makes the finite recurrence solution unique. -/
theorem complete_expansion_unique (hearlier : EarlierChildren children semantic)
    (reference : Fin n → Value)
    (hequation : ∀ parent, cellValue children semantic reference parent = reference parent)
    (parent : Fin n) : finiteExpansion children semantic n parent = reference parent := by
  have hall : ∀ depth parent, parent.val < depth →
      finiteExpansion children semantic depth parent = reference parent := by
    intro depth
    induction depth with
    | zero => intro parent hp; omega
    | succ depth ih =>
      intro parent hp
      change cellValue children semantic (finiteExpansion children semantic depth) parent = reference parent
      rw [← hequation parent]
      apply cellValue_congr children semantic
      intro d hd child hchild
      apply ih child
      have hc := hearlier parent d hd child hchild
      omega
  exact hall n parent parent.isLt

variable {Aux : Type*} (view : Aux → SemanticView (Fin n) Deduction Value)
    (observe : Aux → CandidateEvent (Fin n) Deduction Value → Aux)

/-- Callback-bearing source-reference interpreter, all finite instances.
Actual SCFG2 source schedule and callback-frame proofs remain required. -/
theorem observed_scheduled_chart_correct (hframe : ObserverFrame view observe)
    (aux : Aux) (hearlier : EarlierChildren children (view aux)) (parent : Fin n) :
    (sourceRun children view observe (List.finRange n) aux (fun _ => 0)).2 parent =
      finiteExpansion children (view aux) n parent := by
  rw [(scheduled_run_contract children view observe hframe (List.finRange n) aux (fun _ => 0)).2]
  exact scheduled_chart_eq_complete_expansion children (view aux) hearlier parent

end IndexedGraph
end E8ScheduledHypergraphCorrectness
#print axioms E8ScheduledHypergraphCorrectness.expansion_stabilizes
#print axioms E8ScheduledHypergraphCorrectness.fullExpansion_equation
#print axioms E8ScheduledHypergraphCorrectness.indexed_schedule_topological
#print axioms E8ScheduledHypergraphCorrectness.scheduled_chart_eq_complete_expansion
#print axioms E8ScheduledHypergraphCorrectness.complete_expansion_unique
#print axioms E8ScheduledHypergraphCorrectness.observed_scheduled_chart_correct
