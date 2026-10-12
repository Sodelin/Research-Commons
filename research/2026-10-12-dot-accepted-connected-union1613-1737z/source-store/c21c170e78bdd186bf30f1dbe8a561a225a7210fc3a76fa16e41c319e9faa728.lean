import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic

/-!
Once-for-all source-loop interface for SCFG2 run_w_final_exact_dp_schedule at
PKProbDesign 27afdd054272dbda8a74c8aad156970a44c23cd8, replay header f4b6ab09...
The callback-bearing loop is modeled with ordered runtime-normalized children,
zero initial totals, allowed/zero-local skips, and read-only within-cell chart.
A candidate-observer frame law preserves the semantic provider/allowed/weight
view. Then the entire scheduled loop matches its pure ordered reference for
ALL finite schedules and factor assignments. No semiring/associativity law is
needed for this frame theorem. Actual observer-frame, source schedule, weighted
RNA semantics, C++ extraction and machine arithmetic remain separate gates.
Prior invariant architecture: AFP Monad_Memo_DP DP_CRelVS/Bottom_Up_Computation.
-/
namespace E8ScheduledObserverFrame

variable {Item Deduction Value Aux : Type*}

structure SemanticView (Item Deduction Value : Type*) where
  provider : Item → List Deduction
  allowed : Deduction → Bool
  localWeight : Deduction → Value

structure CandidateEvent (Item Deduction Value : Type*) where
  parent : Item
  deduction : Deduction
  contribution : Value
  chart : Item → Value
  localWeight : Value

variable [Zero Value] [Add Value] [Mul Value] [DecidableEq Value]
    (children : Deduction → List Item)
    (view : Aux → SemanticView Item Deduction Value)
    (observe : Aux → CandidateEvent Item Deduction Value → Aux)

def orderedContribution (semantic : SemanticView Item Deduction Value)
    (chart : Item → Value) (d : Deduction) : Value :=
  (children d).foldl (fun total child => total * chart child) (semantic.localWeight d)

def pureScan (semantic : SemanticView Item Deduction Value) (chart : Item → Value)
    (pending : List Deduction) (initial : Value) : Value :=
  pending.foldl (fun total d =>
    if semantic.allowed d then
      if semantic.localWeight d = 0 then total
      else total + orderedContribution children semantic chart d
    else total) initial

def sourceScan (chart : Item → Value) (parent : Item) :
    List Deduction → Aux → Value → Aux × Value
  | [], aux, total => (aux, total)
  | d :: pending, aux, total =>
    if (view aux).allowed d then
      if (view aux).localWeight d = 0 then sourceScan chart parent pending aux total
      else
        let contribution := orderedContribution children (view aux) chart d
        let event := CandidateEvent.mk parent d contribution chart ((view aux).localWeight d)
        sourceScan chart parent pending (observe aux event) (total + contribution)
    else sourceScan chart parent pending aux total

/-- A frame condition concerns observable callback effects, not the desired
partition/probability conclusion. It must be verified for the actual context. -/
def ObserverFrame : Prop :=
  ∀ aux event, view (observe aux event) = view aux

theorem scan_contract (hframe : ObserverFrame view observe)
    (chart : Item → Value) (parent : Item) (pending : List Deduction)
    (aux : Aux) (initial : Value) :
    view (sourceScan children view observe chart parent pending aux initial).1 = view aux ∧
    (sourceScan children view observe chart parent pending aux initial).2 =
      pureScan children (view aux) chart pending initial := by
  induction pending generalizing aux initial with
  | nil => exact ⟨rfl, rfl⟩
  | cons d pending ih =>
    by_cases ha : (view aux).allowed d = true
    · by_cases hz : (view aux).localWeight d = 0
      · simpa only [sourceScan, pureScan, List.foldl_cons, ha, hz, if_true] using ih aux initial
      · let contribution := orderedContribution children (view aux) chart d
        let event := CandidateEvent.mk parent d contribution chart ((view aux).localWeight d)
        have hobs := hframe aux event
        have h := ih (observe aux event) (initial + contribution)
        rw [hobs] at h
        simpa only [sourceScan, pureScan, List.foldl_cons, ha, hz, if_true, if_false] using h
    · have haf : (view aux).allowed d = false := Bool.eq_false_iff.mpr ha
      simpa only [sourceScan, pureScan, List.foldl_cons, haf, Bool.false_eq_true, if_false] using ih aux initial

variable [DecidableEq Item]

def pureRun (semantic : SemanticView Item Deduction Value) :
    List Item → (Item → Value) → (Item → Value)
  | [], chart => chart
  | parent :: pending, chart =>
    let total := pureScan children semantic chart (semantic.provider parent) 0
    pureRun semantic pending (Function.update chart parent total)

def sourceRun : List Item → Aux → (Item → Value) → Aux × (Item → Value)
  | [], aux, chart => (aux, chart)
  | parent :: pending, aux, chart =>
    let scanned := sourceScan children view observe chart parent ((view aux).provider parent) aux 0
    sourceRun pending scanned.1 (Function.update chart parent scanned.2)

theorem scheduled_run_contract (hframe : ObserverFrame view observe)
    (schedule : List Item) (aux : Aux) (chart : Item → Value) :
    view (sourceRun children view observe schedule aux chart).1 = view aux ∧
    (sourceRun children view observe schedule aux chart).2 =
      pureRun children (view aux) schedule chart := by
  induction schedule generalizing aux chart with
  | nil => exact ⟨rfl, rfl⟩
  | cons parent pending ih =>
    let scanned := sourceScan children view observe chart parent ((view aux).provider parent) aux 0
    have hs := scan_contract children view observe hframe chart parent ((view aux).provider parent) aux 0
    change view scanned.1 = view aux ∧ scanned.2 = _ at hs
    have ht := ih scanned.1 (Function.update chart parent scanned.2)
    constructor
    · exact ht.1.trans hs.1
    · change (sourceRun children view observe pending scanned.1 (Function.update chart parent scanned.2)).2 =
        pureRun children (view aux) pending
          (Function.update chart parent (pureScan children (view aux) chart ((view aux).provider parent) 0))
      rw [ht.2, hs.1, hs.2]

end E8ScheduledObserverFrame
#print axioms E8ScheduledObserverFrame.scan_contract
#print axioms E8ScheduledObserverFrame.scheduled_run_contract
