import LabelledOccurrenceReadout
import CanonicalSyntaxReceiver
import CodeBridge

/-! UNCOMPILED exact finite resolution SET and rational DISTINCT mean.
Resolution coordinates follow the queried ordered original four-tuple;
no sorted-quartet coordinate substitution or switching weighting is hidden. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open scoped Classical
open Nanuq.Source Nanuq.Quartet Nanuq.GraphReceiver Nanuq.AdjacentCertificate

def resolutionIndex : Resolution → Nat
  | .xy_zw => 0
  | .xz_yw => 1
  | .xw_yz => 2

def finiteResolutionSet (T : Tree) (tips : List Nat) (Q : Quartet) : Finset Resolution :=
  ({.xy_zw,.xz_yw,.xw_yz} : Finset Resolution).filter
    (fun r => ∃ e∈T.internalIntervals 1, edgeWitness tips e.1 e.2 Q (resolutionIndex r)=true)

theorem mem_finiteResolutionSet (T : Tree) (tips : List Nat) (Q : Quartet) (r : Resolution) :
    r∈finiteResolutionSet T tips Q ↔
      ∃ e∈T.internalIntervals 1, edgeWitness tips e.1 e.2 Q (resolutionIndex r)=true := by
  cases r <;> simp [finiteResolutionSet]

/-- Exact coordinates for a quartet actually stored at idx. No claim that
an arbitrary queried tuple is already the sorted quartetAt tuple. -/
theorem finiteResolutionSet_code (T : Tree) (tips : List Nat) (qs : List Quartet)
    (idx : Nat) (Q : Quartet) (hQ : qs[idx]?=some Q) (r : Resolution) :
    r∈finiteResolutionSet T tips Q ↔
      (Nanuq.AdjacentCertificate.code (T.summary (edgeContribution tips qs) 1) idx).testBit
        (resolutionIndex r)=true := by
  rw [mem_finiteResolutionSet]
  exact (Nanuq.Restriction.summary_code_edge T tips qs idx Q hQ (resolutionIndex r)
    (by cases r <;> decide)).symm

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hl : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e=N.leaf x)

theorem actual_distinct_set_and_mean_finite
    (code : X ↪ Nat) (lab : N.OpenedHybridVertex → Nat) (T : Tree) (tips : List Nat)
    (hlab : ∀ t, lab (N.openedTipVertex t)=code (N.openedTipLabel hl t))
    (hfinite : ∀ (Q : Quartet) (r a b c d : Nat), Q.parts r=(a,b,c,d) → a≠b → c≠d →
      (LabelledQuartet (N.openedHybridGraph hl) lab a b c d ↔
        ∃ e∈T.internalIntervals 1, edgeWitness tips e.1 e.2 Q r=true))
    (q : Fin 4 ↪ X) :
    N.rawDisplayedQuartets q=finiteResolutionSet T tips
      ⟨code (q 0),code (q 1),code (q 2),code (q 3)⟩ ∧
    N.rawQuartetMean q=distinctMean (finiteResolutionSet T tips
      ⟨code (q 0),code (q 1),code (q 2),code (q 3)⟩) := by
  have hn (i j : Fin 4) (hij : i≠j) : code (q i)≠code (q j) :=
    fun h => hij (q.injective (code.injective h))
  have hset : N.rawDisplayedQuartets q=finiteResolutionSet T tips
      ⟨code (q 0),code (q 1),code (q 2),code (q 3)⟩ := by
    ext r
    rw [N.actual_displayed_iff_labelled hl code lab hlab q r,mem_finiteResolutionSet]
    cases r
    · exact hfinite _ 0 _ _ _ _ rfl (hn 0 1 (by decide)) (hn 2 3 (by decide))
    · exact hfinite _ 1 _ _ _ _ rfl (hn 0 2 (by decide)) (hn 1 3 (by decide))
    · exact hfinite _ 2 _ _ _ _ rfl (hn 0 3 (by decide)) (hn 1 2 (by decide))
  refine ⟨hset,?_⟩
  change distinctMean (N.rawDisplayedQuartets q)=_
  rw [hset]

#print axioms actual_distinct_set_and_mean_finite
end Nanuq.ActualFinite
