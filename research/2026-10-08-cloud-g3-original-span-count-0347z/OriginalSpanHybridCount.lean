import G1OriginalSpanCalendarDecomposition
import G1LiftedOriginalBigon
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup

/-!
# Original calendar spans use each original hybrid at most once

Cloud G3, 2026-10-08. Compiler UNCHECKED; outside the shared source freeze.
The carrier and constructors are the EXISTING G1 OriginalSpan. Every listed
site is an actual Hybrid of the SAME original network. Strict order is reused
from G1OriginalSpanCalendarDecomposition.actual_span_dates_strict.

This counts a span that exists; it does not supply a graph-to-span law,
selected-ancestry serialization, or a scalar recurrence interpretation.
-/
namespace CloudG3.OriginalSpanHybridCount

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1OriginalDecoratedSpan G1NonrootBigonKernel
open G1OriginalSpanCalendarDecomposition
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1LiftedOriginalBigon
open scoped Classical

section Raw
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Bigon occurrences retain genuine original hybrid IDs, in rootward order.
Ordinary edge atoms contribute no hybrid. -/
noncomputable def hybridOccurrences (N : RootedBinary V E X) {a b : V} :
    OriginalSpan N a b → List (Hybrid N)
  | .edge _ _ => []
  | .bigon B => [⟨B.parents.hybrid, B.parents.isHybrid⟩]
  | .append first last => hybridOccurrences N first ++ hybridOccurrences N last

/-- The input is included and the output excluded in the original age window. -/
theorem actual_span_hybrid_age_window (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (word : OriginalSpan N a b) :
    ∀ h ∈ hybridOccurrences N word, C.age a ≤ C.age h.val ∧ C.age h.val < C.age b := by
  induction word with
  | edge e ordinary =>
      intro h hh
      simp only [hybridOccurrences, List.not_mem_nil] at hh
  | bigon B =>
      intro h hh
      simp only [hybridOccurrences, List.mem_singleton] at hh
      subst h
      exact ⟨le_refl _, actual_span_dates_strict N C (.bigon B)⟩
  | append first last ihfirst ihlast =>
      intro h hh
      change h ∈ hybridOccurrences N first ++ hybridOccurrences N last at hh
      rcases List.mem_append.mp hh with hh | hh
      · exact ⟨(ihfirst h hh).1,
          (ihfirst h hh).2.trans (actual_span_dates_strict N C last)⟩
      · exact ⟨(actual_span_dates_strict N C first).le.trans (ihlast h hh).1,
          (ihlast h hh).2⟩

/-- Concatenation separates the actual site ages strictly at its interface. -/
theorem actual_append_hybrid_age_separation (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b c : V} (first : OriginalSpan N a b) (last : OriginalSpan N b c)
    {h k : Hybrid N} (hh : h ∈ hybridOccurrences N first)
    (hk : k ∈ hybridOccurrences N last) : C.age h.val < C.age k.val :=
  ((actual_span_hybrid_age_window N C first h hh).2).trans_le
    (actual_span_hybrid_age_window N C last k hk).1

/-- Pairwise chronological order concerns original sites, not random mergers. -/
theorem actual_span_hybrids_chronological (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (word : OriginalSpan N a b) :
    (hybridOccurrences N word).Pairwise (fun h k => C.age h.val < C.age k.val) := by
  induction word with
  | edge e ordinary => simp only [hybridOccurrences, List.pairwise_nil]
  | bigon B => exact List.pairwise_singleton _ _
  | append first last ihfirst ihlast =>
      change (hybridOccurrences N first ++ hybridOccurrences N last).Pairwise _
      exact List.pairwise_append.mpr ⟨ihfirst, ihlast, fun h hh k hk =>
        actual_append_hybrid_age_separation N C first last hh hk⟩

/-- No original hybrid can appear twice in ONE composed original span. -/
theorem actual_span_hybrids_nodup (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (word : OriginalSpan N a b) : (hybridOccurrences N word).Nodup := by
  induction word with
  | edge e ordinary => simp only [hybridOccurrences, List.nodup_nil]
  | bigon B => exact List.nodup_singleton _
  | append first last ihfirst ihlast =>
      change (hybridOccurrences N first ++ hybridOccurrences N last).Nodup
      apply ihfirst.append ihlast
      apply List.disjoint_left.mpr
      intro h hh hk
      exact (lt_irrefl (C.age h.val))
        (actual_append_hybrid_age_separation N C first last hh hk)

/-- The bound uses the ACTUAL original Hybrid subtype; no supplied injection. -/
theorem actual_span_hybrid_length_le_total (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (word : OriginalSpan N a b) :
    (hybridOccurrences N word).length ≤ Fintype.card (Hybrid N) := by
  exact (actual_span_hybrids_nodup N C word).length_le_card

/-- The existing syntax cannot start at a distinct-parent hybrid merely
because selected pruning would later form a grouped two-arm component. -/
theorem actual_span_start_has_original_atom (N : RootedBinary V E X)
    {a b : V} (word : OriginalSpan N a b) :
    N.graph.inDegree a = 1 ∨ ∃ B : NonrootBigon N, B.parents.hybrid = a := by
  induction word with
  | edge e ordinary => exact Or.inl ordinary
  | bigon B => exact Or.inr ⟨B, rfl⟩
  | append first last ihfirst ihlast => exact ihfirst

/-- A constructor-level obstruction, with graph facts rather than a desired
law or graph-to-word certificate as hypotheses. The manuscript gives an
admitted four-taxon original source deriving both facts. -/
theorem no_span_from_unrepresented_original_site (N : RootedBinary V E X) (a : V)
    (hordinary : N.graph.inDegree a ≠ 1)
    (hbigon : ∀ B : NonrootBigon N, B.parents.hybrid ≠ a)
    {b : V} (word : OriginalSpan N a b) : False := by
  rcases actual_span_start_has_original_atom N word with h | ⟨B, h⟩
  · exact hordinary h
  · exact hbigon B h
end Raw

section Decorated
universe u v w
variable {X : Type w} [Fintype X]

/-- Every EXISTING physical decorated bridge inherits the count on its
constructed original word, including recipes containing prior splices. -/
theorem actual_decorated_bridge_hybrid_length_le_total (O S : Source.{u,v,w} X)
    (D : Decoration O S) (e : S.Edge) (he : S.network.graph.IsBridge e) :
    (hybridOccurrences O.network (bridgeSpan O S D e he)).length ≤
      Fintype.card (Hybrid O.network) :=
  actual_span_hybrid_length_le_total O.network O.calendar _

/-- The lifted removed component and BOTH inherited bookends share ONE
original calendar, so no original hybrid repeats across their concatenation. -/
theorem actual_lifted_bigon_hybrid_length_le_total (O S : Source.{u,v,w} X)
    (D : Decoration O S) (H : OriginalParentRegistry O.network)
    (b : S.network.graph.Blob) (A : G1ActualTwoPortBlob.ActualBlobBigon S.network b) :
    (hybridOccurrences O.network (newOriginalSpan O S D H b A)).length ≤
      Fintype.card (Hybrid O.network) :=
  actual_span_hybrid_length_le_total O.network O.calendar _
end Decorated

end CloudG3.OriginalSpanHybridCount
