import guards.NanuqActualQuartetCutLocalization
import SourceResolve

set_option debug.skipKernelTC false

/-! Physical four-port restriction: changing any of the four taxa within its
original port preserves each actual switching resolution and the DISTINCT
raw displayed quartet set and mean. No desired source identity is assumed. -/
namespace Nanuq.Source.RootedBinary.Switching
open scoped Classical
open Nanuq.Quartet
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

private theorem cut_two_of_four_patterns : ∀ s : Finset (Fin 4), s.card = 2 →
    (0 ∈ s ∧ 1 ∈ s ∧ 2 ∉ s ∧ 3 ∉ s) ∨
    (2 ∈ s ∧ 3 ∈ s ∧ 0 ∉ s ∧ 1 ∉ s) ∨
    (0 ∈ s ∧ 2 ∈ s ∧ 1 ∉ s ∧ 3 ∉ s) ∨
    (1 ∈ s ∧ 3 ∈ s ∧ 0 ∉ s ∧ 2 ∉ s) ∨
    (0 ∈ s ∧ 3 ∈ s ∧ 1 ∉ s ∧ 2 ∉ s) ∨
    (1 ∈ s ∧ 2 ∈ s ∧ 0 ∉ s ∧ 3 ∉ s) := by
  decide +kernel

theorem resolve_eq_of_shared_two_two_cut
    (q q' : Fin 4 ↪ X) (f : S.Edge)
    (hcut : (S.quartetSide q f (S.graph.target f)).card = 2)
    (hsides : S.quartetSide q f (S.graph.target f) =
      S.quartetSide q' f (S.graph.target f)) : S.resolve q = S.resolve q' := by
  let s := S.quartetSide q f (S.graph.target f)
  have hf := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f
  have hT (a : Fin 4 ↪ X) (ha : S.quartetSide a f (S.graph.target f) = s)
      (i : Fin 4) (hi : i ∈ s) :
      S.graph.ReachWithout f (S.graph.target f) (N.leaf (a i)) :=
    (S.mem_quartetSide a f _ i).mp (by rwa [ha])
  have hS (a : Fin 4 ↪ X) (ha : S.quartetSide a f (S.graph.target f) = s)
      (i : Fin 4) (hi : i ∉ s) :
      S.graph.ReachWithout f (S.graph.source f) (N.leaf (a i)) := by
    rcases S.graph.edge_side_cover f (S.selected_connected _ _) with h | h
    · exact h
    · exact False.elim (hi (by rw [← ha]; exact (S.mem_quartetSide a f _ i).mpr h))
  have hex : ∃ r, ∀ a : Fin 4 ↪ X,
      S.quartetSide a f (S.graph.target f) = s →
        S.graph.Resolves (fun i => N.leaf (a i)) r := by
    rcases cut_two_of_four_patterns s hcut with h | h | h | h | h | h
    · refine ⟨.xy_zw, ?_⟩
      intro a ha
      exact ⟨f, hf, Or.inr ⟨hS a ha 2 h.2.2.1, hS a ha 3 h.2.2.2,
        hT a ha 0 h.1, hT a ha 1 h.2.1⟩⟩
    · refine ⟨.xy_zw, ?_⟩
      intro a ha
      exact ⟨f, hf, Or.inl ⟨hS a ha 0 h.2.2.1, hS a ha 1 h.2.2.2,
        hT a ha 2 h.1, hT a ha 3 h.2.1⟩⟩
    · refine ⟨.xz_yw, ?_⟩
      intro a ha
      exact ⟨f, hf, Or.inr ⟨hS a ha 1 h.2.2.1, hS a ha 3 h.2.2.2,
        hT a ha 0 h.1, hT a ha 2 h.2.1⟩⟩
    · refine ⟨.xz_yw, ?_⟩
      intro a ha
      exact ⟨f, hf, Or.inl ⟨hS a ha 0 h.2.2.1, hS a ha 2 h.2.2.2,
        hT a ha 1 h.1, hT a ha 3 h.2.1⟩⟩
    · refine ⟨.xw_yz, ?_⟩
      intro a ha
      exact ⟨f, hf, Or.inr ⟨hS a ha 1 h.2.2.1, hS a ha 2 h.2.2.2,
        hT a ha 0 h.1, hT a ha 3 h.2.1⟩⟩
    · refine ⟨.xw_yz, ?_⟩
      intro a ha
      exact ⟨f, hf, Or.inl ⟨hS a ha 0 h.2.2.1, hS a ha 3 h.2.2.2,
        hT a ha 1 h.1, hT a ha 2 h.2.1⟩⟩
  obtain ⟨r, hr⟩ := hex
  have hq : S.resolve q = r := S.graph.resolution_unique (S.resolve_spec q) (hr q rfl)
  have hq' : S.resolve q' = r :=
    S.graph.resolution_unique (S.resolve_spec q') (hr q' hsides.symm)
  exact hq.trans hq'.symm

theorem actual_four_port_resolve_invariant
    (q q' : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (hports : ∀ i, N.blobProjection b hb (q i) = N.blobProjection b hb (q' i)) :
    S.resolve q = S.resolve q' := by
  obtain ⟨f, _, hcut⟩ := S.quartet_two_two_edge q
  obtain ⟨hfs, hft⟩ := S.original_two_two_cut_internal_to_blob q b hb hinj f hcut
  apply S.resolve_eq_of_shared_two_two_cut q q' f hcut
  ext i
  rw [S.mem_quartetSide, S.mem_quartetSide]
  exact S.original_port_internal_cut_target_side_iff b hb f hfs hft (q i) (q' i) (hports i)
end Nanuq.Source.RootedBinary.Switching

namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_four_port_distinct_quartet_set_and_mean
    (q q' : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (hports : ∀ i, N.blobProjection b hb (q i) = N.blobProjection b hb (q' i)) :
    N.rawDisplayedQuartets q = N.rawDisplayedQuartets q' ∧
      N.rawQuartetMean q = N.rawQuartetMean q' := by
  have hfun : (fun S : N.Switching => S.resolve q) = fun S : N.Switching => S.resolve q' := by
    funext S
    exact S.actual_four_port_resolve_invariant q q' b hb hinj hports
  constructor
  · unfold rawDisplayedQuartets
    rw [hfun]
  · unfold rawQuartetMean
    rw [hfun]
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.actual_four_port_resolve_invariant
#print axioms Nanuq.Source.RootedBinary.actual_four_port_distinct_quartet_set_and_mean
