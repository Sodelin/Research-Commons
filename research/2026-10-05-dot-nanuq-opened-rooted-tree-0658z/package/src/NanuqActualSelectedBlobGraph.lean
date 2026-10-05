import NanuqActualBlobInternalPaths

/-! Literal edge-indexed internal selected graph of one ORIGINAL blob.
This is a restriction of actual source vertices and edge occurrences, not a
prescribed local quartet evaluator or a capped-source admission assumption. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

abbrev OriginalBlobVertex (b : N.graph.Blob) := {v : V // N.graph.blobOf v = b}

namespace Switching
variable {N} (S : N.Switching)

abbrev InternalBlobEdge (b : N.graph.Blob) :=
  {f : S.Edge // N.graph.blobOf (N.graph.source f.val) = b ∧
    N.graph.blobOf (N.graph.target f.val) = b}

def internalBlobGraph (b : N.graph.Blob) :
    EdgeGraph (N.OriginalBlobVertex b) (S.InternalBlobEdge b) where
  source f := ⟨N.graph.source f.val.val, f.property.1⟩
  target f := ⟨N.graph.target f.val.val, f.property.2⟩

theorem internal_blob_walk_projects (b : N.graph.Blob)
    (keep : S.InternalBlobEdge b → Prop) (allowed : S.Edge → Prop)
    (hkeep : ∀ f, keep f → allowed f.val)
    {a c : N.OriginalBlobVertex b} (h : (S.internalBlobGraph b).UReach keep a c) :
    S.graph.UReach allowed a.val c.val := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨f, hf, hinc⟩ := hstep
    apply ih.tail
    refine ⟨f.val, hkeep f hf, ?_⟩
    rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
    · exact Or.inr ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩

theorem selected_internal_walk_lifts (b : N.graph.Blob)
    (keep : S.Edge → Prop)
    (hkeep : ∀ f, keep f → N.graph.blobOf (N.graph.source f.val) = b ∧
      N.graph.blobOf (N.graph.target f.val) = b)
    (a : N.OriginalBlobVertex b) {v : V} (h : S.graph.UReach keep a.val v) :
    ∀ hv : N.graph.blobOf v = b,
      (S.internalBlobGraph b).UReach (fun f => keep f.val) a ⟨v,hv⟩ := by
  induction h with
  | refl => intro _; exact .refl
  | @tail v w hp hstep ih =>
    intro hw
    obtain ⟨f, hf, hinc⟩ := hstep
    have hf0 := hkeep f hf
    rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hv : N.graph.blobOf v = b := by
        rw [← hs]
        exact hf0.1
      exact (ih hv).tail ⟨⟨f,hf0⟩, hf, Or.inl ⟨Subtype.ext hs, Subtype.ext ht⟩⟩
    · have hv : N.graph.blobOf v = b := by
        rw [← ht]
        exact hf0.2
      exact (ih hv).tail ⟨⟨f,hf0⟩, hf, Or.inr ⟨Subtype.ext hs, Subtype.ext ht⟩⟩

theorem internal_blob_graph_connected (b : N.graph.Blob)
    (a c : N.OriginalBlobVertex b) :
    (S.internalBlobGraph b).UReach (fun _ => True) a c := by
  have h := S.selected_original_blob_internal_connected b a.property c.property
  have h' := S.selected_internal_walk_lifts b _ (fun _ hf => hf) a h c.property
  exact (S.internalBlobGraph b).ureach_mono (fun _ _ => trivial) h'

theorem internal_blob_edge_is_bridge (b : N.graph.Blob) (f : S.InternalBlobEdge b) :
    (S.internalBlobGraph b).IsBridge f := by
  intro h
  have hproj := S.internal_blob_walk_projects b (fun g => g ≠ f)
    (fun g => g ≠ f.val) (fun g hgf heq => hgf (Subtype.ext heq)) h
  exact (S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val) hproj

theorem internal_blob_graph_is_tree (b : N.graph.Blob) :
    (S.internalBlobGraph b).IsTree := by
  obtain ⟨r, hr, _⟩ := N.original_blob_entry_every_switching b
  exact ⟨⟨⟨r,hr⟩⟩, S.internal_blob_graph_connected b, S.internal_blob_edge_is_bridge b⟩

theorem internal_blob_cut_source_side_iff (b : N.graph.Blob)
    (f : S.InternalBlobEdge b) (a : N.OriginalBlobVertex b) :
    (S.internalBlobGraph b).ReachWithout f ((S.internalBlobGraph b).source f) a ↔
      S.graph.ReachWithout f.val (S.graph.source f.val) a.val := by
  constructor
  · exact S.internal_blob_walk_projects b (fun g => g ≠ f) (fun g => g ≠ f.val) (fun g hgf heq => hgf (Subtype.ext heq))
  · intro ha
    rcases (S.internalBlobGraph b).edge_side_cover f
      (S.internal_blob_graph_connected b _ a) with hs | ht
    · exact hs
    · have ht0 := S.internal_blob_walk_projects b (fun g => g ≠ f) (fun g => g ≠ f.val)
        (fun g hgf heq => hgf (Subtype.ext heq)) ht
      exact False.elim (S.graph.bridge_sides_disjoint
        (S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val) ha ht0)

theorem internal_blob_cut_target_side_iff (b : N.graph.Blob)
    (f : S.InternalBlobEdge b) (a : N.OriginalBlobVertex b) :
    (S.internalBlobGraph b).ReachWithout f ((S.internalBlobGraph b).target f) a ↔
      S.graph.ReachWithout f.val (S.graph.target f.val) a.val := by
  constructor
  · exact S.internal_blob_walk_projects b (fun g => g ≠ f) (fun g => g ≠ f.val) (fun g hgf heq => hgf (Subtype.ext heq))
  · intro ha
    rcases (S.internalBlobGraph b).edge_side_cover f
      (S.internal_blob_graph_connected b _ a) with hs | ht
    · have hs0 := S.internal_blob_walk_projects b (fun g => g ≠ f) (fun g => g ≠ f.val)
        (fun g hgf heq => hgf (Subtype.ext heq)) hs
      exact False.elim (S.graph.bridge_sides_disjoint
        (S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val) hs0 ha)
    · exact ht
end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.internal_blob_graph_is_tree
#print axioms Nanuq.Source.RootedBinary.Switching.internal_blob_cut_source_side_iff
#print axioms Nanuq.Source.RootedBinary.Switching.internal_blob_cut_target_side_iff
