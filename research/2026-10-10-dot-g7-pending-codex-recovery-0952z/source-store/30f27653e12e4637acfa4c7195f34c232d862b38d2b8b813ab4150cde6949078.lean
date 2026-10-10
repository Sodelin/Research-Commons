import G7OriginalRelabelling

/-!
Finite labelled code universe for the actual G7 original registry.
Contributor: dot, 2026-10-09. This retains duplicates and is a complete finite
candidate universe, not an admission oracle or a polynomial-law compiler.
-/
namespace GProgram.G7.OriginalFiniteEncoding
open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open GProgram.G7.OriginalRelabelling
open scoped Classical
variable {V E X ID : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype ID]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq ID]

def vertexCount (n r : ℕ) : ℕ := 2*n + 2*r - 1
def edgeCount (n r : ℕ) : ℕ := 2*n + 3*r - 2

theorem hybrid_card (N : RootedBinary V E X) : Fintype.card (Hybrid N) = hybridCount N := by
  simp [Hybrid, hybridCount, Fintype.card_subtype]

theorem original_registry_sizes (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    Fintype.card V = vertexCount (Fintype.card X) (Fintype.card ID) ∧
    Fintype.card E = edgeCount (Fintype.card X) (Fintype.card ID) := by
  have hi : hybridCount N = Fintype.card ID := (hybrid_card N).symm.trans (Fintype.card_congr ids).symm
  obtain ⟨hv,he⟩ := original_census N
  rw [hi] at hv he
  unfold vertexCount edgeCount
  omega

noncomputable def vertexNumbering (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    V ≃ Fin (vertexCount (Fintype.card X) (Fintype.card ID)) :=
  Fintype.equivFinOfCardEq (original_registry_sizes N ids).1

noncomputable def edgeNumbering (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    E ≃ Fin (edgeCount (Fintype.card X) (Fintype.card ID)) :=
  Fintype.equivFinOfCardEq (original_registry_sizes N ids).2

/-- source/target arrays, root, named taxa, named hybrids, ordered parent IDs.
Parallel arcs occupy different array coordinates. X and ID are unchanged. -/
abbrev Code (X ID : Type*) [Fintype X] [Fintype ID] :=
  let nv := vertexCount (Fintype.card X) (Fintype.card ID)
  let ne := edgeCount (Fintype.card X) (Fintype.card ID)
  (Fin ne → Fin nv) × (Fin ne → Fin nv) × Fin nv ×
    (X → Fin nv) × (ID → Fin nv) × (ID → Bool → Fin ne)

def allCodes : Finset (Code X ID) := Finset.univ

noncomputable def encode (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) : Code X ID :=
  let v := vertexNumbering N ids
  let e := edgeNumbering N ids
  ⟨fun f => v (N.graph.source (e.symm f)),
   fun f => v (N.graph.target (e.symm f)), v N.root,
   fun x => v (N.leaf x), fun h => v (ids h).val,
   fun h b => e ((H.parents (ids h)).parent b)⟩

/-- Coverage is unconditional on source parameters and does not collapse a
parallel occurrence or rename a supplied taxon/hybrid label. -/
theorem every_original_source_has_code (N : RootedBinary V E X)
    (ids : ID ≃ Hybrid N) (H : OriginalParentRegistry N) :
    encode N ids H ∈ (allCodes : Finset (Code X ID)) := Finset.mem_univ _

noncomputable def numberedSource (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    RootedBinary (Fin (vertexCount (Fintype.card X) (Fintype.card ID)))
      (Fin (edgeCount (Fintype.card X) (Fintype.card ID))) X :=
  network N (vertexNumbering N ids) (edgeNumbering N ids)

/-- The finite code really contains the incidence data of a reconstructed
actual RootedBinary source, not merely an uninterpreted identifier. -/
theorem encoded_graph_exact (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) :
    (encode N ids H).1 = (numberedSource N ids).graph.source ∧
    (encode N ids H).2.1 = (numberedSource N ids).graph.target ∧
    (encode N ids H).2.2.1 = (numberedSource N ids).root ∧
    (encode N ids H).2.2.2.1 = (fun x => (numberedSource N ids).leaf x) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem encoded_parent_target (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) (h : ID) (b : Bool) :
    (encode N ids H).2.1 ((encode N ids H).2.2.2.2.2 h b) =
      (encode N ids H).2.2.2.2.1 h := by
  simp only [encode, Equiv.symm_apply_apply]
  exact congrArg (vertexNumbering N ids) (registry_parent_target N H (ids h) b)

theorem encoded_parent_bits_distinct (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) (h : ID) :
    (encode N ids H).2.2.2.2.2 h false ≠ (encode N ids H).2.2.2.2.2 h true := by
  intro he
  have he' := (edgeNumbering N ids).injective he
  exact (H.parents (ids h)).different (by simpa [GProgram.G2.OriginalHybridParents.parent] using he')

#print axioms original_registry_sizes
#print axioms every_original_source_has_code
#print axioms encoded_graph_exact
#print axioms encoded_parent_bits_distinct
end GProgram.G7.OriginalFiniteEncoding
