import RootBlobBoundaryGraph

/-!
# Original two-boundary-edge region to the two-sink endpoint
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No execution or verification.

Unlike a conditional certificate wrapper, this file constructs the entire
two-sink component after two exact free-edge subdivisions. Its input has
neither ancestry nor a sink assumption. Original edges remain individually
indexed; the original inheritance function is unchanged on them.
-/

open RootBlobInterfaces RootBlobEdgeIndexed RootBlobBoundaryGraph
open RootBlobComponentConstructor RootBlobEdgeSubdivision
namespace RootBlobBoundaryAdapter
universe u v w x
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable {G : Network V E O}
variable (R : RootTwoBoundaryRegion G)

abbrev AugV := Sum (Sum V Unit) Unit
abbrev AugE := Sum (Sum E Unit) Unit
def oldVertex (v : V) : AugV (V := V) := Sum.inl (Sum.inl v)
def oldEdge (e : E) : AugE (E := E) := Sum.inl (Sum.inl e)
def port (i : Fin 2) : AugV (V := V) :=
  if i = 0 then Sum.inl (Sum.inr ()) else Sum.inr ()
def freshEdge (i : Fin 2) : AugE (E := E) :=
  if i = 0 then Sum.inl (Sum.inr ()) else Sum.inr ()
noncomputable def boundaryEdge (i : Fin 2) : E :=
  if i = 0 then R.pair.first else R.pair.second

noncomputable def augmented : Network (AugV (V := V)) (AugE (E := E)) O :=
  subdivideTwice G R.pair.first R.pair.second

def augmentedVertices : Set (AugV (V := V)) :=
  {v | match v with
    | Sum.inl (Sum.inl v) => v ∈ R.vertices
    | _ => True}

@[simp] theorem old_mem (v : V) :
    oldVertex v ∈ R.augmentedVertices ↔ v ∈ R.vertices := Iff.rfl
@[simp] theorem port_mem (i : Fin 2) :
    port (V := V) i ∈ R.augmentedVertices := by
  fin_cases i <;> simp [port, augmentedVertices]
@[simp] theorem root_augmented : R.augmented.root = oldVertex G.root := rfl
@[simp] theorem observed_augmented (o : O) :
    R.augmented.observed o = oldVertex (G.observed o) := rfl
@[simp] theorem target_old (e : E) :
    R.augmented.target (oldEdge e) = oldVertex (G.target e) := rfl
@[simp] theorem target_fresh (i : Fin 2) :
    R.augmented.target (freshEdge (E := E) i) = port (V := V) i := by
  fin_cases i <;> rfl

theorem source_old (e : E) : R.augmented.source (oldEdge e) =
    if e = R.pair.second then port 1
    else if e = R.pair.first then port 0 else oldVertex (G.source e) := by
  classical
  by_cases h1 : e = R.pair.second <;> by_cases h0 : e = R.pair.first <;>
    simp [augmented, subdivideTwice, subdivide, oldEdge, oldVertex, port, h0, h1]

theorem source_fresh (i : Fin 2) :
    R.augmented.source (freshEdge (E := E) i) = oldVertex (G.source (R.boundaryEdge i)) := by
  classical
  have h10 : R.pair.second ≠ R.pair.first := Ne.symm R.pair.distinct
  fin_cases i <;>
    simp [augmented, subdivideTwice, subdivide, freshEdge, boundaryEdge, oldVertex, h10]

theorem boundary_out (hG : GraphAdmitted G) (i : Fin 2) :
    Outgoing G R.vertices (R.boundaryEdge i) := by
  fin_cases i
  · simpa [boundaryEdge] using R.first_outgoing hG
  · simpa [boundaryEdge] using R.second_outgoing hG

theorem source_boundary (i : Fin 2) :
    R.augmented.source (oldEdge (R.boundaryEdge i)) = port (V := V) i := by
  have h01 := R.pair.distinct
  fin_cases i <;> simp [source_old, boundaryEdge, h01]

theorem augmented_admitted (hG : GraphAdmitted G) : GraphAdmitted R.augmented :=
  graph_admitted (subdivide G R.pair.first) (Sum.inl R.pair.second)
    (graph_admitted G R.pair.first hG)

theorem augmented_weights (W : E → ℝ) (hW : WeightsAdmitted G W) :
    WeightsAdmitted R.augmented (weights (weights W)) :=
  weights_admitted (subdivide G R.pair.first) (Sum.inl R.pair.second) (weights W)
    (weights_admitted G R.pair.first W hW)

theorem augmented_ancestral (hG : GraphAdmitted G) :
    ∀ e, R.augmented.target e ∈ R.augmentedVertices →
      R.augmented.source e ∈ R.augmentedVertices := by
  intro e ht
  cases e with
  | inl e =>
    cases e with
    | inl e =>
      change oldVertex (G.target e) ∈ R.augmentedVertices at ht
      have hs := R.ancestral hG e ((R.old_mem _).mp ht)
      change R.augmented.source (oldEdge e) ∈ R.augmentedVertices
      rw [R.source_old]
      split_ifs <;> simp_all
    | inr e =>
      cases e
      change R.augmented.source (freshEdge (E := E) 0) ∈ R.augmentedVertices
      rw [R.source_fresh]
      exact (R.old_mem _).mpr (R.boundary_out hG 0).1
  | inr e =>
    cases e
    change R.augmented.source (freshEdge (E := E) 1) ∈ R.augmentedVertices
    rw [R.source_fresh]
    exact (R.old_mem _).mpr (R.boundary_out hG 1).1

/-- A port has exactly its original second-segment outgoing occurrence. -/
theorem source_port_edge (i : Fin 2) (e : AugE (E := E))
    (h : R.augmented.source e = port (V := V) i) :
    e = oldEdge (R.boundaryEdge i) := by
  classical
  have h01 := R.pair.distinct
  cases e with
  | inl e =>
    cases e with
    | inl e =>
      change R.augmented.source (oldEdge e) = port i at h
      rw [R.source_old] at h
      fin_cases i <;> split_ifs at h with he1 he0 <;>
        simp_all [port, oldVertex, boundaryEdge]
    | inr e =>
      cases e
      change R.augmented.source (freshEdge (E := E) 0) = port i at h
      rw [R.source_fresh] at h
      fin_cases i <;> simp [oldVertex, port] at h
  | inr e =>
    cases e
    change R.augmented.source (freshEdge (E := E) 1) = port i at h
    rw [R.source_fresh] at h
    fin_cases i <;> simp [oldVertex, port] at h

theorem port_is_sink (hG : GraphAdmitted G) (i : Fin 2) :
    ∀ e, R.augmented.target e ∈ R.augmentedVertices →
      R.augmented.source e ≠ port (V := V) i := by
  intro e ht hs
  have he := R.source_port_edge i e hs
  subst e
  exact (R.boundary_out hG i).2 ((R.old_mem _).mp ht)

/-- An original hidden vertex still has an internal outgoing edge after
subdivision, even when it was an original boundary attachment vertex. -/
theorem old_internal_outgoing (hG : GraphAdmitted G) {v : V} (hv : v ∈ R.vertices) :
    ∃ e, R.augmented.source e = oldVertex v ∧
      R.augmented.target e ∈ R.augmentedVertices := by
  classical
  have hout : ∃ e, G.source e = v := by
    by_contra hn
    have hs : ∀ e, G.source e ≠ v := by simpa using hn
    obtain ⟨o, ho⟩ := (hG.2.2.2.2.2 v).mp hs
    exact R.hidden o (by simpa [ho] using hv)
  obtain ⟨e, he⟩ := hout
  by_cases ht : G.target e ∈ R.vertices
  · have h0 : e ≠ R.pair.first := by
      intro h; subst e; exact (R.first_outgoing hG).2 ht
    have h1 : e ≠ R.pair.second := by
      intro h; subst e; exact (R.second_outgoing hG).2 ht
    refine ⟨oldEdge e, ?_, (R.old_mem _).mpr ht⟩
    simp [R.source_old, h0, h1, he]
  · have hb : Boundary G R.vertices e := Or.inl ⟨by simpa [he] using hv, ht⟩
    rcases (R.pair.cover e).mp hb with h0 | h1
    · refine ⟨freshEdge (E := E) 0, ?_, ?_⟩
      · rw [R.source_fresh]
        simpa [boundaryEdge, h0] using congrArg (oldVertex (V := V)) he
      · exact R.port_mem 0
    · refine ⟨freshEdge (E := E) 1, ?_, ?_⟩
      · rw [R.source_fresh]
        simpa [boundaryEdge, h1] using congrArg (oldVertex (V := V)) he
      · exact R.port_mem 1

theorem augmented_sinks (hG : GraphAdmitted G) (v : AugV (V := V))
    (hv : v ∈ R.augmentedVertices) :
    (∀ e, R.augmented.target e ∈ R.augmentedVertices → R.augmented.source e ≠ v) ↔
      ∃ i, port (V := V) i = v := by
  constructor
  · intro hs
    cases v with
    | inl v =>
      cases v with
      | inl v =>
        obtain ⟨e, he, ht⟩ := R.old_internal_outgoing hG hv
        exact False.elim (hs e ht he)
      | inr v => cases v; exact ⟨0, rfl⟩
    | inr v => cases v; exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩
    exact R.port_is_sink hG i

theorem augmented_outgoing_ports (hG : GraphAdmitted G) :
    ∀ e, R.augmented.source e ∈ R.augmentedVertices →
      R.augmented.target e ∉ R.augmentedVertices →
      ∃ i, port (V := V) i = R.augmented.source e := by
  intro e hs ht
  cases e with
  | inl e =>
    cases e with
    | inl e =>
      change R.augmented.source (oldEdge e) ∈ R.augmentedVertices at hs
      change ∃ i, port i = R.augmented.source (oldEdge e)
      by_cases h1 : e = R.pair.second
      · exact ⟨1, by simp [R.source_old, h1]⟩
      by_cases h0 : e = R.pair.first
      · exact ⟨0, by simp [R.source_old, h1, h0]⟩
      have hsource : G.source e ∈ R.vertices := by
        simpa [R.source_old, h0, h1] using hs
      have htarget : G.target e ∉ R.vertices := ht
      rcases (R.pair.cover e).mp (Or.inl ⟨hsource, htarget⟩) with h | h
      · exact False.elim (h0 h)
      · exact False.elim (h1 h)
    | inr e => cases e; exact False.elim (ht (R.port_mem 0))
  | inr e => cases e; exact False.elim (ht (R.port_mem 1))

/-- The structural certificate is now constructed from the literal original
edge-boundary input, rather than imported as an extra source hypothesis. -/
noncomputable def component (hG : GraphAdmitted G) : RootComponent R.augmented where
  vertices := R.augmentedVertices
  root_mem := R.root_mem
  ports := port
  ports_mem := R.port_mem
  ports_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [port]
  ports_nonroot := by intro i; fin_cases i <;> simp [port, augmented, subdivideTwice, subdivide]
  ancestral := R.augmented_ancestral hG
  sinks := R.augmented_sinks hG
  outgoing_ports := R.augmented_outgoing_ports hG
  hidden := R.hidden

/-- Both complete parameter-image directions, not just inclusion or closure.
All original cut-edge matrices are free. No protected matrix is asserted to
survive the compensation step; original inheritance remains fixed. -/
theorem modelImage_eq_boundaryFork [Nonempty S]
    (hG : GraphAdmitted G) (W : E → ℝ) (hW : WeightsAdmitted G W)
    (H : Subgroup (Equiv.Perm S))
    (forkRank : Sum (Fin 3) (R.component hG).Outside → ℕ)
    (hS : 1 < Fintype.card S) :
    RootBlobFullModel.modelImage G W H =
      RootBlobFullModel.modelImage
        (RootBlobCutFactorization.cutNetwork rootedFork
          ((R.component hG).exterior (R.augmented_admitted hG))
          (R.component hG).labels forkRank)
        (Sum.elim forkWeights
          (((R.component hG).sourceCut (R.augmented_admitted hG)).outsideWeights
            (weights (weights W)))) H := by
  calc
    _ = RootBlobFullModel.modelImage R.augmented (weights (weights W)) H :=
      modelImage_eq_subdivideTwice G R.pair.first R.pair.second W H hG
    _ = _ := RootBlobFullModel.rootComponent_model_eq_rootedFork
      (R.component hG) (R.augmented_admitted hG) (weights (weights W))
      (R.augmented_weights W hW) H forkRank hS

end RootBlobBoundaryAdapter
