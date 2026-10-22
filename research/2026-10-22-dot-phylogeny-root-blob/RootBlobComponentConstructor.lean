import RootBlobSourceCut

/-!
# Construct the structural adapter from an ancestral hidden two-sink component

Author: dot (OpenAI), 22 October 2026.
UNELABORATED source only; no compiler, kernel or runtime verification.
The component hypotheses are graph incidences and the source observation
contract. No equality of probabilistic models is assumed.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobContextGlue RootBlobCutFactorization
open RootBlobRelabeling RootBlobSourceCut
namespace RootBlobComponentConstructor
universe u v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable {O : Type x} [Fintype O]
variable (G : RootBlobEdgeIndexed.Network V E O)

/-- Exact rooted component contract used by the selected source question.
Maximality or edge-biconnectivity is not needed by the stronger image proof. -/
structure RootComponent where
  vertices : Set V
  root_mem : G.root ∈ vertices
  ports : Fin 2 → V
  ports_mem : ∀ o, ports o ∈ vertices
  ports_injective : Function.Injective ports
  ports_nonroot : ∀ o, ports o ≠ G.root
  ancestral : ∀ e, G.target e ∈ vertices → G.source e ∈ vertices
  sinks : ∀ v, v ∈ vertices →
    (∀ e, G.target e ∈ vertices → G.source e ≠ v) ↔ ∃ o, ports o = v
  outgoing_ports : ∀ e, G.source e ∈ vertices → G.target e ∉ vertices →
    ∃ o, ports o = G.source e
  hidden : ∀ o, G.observed o ∉ vertices

variable {G}
variable (R : RootComponent G)

abbrev Inside := {v : V // v ∈ R.vertices}
abbrev Outside := {v : V // v ∉ R.vertices}
abbrev InnerEdge := {e : E // G.target e ∈ R.vertices}
abbrev OuterEdge := {e : E // G.target e ∉ R.vertices}

noncomputable instance insideFintype : Fintype R.Inside := Fintype.ofFinite _
noncomputable instance outsideFintype : Fintype R.Outside := Fintype.ofFinite _
noncomputable instance innerEdgeFintype : Fintype R.InnerEdge := Fintype.ofFinite _
noncomputable instance outerEdgeFintype : Fintype R.OuterEdge := Fintype.ofFinite _

def interior : RootBlobEdgeIndexed.Network R.Inside R.InnerEdge (Fin 2) where
  root := ⟨G.root, R.root_mem⟩
  observed := fun o => ⟨R.ports o, R.ports_mem o⟩
  source := fun e => ⟨G.source e.val, R.ancestral e.val e.property⟩
  target := fun e => ⟨G.target e.val, e.property⟩
  rank := fun v => G.rank v.val

theorem interior_admitted (hG : RootBlobEdgeIndexed.GraphAdmitted G) :
    RootBlobEdgeIndexed.GraphAdmitted R.interior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact R.ports_injective (congrArg Subtype.val h)
  · intro o h
    exact R.ports_nonroot o (congrArg Subtype.val h)
  · intro e
    exact hG.2.2.1 e.val
  · intro e h
    exact hG.2.2.2.1 e.val (congrArg Subtype.val h)
  · intro v hv
    have hn : v.val ≠ G.root := by
      intro he
      exact hv (Subtype.ext he)
    obtain ⟨e, he⟩ := hG.2.2.2.2.1 v.val hn
    have hm : G.target e ∈ R.vertices := by simpa [he] using v.property
    exact ⟨⟨e, hm⟩, Subtype.ext he⟩
  · intro v
    constructor
    · intro h
      have hs : ∀ e, G.target e ∈ R.vertices → G.source e ≠ v.val := by
        intro e he hsource
        exact h ⟨e, he⟩ (Subtype.ext hsource)
      obtain ⟨o, ho⟩ := (R.sinks v.val v.property).mp hs
      exact ⟨o, Subtype.ext ho⟩
    · rintro ⟨o, ho⟩ e he
      have hs := (R.sinks v.val v.property).mpr ⟨o, congrArg Subtype.val ho⟩
      exact hs e.val e.property (congrArg Subtype.val he)

noncomputable def exteriorSource (e : R.OuterEdge) : Sum (Fin 2) R.Outside := by
  classical
  exact if h : G.source e.val ∈ R.vertices then
    Sum.inl (Classical.choose (R.outgoing_ports e.val h e.property))
  else Sum.inr ⟨G.source e.val, h⟩

theorem exteriorSource_inr_source (e : R.OuterEdge) (v : R.Outside)
    (h : R.exteriorSource e = Sum.inr v) : G.source e.val = v.val := by
  classical
  unfold exteriorSource at h
  split_ifs at h with hm
  · cases h
  · exact congrArg Subtype.val (Sum.inr.inj h)

noncomputable def exterior (hG : RootBlobEdgeIndexed.GraphAdmitted G) :
    ExteriorDAG R.Outside R.OuterEdge where
  source := R.exteriorSource
  target := fun e => ⟨G.target e.val, e.property⟩
  rank := fun v => G.rank v.val
  internal_rank := by
    intro e v he
    have hs := R.exteriorSource_inr_source e v he
    simpa [hs] using hG.2.2.1 e.val

noncomputable def vertexEquiv : V ≃ Sum R.Inside R.Outside := by
  classical
  exact (Equiv.Set.sumCompl R.vertices).symm

noncomputable def edgeEquiv : E ≃ Sum R.InnerEdge R.OuterEdge := by
  classical
  exact (Equiv.Set.sumCompl {e | G.target e ∈ R.vertices}).symm

def labels : O → Sum (Fin 2) R.Outside :=
  fun o => Sum.inr ⟨G.observed o, R.hidden o⟩

noncomputable def fullRank : Sum R.Inside R.Outside → ℕ :=
  fun v => G.rank (R.vertexEquiv.symm v)

theorem vertexEquiv_inside (v : R.Inside) :
    R.vertexEquiv v.val = Sum.inl v := by
  classical
  exact Equiv.Set.sumCompl_symm_apply (s := R.vertices) v

theorem vertexEquiv_outside (v : R.Outside) :
    R.vertexEquiv v.val = Sum.inr v := by
  classical
  exact Equiv.Set.sumCompl_symm_apply_compl (s := R.vertices) v

theorem edgeEquiv_symm_inl (e : R.InnerEdge) :
    R.edgeEquiv.symm (Sum.inl e) = e.val := by
  classical
  exact Equiv.Set.sumCompl_apply_inl {e | G.target e ∈ R.vertices} e

theorem edgeEquiv_symm_inr (e : R.OuterEdge) :
    R.edgeEquiv.symm (Sum.inr e) = e.val := by
  classical
  exact Equiv.Set.sumCompl_apply_inr {e | G.target e ∈ R.vertices} e

theorem exterior_source_partition (e : R.OuterEdge) :
    R.vertexEquiv (G.source e.val) =
      boundarySource R.interior (R.exteriorSource e) := by
  classical
  by_cases h : G.source e.val ∈ R.vertices
  · let o := Classical.choose (R.outgoing_ports e.val h e.property)
    have ho : R.ports o = G.source e.val :=
      Classical.choose_spec (R.outgoing_ports e.val h e.property)
    have hv := R.vertexEquiv_inside ⟨R.ports o, R.ports_mem o⟩
    simpa [exteriorSource, h, boundarySource, interior, o, ho] using hv
  · simpa [exteriorSource, h, boundarySource] using
      R.vertexEquiv_outside ⟨G.source e.val, h⟩

theorem graph_partition (hG : RootBlobEdgeIndexed.GraphAdmitted G) :
    relabel G R.vertexEquiv R.edgeEquiv =
      cutNetwork R.interior (R.exterior hG) R.labels R.fullRank := by
  classical
  have hroot : R.vertexEquiv G.root = Sum.inl R.interior.root :=
    R.vertexEquiv_inside ⟨G.root, R.root_mem⟩
  have hobs : (fun o => R.vertexEquiv (G.observed o)) =
      fun o => boundarySource R.interior (R.labels o) := by
    funext o
    exact R.vertexEquiv_outside ⟨G.observed o, R.hidden o⟩
  have hsource : (fun e => R.vertexEquiv (G.source (R.edgeEquiv.symm e))) =
      Sum.elim (fun e => Sum.inl (R.interior.source e))
        (fun e => boundarySource R.interior ((R.exterior hG).source e)) := by
    funext e
    cases e with
    | inl e =>
      rw [R.edgeEquiv_symm_inl]
      exact R.vertexEquiv_inside ⟨G.source e.val, R.ancestral e.val e.property⟩
    | inr e =>
      rw [R.edgeEquiv_symm_inr]
      exact R.exterior_source_partition e
  have htarget : (fun e => R.vertexEquiv (G.target (R.edgeEquiv.symm e))) =
      Sum.elim (fun e => Sum.inl (R.interior.target e))
        (fun e => Sum.inr ((R.exterior hG).target e)) := by
    funext e
    cases e with
    | inl e =>
      rw [R.edgeEquiv_symm_inl]
      exact R.vertexEquiv_inside ⟨G.target e.val, e.property⟩
    | inr e =>
      rw [R.edgeEquiv_symm_inr]
      exact R.vertexEquiv_outside ⟨G.target e.val, e.property⟩
  unfold relabel cutNetwork
  rw [hroot, hobs, hsource, htarget]
  rfl

/-- Construct the earlier structural certificate, rather than assuming it. -/
noncomputable def sourceCut (hG : RootBlobEdgeIndexed.GraphAdmitted G) :
    SourceCut (A := R.Inside) (B := R.Outside)
      (EI := R.InnerEdge) (EX := R.OuterEdge) G where
  interior := R.interior
  exterior := R.exterior hG
  labels := R.labels
  rank := R.fullRank
  vertices := R.vertexEquiv
  edges := R.edgeEquiv
  graph_eq := R.graph_partition hG
  interior_admitted := R.interior_admitted hG
  hidden_blob := by
    intro o
    exact ⟨⟨G.observed o, R.hidden o⟩, rfl⟩

/-- Original source component endpoint, now with the graph adapter
constructed from explicit source graph hypotheses. -/
theorem componentImage_eq_rootedFork {S : Type u} [Fintype S] [Nonempty S]
    (hG : RootBlobEdgeIndexed.GraphAdmitted G)
    (W : E → ℝ) (hW : RootBlobEdgeIndexed.WeightsAdmitted G W)
    (MX : R.OuterEdge → Mat S) (H : Subgroup (Equiv.Perm S))
    (hMX : ∀ e, OpenTransition H (MX e))
    (forkRank : Sum (Fin 3) R.Outside → ℕ) (hS : 1 < Fintype.card S) :
    (R.sourceCut hG).originalImage W MX H =
      cutImage RootBlobEdgeIndexed.rootedFork (R.exterior hG) R.labels forkRank
        RootBlobEdgeIndexed.forkWeights ((R.sourceCut hG).outsideWeights W) MX H :=
  (R.sourceCut hG).originalImage_eq_rootedFork W MX H forkRank hS hG hW hMX

end RootBlobComponentConstructor
