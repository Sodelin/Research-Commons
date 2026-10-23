import RootBlobRetainedPortSemantics
import RootBlobRelabeling

/-!
# Original-port graph partition and admitted retained fork
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No execution or kernel verification.

The outer-edge subtype is EXACTLY the original edges with outside targets.
In particular the two original cut edges are exterior, not interior factors
that may be changed by the realization. No subdivision is performed.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobEdgeIndexed RootBlobContextGlue
open RootBlobCutFactorization RootBlobRelabeling RootBlobRetainedPortSemantics
namespace RootBlobRetainedPortGraph
universe u v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable {O : Type x} [Fintype O]
variable (G : Network V E O)

structure PortComponent where
  vertices : Set V
  root_mem : G.root ∈ vertices
  ports : Fin 2 → V
  ports_mem : ∀ o, ports o ∈ vertices
  ports_injective : Function.Injective ports
  ports_nonroot : ∀ o, ports o ≠ G.root
  ancestral : ∀ e, G.target e ∈ vertices → G.source e ∈ vertices
  first_sink : ∀ e, G.target e ∈ vertices → G.source e ≠ ports 0
  outgoing_ports : ∀ e, G.source e ∈ vertices → G.target e ∉ vertices →
    ∃ o, ports o = G.source e
  port_exits : ∀ o, ∃ e, G.source e = ports o ∧ G.target e ∉ vertices
  hidden : ∀ o, G.observed o ∉ vertices

variable {G}
variable (R : PortComponent G)
abbrev Inside := {v : V // v ∈ R.vertices}
abbrev Outside := {v : V // v ∉ R.vertices}
abbrev InnerEdge := {e : E // G.target e ∈ R.vertices}
abbrev OuterEdge := {e : E // G.target e ∉ R.vertices}
noncomputable instance : Fintype R.Inside := Fintype.ofFinite _
noncomputable instance : Fintype R.Outside := Fintype.ofFinite _
noncomputable instance : Fintype R.InnerEdge := Fintype.ofFinite _
noncomputable instance : Fintype R.OuterEdge := Fintype.ofFinite _

def interior : Network R.Inside R.InnerEdge (Fin 2) where
  root := ⟨G.root, R.root_mem⟩
  observed := fun o => ⟨R.ports o, R.ports_mem o⟩
  source := fun e => ⟨G.source e.val, R.ancestral e.val e.property⟩
  target := fun e => ⟨G.target e.val, e.property⟩
  rank := fun v => G.rank v.val

theorem interior_admitted (hG : GraphAdmitted G) : PortAdmitted R.interior where
  observed_injective := fun _ _ h => R.ports_injective (congrArg Subtype.val h)
  observed_nonroot := fun o h => R.ports_nonroot o (congrArg Subtype.val h)
  edge_rank := fun e => hG.2.2.1 e.val
  target_nonroot := fun e h => hG.2.2.2.1 e.val (congrArg Subtype.val h)
  incoming := by
    intro v hv
    have hn : v.val ≠ G.root := by
      intro he
      exact hv (Subtype.ext he)
    obtain ⟨e, he⟩ := hG.2.2.2.2.1 v.val hn
    have hm : G.target e ∈ R.vertices := by simpa [he] using v.property
    exact ⟨⟨e, hm⟩, Subtype.ext he⟩
  first_sink := fun e h => R.first_sink e.val e.property (congrArg Subtype.val h)

noncomputable def exteriorSource (e : R.OuterEdge) : Sum (Fin 2) R.Outside := by
  classical
  exact if h : G.source e.val ∈ R.vertices then
    Sum.inl (Classical.choose (R.outgoing_ports e.val h e.property))
  else Sum.inr ⟨G.source e.val, h⟩

theorem exteriorSource_inl_iff (e : R.OuterEdge) (p : Fin 2) :
    R.exteriorSource e = Sum.inl p ↔ G.source e.val = R.ports p := by
  classical
  by_cases hs : G.source e.val ∈ R.vertices
  · have hc := Classical.choose_spec (R.outgoing_ports e.val hs e.property)
    simp only [exteriorSource, dif_pos hs, Sum.inl.injEq]
    constructor
    · intro hp
      simpa [hp] using hc.symm
    · intro hp
      exact R.ports_injective (hc.trans hp)
  · have hn : G.source e.val ≠ R.ports p := by
      intro hp
      exact hs (hp.symm ▸ R.ports_mem p)
    simp [exteriorSource, hs, hn]

theorem exteriorSource_inr_iff (e : R.OuterEdge) (v : R.Outside) :
    R.exteriorSource e = Sum.inr v ↔ G.source e.val = v.val := by
  classical
  by_cases hs : G.source e.val ∈ R.vertices
  · have hn : G.source e.val ≠ v.val := by
      intro hp
      exact v.property (hp ▸ hs)
    simp [exteriorSource, hs, hn]
  · simp only [exteriorSource, dif_neg hs, Sum.inr.injEq]
    exact Subtype.ext_iff

noncomputable def exterior (hG : GraphAdmitted G) : ExteriorDAG R.Outside R.OuterEdge where
  source := R.exteriorSource
  target := fun e => ⟨G.target e.val, e.property⟩
  rank := fun v => G.rank v.val
  internal_rank := by
    intro e v he
    have hs := (R.exteriorSource_inr_iff e v).mp he
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
  cases he : R.exteriorSource e with
  | inl p =>
    have hs := (R.exteriorSource_inl_iff e p).mp he
    simpa [boundarySource, interior, hs] using
      R.vertexEquiv_inside ⟨R.ports p, R.ports_mem p⟩
  | inr v =>
    have hs := (R.exteriorSource_inr_iff e v).mp he
    simpa [boundarySource, hs] using R.vertexEquiv_outside v

theorem graph_partition (hG : GraphAdmitted G) :
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

/-- An explicit admissible rank, rather than an arbitrary unused rank. -/
def forkRank : Sum (Fin 3) R.Outside → ℕ
  | Sum.inl v => if v = 0 then 0 else 1
  | Sum.inr v => G.rank v.val + 2

noncomputable def retainedFork (hG : GraphAdmitted G) :
    Network (Sum (Fin 3) R.Outside) (Sum (Fin 2) R.OuterEdge) O :=
  cutNetwork rootedFork (R.exterior hG) R.labels R.forkRank

def insideWeights (W : E → ℝ) : R.InnerEdge → ℝ := fun e => W e.val
def outsideWeights (W : E → ℝ) : R.OuterEdge → ℝ := fun e => W e.val
def retainedWeights (W : E → ℝ) : Sum (Fin 2) R.OuterEdge → ℝ :=
  Sum.elim forkWeights (R.outsideWeights W)

theorem fork_source_port (hG : GraphAdmitted G) (e : R.OuterEdge) (p : Fin 2) :
    (R.retainedFork hG).source (Sum.inr e) = Sum.inl (rootedFork.observed p) ↔
      G.source e.val = R.ports p := by
  classical
  change boundarySource rootedFork (R.exteriorSource e) =
    Sum.inl (rootedFork.observed p) ↔ _
  cases he : R.exteriorSource e with
  | inl q =>
    have hinj : rootedFork.observed q = rootedFork.observed p ↔ q = p :=
      RootBlobTreeMarginals.rootedFork_graph.1.eq_iff
    simpa only [boundarySource, Sum.elim_inl, Sum.inl.injEq, hinj, he,
      Sum.inl.injEq] using R.exteriorSource_inl_iff e p
  | inr v =>
    have hh := R.exteriorSource_inl_iff e p
    simpa [he, boundarySource] using hh

theorem fork_source_outside (hG : GraphAdmitted G) (e : R.OuterEdge) (v : R.Outside) :
    (R.retainedFork hG).source (Sum.inr e) = Sum.inr v ↔
      G.source e.val = v.val := by
  change boundarySource rootedFork (R.exteriorSource e) = Sum.inr v ↔ _
  cases he : R.exteriorSource e <;>
    simpa [he, boundarySource] using R.exteriorSource_inr_iff e v

theorem retainedFork_admitted (hG : GraphAdmitted G) :
    GraphAdmitted (R.retainedFork hG) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b he
    exact hG.1 (congrArg Subtype.val (Sum.inr.inj he))
  · intro o he
    exact Sum.noConfusion he
  · intro e
    cases e with
    | inl e =>
      fin_cases e <;> norm_num [retainedFork, cutNetwork, rootedFork, forkRank]
    | inr e =>
      cases hs : R.exteriorSource e with
      | inl p =>
        fin_cases p <;>
          simp [retainedFork, cutNetwork, exterior, boundarySource, rootedFork,
            forkRank, hs]
      | inr v =>
        have hr := (R.exterior hG).internal_rank e v hs
        simpa [retainedFork, cutNetwork, exterior, boundarySource, forkRank, hs] using
          Nat.add_lt_add_right hr 2
  · intro e he
    cases e with
    | inl e => fin_cases e <;> simp [retainedFork, cutNetwork, rootedFork] at he
    | inr e => exact Sum.noConfusion he
  · intro v hv
    cases v with
    | inl v =>
      fin_cases v
      · exact False.elim (hv rfl)
      · exact ⟨Sum.inl 0, rfl⟩
      · exact ⟨Sum.inl 1, rfl⟩
    | inr v =>
      have hn : v.val ≠ G.root := by
        intro he
        exact v.property (by simpa [he] using R.root_mem)
      obtain ⟨e, he⟩ := hG.2.2.2.2.1 v.val hn
      have ht : G.target e ∉ R.vertices := by simpa [he] using v.property
      exact ⟨Sum.inr ⟨e, ht⟩, congrArg Sum.inr (Subtype.ext he)⟩
  · intro v
    cases v with
    | inl v =>
      constructor
      · intro hs
        fin_cases v
        · exact False.elim (hs (Sum.inl 0) rfl)
        · obtain ⟨e, he, ht⟩ := R.port_exits 0
          exact False.elim (hs (Sum.inr ⟨e, ht⟩)
            ((R.fork_source_port hG ⟨e, ht⟩ 0).mpr he))
        · obtain ⟨e, he, ht⟩ := R.port_exits 1
          exact False.elim (hs (Sum.inr ⟨e, ht⟩)
            ((R.fork_source_port hG ⟨e, ht⟩ 1).mpr he))
      · rintro ⟨o, ho⟩
        exact False.elim (Sum.noConfusion ho)
    | inr v =>
      constructor
      · intro hs
        have hold : ∀ e, G.source e ≠ v.val := by
          intro e he
          have ht : G.target e ∉ R.vertices := by
            intro ht
            exact v.property (by simpa [he] using R.ancestral e ht)
          exact hs (Sum.inr ⟨e, ht⟩)
            ((R.fork_source_outside hG ⟨e, ht⟩ v).mpr he)
        obtain ⟨o, ho⟩ := (hG.2.2.2.2.2 v.val).mp hold
        exact ⟨o, congrArg Sum.inr (Subtype.ext ho)⟩
      · rintro ⟨o, ho⟩ e he
        have ho' : G.observed o = v.val := congrArg Subtype.val (Sum.inr.inj ho)
        cases e with
        | inl e => exact Sum.noConfusion he
        | inr e =>
          have hs := (R.fork_source_outside hG e v).mp he
          exact ((hG.2.2.2.2.2 _).mpr ⟨o, ho'⟩) e.val hs

end RootBlobRetainedPortGraph
