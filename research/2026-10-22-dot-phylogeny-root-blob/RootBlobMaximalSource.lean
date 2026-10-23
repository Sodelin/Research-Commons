import RootBlobBoundaryAdapter

/-!
# Binary, internally bridgeless root-blob admission
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler or kernel verification.

Connectedness and no internal cut edge are expressed by undirected walks
inside the induced region, with any one edge occurrence deleted. Maximality
is retained in the original-source record, although the proof is stronger
and does not use it. This is not a semidirected rooting theorem.
-/

open RootBlobEdgeIndexed RootBlobBoundaryGraph
namespace RootBlobMaximalSource
universe v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable (G : Network V E O)

noncomputable def incomingEdges (v : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => G.target e = v)
noncomputable def outgoingEdges (v : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => G.source e = v)
noncomputable def incidentEdges (v : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => G.source e = v ∨ G.target e = v)
noncomputable def internalIncident (R : Set V) (v : V) : Finset E := by
  classical
  exact (incidentEdges G v).filter (fun e => G.source e ∈ R ∧ G.target e ∈ R)

theorem incident_card (hG : GraphAdmitted G) (v : V) :
    (incidentEdges G v).card = (incomingEdges G v).card + (outgoingEdges G v).card := by
  classical
  have heq : incidentEdges G v = incomingEdges G v ∪ outgoingEdges G v := by
    ext e
    simp [incidentEdges, incomingEdges, outgoingEdges, or_comm]
  have hd : Disjoint (incomingEdges G v) (outgoingEdges G v) := by
    apply Finset.disjoint_left.mpr
    intro e hi ho
    have ht : G.target e = v := by simpa [incomingEdges] using hi
    have hs : G.source e = v := by simpa [outgoingEdges] using ho
    have hh := hG.2.2.1 e
    simpa [ht, hs] using hh
  rw [heq, Finset.card_union_of_disjoint hd]

/-- Literal binary indegree/outdegree conditions, separate from acyclic
single-root and leaf-observation admission. Parallel edges, if any, remain
separate occurrences; the published simple subclass is therefore included. -/
structure BinaryAdmission : Prop where
  root_degrees : (incomingEdges G G.root).card = 0 ∧ (outgoingEdges G G.root).card = 2
  leaf_degrees : ∀ o, (incomingEdges G (G.observed o)).card = 1 ∧
    (outgoingEdges G (G.observed o)).card = 0
  internal_degrees : ∀ v, v ≠ G.root → (∀ o, G.observed o ≠ v) →
    ((incomingEdges G v).card = 1 ∧ (outgoingEdges G v).card = 2) ∨
    ((incomingEdges G v).card = 2 ∧ (outgoingEdges G v).card = 1)

theorem binary_root_card (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    (incidentEdges G G.root).card = 2 := by
  rw [incident_card G hG, hB.root_degrees.1, hB.root_degrees.2]

theorem binary_leaf_card (hG : GraphAdmitted G) (hB : BinaryAdmission G) (o : O) :
    (incidentEdges G (G.observed o)).card = 1 := by
  rw [incident_card G hG, (hB.leaf_degrees o).1, (hB.leaf_degrees o).2]

theorem binary_card_le_three (hG : GraphAdmitted G) (hB : BinaryAdmission G) (v : V) :
    (incidentEdges G v).card ≤ 3 := by
  classical
  by_cases hr : v = G.root
  · subst v; rw [binary_root_card G hG hB]; omega
  by_cases ho : ∃ o, G.observed o = v
  · obtain ⟨o, rfl⟩ := ho
    rw [binary_leaf_card G hG hB]; omega
  have hn : ∀ o, G.observed o ≠ v := by simpa using ho
  rcases hB.internal_degrees v hr hn with h | h <;>
    rw [incident_card G hG, h.1, h.2] <;> omega

def UndirectedArc (R : Set V) (deleted : Finset E) (u v : V) : Prop :=
  ∃ e, e ∉ deleted ∧ G.source e ∈ R ∧ G.target e ∈ R ∧
    ((G.source e = u ∧ G.target e = v) ∨ (G.target e = u ∧ G.source e = v))

def RegionConnected (R : Set V) (deleted : Finset E) : Prop :=
  ∀ u ∈ R, ∀ v ∈ R, Relation.ReflTransGen (UndirectedArc G R deleted) u v

structure BridgelessRegion (R : Set V) : Prop where
  connected : RegionConnected G R ∅
  no_cut : ∀ e, RegionConnected G R {e}

theorem first_incident_on_walk {R : Set V} {deleted : Finset E} {u v : V}
    (huv : u ≠ v) (h : Relation.ReflTransGen (UndirectedArc G R deleted) u v) :
    ∃ e, e ∈ internalIncident G R u ∧ e ∉ deleted := by
  classical
  rcases h.cases_head with heq | ⟨c, hac, _⟩
  · exact False.elim (huv heq)
  obtain ⟨e, he, hs, ht, hi⟩ := hac
  refine ⟨e, ?_, he⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, hs, ht⟩
  rcases hi with h | h <;> simp [incidentEdges, h.1]

theorem internal_degree_ge_two {R : Set V} (hb : BridgelessRegion G R)
    (hr : G.root ∈ R) (hnt : ∃ v ∈ R, v ≠ G.root) {u : V} (hu : u ∈ R) :
    2 ≤ (internalIncident G R u).card := by
  classical
  obtain ⟨v, hv, hvr⟩ := hnt
  have hw : ∃ w ∈ R, u ≠ w := by
    by_cases hur : u = G.root
    · exact ⟨v, hv, by simpa [hur] using Ne.symm hvr⟩
    · exact ⟨G.root, hr, hur⟩
  obtain ⟨w, hw, huw⟩ := hw
  obtain ⟨e, he, _⟩ := first_incident_on_walk G huw (hb.connected u hu w hw)
  obtain ⟨f, hf, hfe⟩ := first_incident_on_walk G huw (hb.no_cut e u hu w hw)
  have hne : e ≠ f := by simpa [eq_comm] using hfe
  have hsub : ({e, f} : Finset E) ⊆ internalIncident G R u := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  simpa [hne] using hc

/-- This is a rooted, induced, nontrivial maximal bridgeless subgraph with
two boundary edge occurrences. It says nothing about arbitrary printed
two-boundary-vertex sub-blobs or how semidirected rootings collapse. -/
structure MaximalRootTwoBlob where
  vertices : Set V
  root_mem : G.root ∈ vertices
  nontrivial : ∃ v ∈ vertices, v ≠ G.root
  bridgeless : BridgelessRegion G vertices
  maximal : ∀ T : Set V, vertices ⊆ T → BridgelessRegion G T → T = vertices
  boundary_card : (boundaryEdges G vertices).card = 2

variable {G}
variable (B : MaximalRootTwoBlob G)

theorem hidden (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    ∀ o, G.observed o ∉ B.vertices := by
  intro o ho
  have hl := internal_degree_ge_two G B.bridgeless B.root_mem B.nontrivial ho
  have hu : (internalIncident G B.vertices (G.observed o)).card ≤
      (incidentEdges G (G.observed o)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [binary_leaf_card G hG hB] at hu
  omega

noncomputable def region (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    RootTwoBoundaryRegion G where
  vertices := B.vertices
  root_mem := B.root_mem
  hidden := B.hidden hG hB
  boundary_card := B.boundary_card

theorem incident_with_exit {v : V} (hv : v ∈ B.vertices) {e : E}
    (he : Outgoing G B.vertices e) (hs : G.source e = v) :
    (internalIncident G B.vertices v).card + 1 ≤ (incidentEdges G v).card := by
  classical
  have hn : e ∉ internalIncident G B.vertices v := by
    intro hm
    exact he.2 (Finset.mem_filter.mp hm).2.2
  have hsub : insert e (internalIncident G B.vertices v) ⊆ incidentEdges G v := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp [incidentEdges, hs]
    · exact (Finset.mem_filter.mp ha).1
  simpa [hn] using Finset.card_le_card hsub

theorem exit_source_nonroot (hG : GraphAdmitted G) (hB : BinaryAdmission G) {e : E}
    (he : Outgoing G B.vertices e) : G.source e ≠ G.root := by
  intro hs
  have hl := internal_degree_ge_two G B.bridgeless B.root_mem B.nontrivial B.root_mem
  have hu := B.incident_with_exit B.root_mem he hs
  rw [binary_root_card G hG hB] at hu
  omega

theorem exit_sources_distinct (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    {e f : E} (hef : e ≠ f) (he : Outgoing G B.vertices e)
    (hf : Outgoing G B.vertices f) : G.source e ≠ G.source f := by
  classical
  intro hs
  let v := G.source e
  have hv : v ∈ B.vertices := he.1
  have hne : e ∉ internalIncident G B.vertices v := by
    intro hm; exact he.2 (Finset.mem_filter.mp hm).2.2
  have hnf : f ∉ internalIncident G B.vertices v := by
    intro hm; exact hf.2 (Finset.mem_filter.mp hm).2.2
  have hsub : insert e (insert f (internalIncident G B.vertices v)) ⊆
      incidentEdges G v := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp [incidentEdges, v]
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp [incidentEdges, v, hs]
    · exact (Finset.mem_filter.mp ha).1
  have hu := Finset.card_le_card hsub
  simp [hef, hne, hnf] at hu
  have hl := internal_degree_ge_two G B.bridgeless B.root_mem B.nontrivial hv
  have hc := binary_card_le_three G hG hB v
  omega

/-- Adding one outside vertex joined by two distinct edges preserves
connectedness after any one deletion. This is the precise maximality
argument ruling out parallel root edges in the binary replacement. -/
theorem connected_insert_vertex {R : Set V} {deleted : Finset E} {c : V}
    (hc : RegionConnected G R deleted) {e : E}
    (he : e ∉ deleted) (hs : G.source e ∈ R) (ht : G.target e = c) :
    RegionConnected G (insert c R) deleted := by
  intro u hu v hv
  have lift : ∀ {a b}, Relation.ReflTransGen (UndirectedArc G R deleted) a b →
      Relation.ReflTransGen (UndirectedArc G (insert c R) deleted) a b := by
    apply Relation.ReflTransGen.mono
    rintro a b ⟨f, hf, hfs, hft, hdir⟩
    exact ⟨f, hf, Set.mem_insert_of_mem _ hfs, Set.mem_insert_of_mem _ hft, hdir⟩
  have forward : UndirectedArc G (insert c R) deleted (G.source e) c :=
    ⟨e, he, Set.mem_insert_of_mem _ hs, by simp [ht], Or.inl ⟨rfl, ht⟩⟩
  have backward : UndirectedArc G (insert c R) deleted c (G.source e) :=
    ⟨e, he, Set.mem_insert_of_mem _ hs, by simp [ht], Or.inr ⟨ht, rfl⟩⟩
  have hu' : Relation.ReflTransGen (UndirectedArc G (insert c R) deleted)
      u (G.source e) := by
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact Relation.ReflTransGen.single backward
    · exact lift (hc u hu _ hs)
  have hv' : Relation.ReflTransGen (UndirectedArc G (insert c R) deleted)
      (G.source e) v := by
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact Relation.ReflTransGen.single forward
    · exact lift (hc _ hs v hv)
  exact hu'.trans hv'

theorem exit_targets_distinct {e f : E} (hef : e ≠ f)
    (he : Outgoing G B.vertices e) (hf : Outgoing G B.vertices f) :
    G.target e ≠ G.target f := by
  classical
  intro ht
  let c := G.target e
  have hc : c ∉ B.vertices := he.2
  have hnew : BridgelessRegion G (insert c B.vertices) := by
    constructor
    · exact connected_insert_vertex (G := G) B.bridgeless.connected (by simp) he.1 rfl
    · intro d
      by_cases hed : e = d
      · have hfd : f ≠ d := by intro h; exact hef (hed.trans h.symm)
        exact connected_insert_vertex (G := G) (B.bridgeless.no_cut d)
          (by simpa using hfd) hf.1 ht.symm
      · exact connected_insert_vertex (G := G) (B.bridgeless.no_cut d)
          (by simpa using hed) he.1 rfl
  have heq := B.maximal (insert c B.vertices) (Set.subset_insert _ _) hnew
  have hcin : c ∈ insert c B.vertices := by simp
  rw [heq] at hcin
  exact hc hcin

end RootBlobMaximalSource
