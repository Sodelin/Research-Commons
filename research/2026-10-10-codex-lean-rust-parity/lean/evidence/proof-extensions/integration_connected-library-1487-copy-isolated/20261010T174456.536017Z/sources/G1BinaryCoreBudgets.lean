import G1ReducedCoreCounts

/-! Exact raw binary degree identities and reduced core V/E budgets.
Contributor: dot, 2026-10-03. No size budget is an admission field. -/
namespace G1BinaryCoreBudgets
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ReducedCoreCounts G1ActualGraphNormalization
open scoped Classical BigOperators
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def leafVertices (N : RootedBinary V E X) : Finset V := Finset.univ.image N.leaf

lemma actual_leaf_vertex_count (N : RootedBinary V E X) :
    (leafVertices N).card = Fintype.card X := by
  rw [leafVertices,Finset.card_image_of_injective _ N.leaf.injective,Finset.card_univ]

lemma mem_leafVertices (N : RootedBinary V E X) (v : V) :
    v ∈ leafVertices N ↔ ∃ x : X, N.leaf x = v := by simp [leafVertices]

lemma actual_in_degree_pointwise (N : RootedBinary V E X) (v : V) :
    N.graph.inDegree v + (if v = N.root then 1 else 0) =
      1 + (if N.graph.IsHybrid v then 1 else 0) := by
  by_cases hr : v = N.root
  · subst v; simp [N.root_degrees.1,N.root_degrees.2,EdgeGraph.IsHybrid]
  · by_cases hl : ∃ x : X, N.leaf x = v
    · obtain ⟨x,rfl⟩ := hl
      simp [hr,(N.leaf_degrees x).1,(N.leaf_degrees x).2,EdgeGraph.IsHybrid]
    · rcases N.internal_degrees v hr (fun x hx => hl ⟨x,hx⟩) with ht | hh
      · simp [hr,ht.1,ht.2,EdgeGraph.IsHybrid]
      · simp [hr,hh,hh.1]

lemma actual_out_degree_pointwise (N : RootedBinary V E X) (v : V) :
    N.graph.outDegree v + (if N.graph.IsHybrid v then 1 else 0) +
      2 * (if v ∈ leafVertices N then 1 else 0) = 2 := by
  by_cases hr : v = N.root
  · subst v
    have hn : N.root ∉ leafVertices N := by
      intro h; obtain ⟨x,hx⟩ := (mem_leafVertices N _).mp h; exact N.leaf_ne_root x hx
    simp [hn,N.root_degrees.1,N.root_degrees.2,EdgeGraph.IsHybrid]
  · by_cases hl : ∃ x : X, N.leaf x = v
    · obtain ⟨x,rfl⟩ := hl
      simp [(N.leaf_degrees x).1,(N.leaf_degrees x).2,EdgeGraph.IsHybrid,mem_leafVertices]
    · have hn : v ∉ leafVertices N := fun h => hl ((mem_leafVertices N _).mp h)
      rcases N.internal_degrees v hr (fun x hx => hl ⟨x,hx⟩) with ht | hh
      · simp [hn,ht.1,ht.2,EdgeGraph.IsHybrid]
      · simp [hn,hh,hh.2]

lemma sum_indicator {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    (∑ a : A, if p a then (1:ℕ) else 0) = (Finset.univ.filter p).card := by
  rw [← Finset.sum_filter]
  simp

lemma actual_total_indegree (N : RootedBinary V E X) :
    (∑ v : V, N.graph.inDegree v) = Fintype.card E := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
    (Finset.univ : Finset V) N.graph.target
  simpa [EdgeGraph.inDegree] using h

lemma actual_total_outdegree (N : RootedBinary V E X) :
    (∑ v : V, N.graph.outDegree v) = Fintype.card E := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
    (Finset.univ : Finset V) N.graph.source
  simpa [EdgeGraph.outDegree] using h

/-- Counting actual directed ORIGINAL edge incidences derives both binary
identities, including parallel edge occurrences. -/
theorem actual_binary_degree_identities (N : RootedBinary V E X) :
    Fintype.card E + 1 = Fintype.card V + (hybrids N).card ∧
      Fintype.card E + (hybrids N).card + 2 * Fintype.card X = 2 * Fintype.card V := by
  constructor
  · have h := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
      (fun v _ => actual_in_degree_pointwise N v)
    simp only [Finset.sum_add_distrib] at h
    rw [actual_total_indegree] at h
    simpa [sum_indicator,hybrids] using h
  · have h := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
      (fun v _ => actual_out_degree_pointwise N v)
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
    have hf : (∑ v : V, if v ∈ leafVertices N then (1:ℕ) else 0) = Fintype.card X := by
      calc
        _ = (Finset.univ.filter (fun v : V => v ∈ leafVertices N)).card := sum_indicator _
        _ = (leafVertices N).card := by simp
        _ = Fintype.card X := actual_leaf_vertex_count N
    simpa only [actual_total_outdegree,sum_indicator N.graph.IsHybrid,hf,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm,hybrids] using h


theorem actual_binary_vertex_edge_census (N : RootedBinary V E X) :
    Fintype.card V + 1 = 2 * Fintype.card X + 2 * (hybrids N).card ∧
      Fintype.card E + 2 = 2 * Fintype.card X + 3 * (hybrids N).card := by
  obtain ⟨hin,hout⟩ := actual_binary_degree_identities N
  omega

/-- Exact accepted reduced-core bounds, derived from actual LSA-rooted
binary CutChild and literal nonroot-two-port reducedness. -/
theorem actual_reduced_core_budgets (N : RootedBinary V E X) (hc : CutChild N)
    (hr : ∀ b : N.graph.Blob, b ≠ N.graph.blobOf N.root → Fintype.card (N.BlobPort b) ≠ 2) :
    (hybrids N).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card V ≤ 6 * Fintype.card X - 5 ∧
      Fintype.card E ≤ 8 * Fintype.card X - 8 := by
  have hh := actual_reduced_hybrid_budget N hc hr
  obtain ⟨hv,he⟩ := actual_binary_vertex_edge_census N
  omega

/-- A bounded reduced core is CONSTRUCTED from every admitted actual graph
by the proved finite splice sequence. Demographic labels are a separate
source-derived provenance obligation, never an arbitrary fitted rate. -/
theorem actual_finite_bounded_core (S : Source X) :
    ∃ T : Source X, Steps S T ∧ Reduced T ∧
      (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧
      Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 := by
  obtain ⟨T,hST,hr⟩ := actual_finite_normalization S
  obtain ⟨hh,hv,he⟩ := actual_reduced_core_budgets T.network T.cutChild hr
  exact ⟨T,hST,hr,hh,hv,he⟩

end G1BinaryCoreBudgets
