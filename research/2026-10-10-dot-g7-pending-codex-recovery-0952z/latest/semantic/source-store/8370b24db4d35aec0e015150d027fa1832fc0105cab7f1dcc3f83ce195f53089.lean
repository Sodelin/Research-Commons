import GraphBlobPorts
import GraphGalls
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Actual cut-child blob-port counts for G1 extraction

Contributor: dot, 2026-10-03. These are original edge-indexed graph facts.
The accepted cut-child property is expressed directly as every outgoing edge
of an actual hybrid being a bridge. No two-port shape, kernel, core bound or
normal form is supplied as an input field. In particular, the original root
blob is recognized by actual bridge-deletion equivalence, not vertex inequality.
-/
namespace G1CutChildPorts
open Nanuq.Source
open scoped Classical BigOperators
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Literal accepted cut-child premise on original hybrid-child edge IDs. -/
def CutChild (N : RootedBinary V E X) : Prop :=
  ∀ e : E, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e

noncomputable def blobVertices (N : RootedBinary V E X) (b : N.graph.Blob) : Finset V :=
  Finset.univ.filter (fun v => N.graph.blobOf v = b)

noncomputable def inPorts (N : RootedBinary V E X) (b : N.graph.Blob) : Finset E :=
  Finset.univ.filter (fun e => N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.target e) = b)

noncomputable def outPorts (N : RootedBinary V E X) (b : N.graph.Blob) : Finset E :=
  Finset.univ.filter (fun e => N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.source e) = b)

noncomputable def allPorts (N : RootedBinary V E X) (b : N.graph.Blob) : Finset E :=
  outPorts N b ∪ inPorts N b

noncomputable def blobHybrids (N : RootedBinary V E X) (b : N.graph.Blob) : Finset V :=
  Finset.univ.filter (fun v => N.graph.IsHybrid v ∧ N.graph.blobOf v = b)

/-- In every actual rooted acyclic source, each hybrid parent edge has a
detour through the other parent. This does not need a supplied gall shape. -/
theorem actual_hybrid_parent_nonbridge (N : RootedBinary V E X) (e : E)
    (hh : N.graph.IsHybrid (N.graph.target e)) : ¬ N.graph.IsBridge e := by
  obtain ⟨f,hft,hfe⟩ := N.graph.hybrid_has_partner hh e
  have hroot : N.graph.ReachWithout e N.root (N.graph.source f) := by
    apply N.graph.dreach_without_of_no_return e (N.rooted (N.graph.source f))
    intro hreturn
    exact N.acyclic (N.graph.target e) (Relation.TransGen.tail' hreturn ⟨f,rfl,hft⟩)
  exact N.graph.not_bridge_of_detour
    ((N.root_on_source_side e).trans (hroot.tail ⟨f,hfe,Or.inl ⟨rfl,hft⟩⟩))

theorem actual_in_out_ports_disjoint (N : RootedBinary V E X) (b : N.graph.Blob) :
    Disjoint (outPorts N b) (inPorts N b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have he := (Finset.mem_filter.mp he).2
  have hf := (Finset.mem_filter.mp hf).2
  exact N.graph.bridge_blob_ne he.1 (he.2.trans hf.2.symm)

theorem actual_port_count (N : RootedBinary V E X) (b : N.graph.Blob) :
    (allPorts N b).card = (outPorts N b).card + (inPorts N b).card :=
  Finset.card_union_of_disjoint (actual_in_out_ports_disjoint N b)

/-- The actual nonroot blob has exactly ONE original entering cut edge.
This is derived from the existing actual quotient arborescence. -/
theorem actual_nonroot_incoming_port_one (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) : (inPorts N b).card = 1 := by
  have hpath := N.blob_quotient_rooted b
  rcases Relation.ReflTransGen.cases_tail hpath with hr | ⟨a,_,e,hes,het⟩
  · exact False.elim (hb hr)
  · apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨e.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property,het⟩,?_⟩
    intro f hf
    have hf := (Finset.mem_filter.mp hf).2
    have heq := N.blob_quotient_uniqueIncoming ⟨f,hf.1⟩ e (hf.2.trans het.symm)
    exact congrArg Subtype.val heq

lemma hybrid_child_exists_unique (N : RootedBinary V E X) (h : V) (hh : N.graph.IsHybrid h) :
    ∃ e : E, N.graph.source e = h ∧ ∀ f, N.graph.source f = h → f = e := by
  obtain ⟨e,he,hu⟩ := Finset.card_eq_one_iff_existsUnique.mp hh.2
  refine ⟨e,(Finset.mem_filter.mp he).2,?_⟩
  intro f hf
  exact hu f (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩)

noncomputable def hybridChild (N : RootedBinary V E X) (h : V) (hh : N.graph.IsHybrid h) : E :=
  Classical.choose (hybrid_child_exists_unique N h hh)

lemma hybridChild_source (N : RootedBinary V E X) (h : V) (hh : N.graph.IsHybrid h) :
    N.graph.source (hybridChild N h hh) = h :=
  (Classical.choose_spec (hybrid_child_exists_unique N h hh)).1

noncomputable def hybridToOutPort (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob) :
    (blobHybrids N b) → (outPorts N b) := fun h => by
  have hh := (Finset.mem_filter.mp h.property).2
  refine ⟨hybridChild N h.val hh.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩⟩
  · apply hc
    rw [hybridChild_source]
    exact hh.1
  · rw [hybridChild_source]
    exact hh.2

theorem actual_hybrid_port_injection (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob) :
    Function.Injective (hybridToOutPort N hc b) := by
  intro h k heq
  apply Subtype.ext
  have hs := congrArg (fun e : outPorts N b => N.graph.source e.val) heq
  simpa only [hybridToOutPort,hybridChild_source] using hs

theorem actual_hybrid_count_le_outports (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob) :
    (blobHybrids N b).card ≤ (outPorts N b).card := by
  have h := Fintype.card_le_of_injective (hybridToOutPort N hc b) (actual_hybrid_port_injection N hc b)
  simpa only [Fintype.card_coe] using h

/-- Original cut-child injectivity plus the one actual nonroot entry gives
h<=p-1. Root blobs instead retain h<=p. No graph-size budget is assumed. -/
theorem actual_nonroot_hybrid_port_bound (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) :
    (blobHybrids N b).card + 1 ≤ (allPorts N b).card := by
  rw [actual_port_count,actual_nonroot_incoming_port_one N b hb]
  exact Nat.add_le_add_right (actual_hybrid_count_le_outports N hc b) 1

theorem actual_root_hybrid_port_bound (N : RootedBinary V E X) (hc : CutChild N) :
    (blobHybrids N (N.graph.blobOf N.root)).card ≤ (allPorts N (N.graph.blobOf N.root)).card := by
  rw [actual_port_count]
  exact (actual_hybrid_count_le_outports N hc _).trans (Nat.le_add_right _ _)

/-- The original-edge port census is exactly the inherited actual quotient
BlobPort carrier, not a substitute notion of component boundary. -/
noncomputable def actualPortEquiv (N : RootedBinary V E X) (b : N.graph.Blob) :
    N.BlobPort b ≃ (allPorts N b) where
  toFun p := by
    refine ⟨p.val.val,?_⟩
    rcases p.property with hs | ht
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.val.property,hs⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.val.property,ht⟩))
  invFun p := by
    have h : N.graph.IsBridge p.val ∧
        (N.graph.blobOf (N.graph.source p.val) = b ∨ N.graph.blobOf (N.graph.target p.val) = b) := by
      rcases Finset.mem_union.mp p.property with hs | ht
      · have hs := (Finset.mem_filter.mp hs).2
        exact ⟨hs.1,Or.inl hs.2⟩
      · have ht := (Finset.mem_filter.mp ht).2
        exact ⟨ht.1,Or.inr ht.2⟩
    exact ⟨⟨p.val,h.1⟩,h.2⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

theorem actual_quotient_port_card (N : RootedBinary V E X) (b : N.graph.Blob) :
    Fintype.card (N.BlobPort b) = (allPorts N b).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (actualPortEquiv N b)

end G1CutChildPorts
