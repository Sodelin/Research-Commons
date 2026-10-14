import G4WholeProfileDetermination
import G1OriginalClassSameCoreAssembly
import G7OriginalSurvivalCoverage
import G7OriginalAdmission
import G1SplicedOriginalSwitching
import G4PairedNaturalTreeCore

/-!
Protected original COMMON physical representatives.
Contributor: dot (OpenAI), 12 October 2026. Source-only work in progress.
The intended complete endpoint is the accepted whole-COMMON physical
representative and finite original-code coverage theorem, not a local graph
bound or an ordinary-tree mixture substitute. ORIGINAL-COMPILER §4.2 counts
all protected edge/hybrid primitive IDs, including expanded template/boundary
support. Whole-COMMON §§8–9 and its mandatory COMMON-only correction supply
the hand argument. No source-law equality or representative bound is a field.
-/
namespace DotG4.ProtectedCommonRepresentative
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1CutChildPorts G1ReducedQuotientGeometry G1ReducedCoreCounts G1BinaryCoreBudgets
open scoped Classical BigOperators
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Every fixed primitive, actuator, template edge and boundary-incident edge
is included explicitly. A formula with many primitive dependencies contributes
all those dependencies, not one anonymous mark. -/
structure ProtectedIDs (N : RootedBinary V E X) where
  edges : Finset E
  hybrids : Finset (Hybrid N)

noncomputable def protectedCount (N : RootedBinary V E X) (P : ProtectedIDs N) : Nat :=
  P.edges.card + P.hybrids.card

/-- Both ends of a protected edge are retained at blob level. This includes
the two adjacent cells of a protected connector, when both are present. -/
noncomputable def protectedBlobs (N : RootedBinary V E X) (P : ProtectedIDs N) : Finset N.graph.Blob :=
  P.edges.image (fun e => N.graph.blobOf (N.graph.source e)) ∪
  P.edges.image (fun e => N.graph.blobOf (N.graph.target e)) ∪
  P.hybrids.image (fun h => N.graph.blobOf h.val)

lemma protectedBlobs_card (N : RootedBinary V E X) (P : ProtectedIDs N) :
    (protectedBlobs N P).card ≤ 2 * protectedCount N P := by
  have hs := Finset.card_image_le (s := P.edges) (f := fun e => N.graph.blobOf (N.graph.source e))
  have ht := Finset.card_image_le (s := P.edges) (f := fun e => N.graph.blobOf (N.graph.target e))
  have hh := Finset.card_image_le (s := P.hybrids) (f := fun h => N.graph.blobOf h.val)
  have h₁ := Finset.card_union_le
    (P.edges.image (fun e => N.graph.blobOf (N.graph.source e)))
    (P.edges.image (fun e => N.graph.blobOf (N.graph.target e)))
  have h₂ := Finset.card_union_le
    (P.edges.image (fun e => N.graph.blobOf (N.graph.source e)) ∪
      P.edges.image (fun e => N.graph.blobOf (N.graph.target e)))
    (P.hybrids.image (fun h => N.graph.blobOf h.val))
  unfold protectedBlobs protectedCount
  omega

/-- A literal structural stopping condition. It asserts no probability or
physical replacement law: only unprotected nonroot two-port blobs are absent. -/
def ReducedAway (N : RootedBinary V E X) (P : Finset N.graph.Blob) : Prop :=
  ∀ b : N.graph.Blob, b ≠ N.graph.blobOf N.root → b ∉ P →
    Fintype.card (N.BlobPort b) ≠ 2

lemma reducedAway_outport_bound (N : RootedBinary V E X) (P : Finset N.graph.Blob)
    (hr : ReducedAway N P) (b : N.graph.Blob) (hb : b ∈ internalBlobs N) :
    2 ≤ (outPorts N b).card + if b ∈ P then 1 else 0 := by
  have hn := (Finset.mem_filter.mp hb).2
  by_cases hp : b ∈ P
  · have h := actual_nonleaf_outport_positive N b hn.2
    simp only [if_pos hp]
    omega
  · have h₁ := actual_nonleaf_outport_positive N b hn.2
    have h₂ := actual_nonroot_incoming_port_one N b hn.1
    have h₃ := actual_port_count N b
    have h₄ := actual_quotient_port_card N b
    have h₅ := hr b hn.1 hp
    simp only [if_neg hp,add_zero]
    omega

lemma reducedAway_internal_budget (N : RootedBinary V E X) (P : Finset N.graph.Blob)
    (hr : ReducedAway N P) :
    (internalBlobs N).card + 2 ≤ Fintype.card X + P.card := by
  have hi := Finset.sum_le_sum (s := internalBlobs N) (f := fun _ => 2)
    (g := fun b => (outPorts N b).card + if b ∈ P then 1 else 0)
    (fun b hb => reducedAway_outport_bound N P hr b hb)
  have hfilter : ((internalBlobs N).filter (fun b => b ∈ P)).card ≤ P.card :=
    Finset.card_le_card (by intro b hb; exact (Finset.mem_filter.mp hb).2)
  have hsum : (∑ b ∈ internalBlobs N, if b ∈ P then 1 else 0) =
      ((internalBlobs N).filter (fun b => b ∈ P)).card := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib,hsum] at hi
  simp only [Finset.sum_const,smul_eq_mul] at hi
  have hd : Disjoint {N.graph.blobOf N.root} (internalBlobs N) := by
    apply Finset.disjoint_left.mpr
    intro b hb hi
    exact (Finset.mem_filter.mp hi).2.1 (Finset.mem_singleton.mp hb)
  have hs : {N.graph.blobOf N.root} ∪ internalBlobs N ⊆
      (Finset.univ : Finset N.graph.Blob) := Finset.subset_univ _
  have hc := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun b => (outPorts N b).card) hs (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_union hd,Finset.sum_singleton] at hc
  have hroot := actual_root_blob_outports_two N
  have hbc := actual_bridge_blob_census N
  have htc := actual_total_blob_census N
  rw [actual_total_outport_census] at hc
  omega

lemma reducedAway_hybrid_budget (N : RootedBinary V E X) (hc : CutChild N)
    (P : Finset N.graph.Blob) (hr : ReducedAway N P) :
    (hybrids N).card + 2 ≤ 2 * Fintype.card X + P.card := by
  have hh := Fintype.card_le_of_injective (hybridBridge N hc)
    (actual_hybrid_bridge_injective N hc)
  simp only [Fintype.card_coe] at hh
  have hi := reducedAway_internal_budget N P hr
  have hb := actual_total_blob_census N
  have he := actual_bridge_blob_census N
  omega

/-- The marked structural census follows from actual source degrees and
primitive incidence counting. Construction of this stopping condition and
all stochastic/parameter preservation are subsequent obligations. -/
theorem marked_reduced_core_budgets (N : RootedBinary V E X) (hc : CutChild N)
    (P : ProtectedIDs N) (hr : ReducedAway N (protectedBlobs N P)) :
    (hybrids N).card ≤ 2 * Fintype.card X - 2 + 2 * protectedCount N P ∧
      Fintype.card V ≤ 6 * Fintype.card X - 5 + 4 * protectedCount N P ∧
      Fintype.card E ≤ 8 * Fintype.card X - 8 + 6 * protectedCount N P := by
  have hh := reducedAway_hybrid_budget N hc (protectedBlobs N P) hr
  have hp := protectedBlobs_card N P
  obtain ⟨hv,he⟩ := actual_binary_vertex_edge_census N
  have hn := N.at_least_two_taxa
  omega


section ProtectedSplice
open G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1SplicedSourceAdmission G1SpliceDegrees

lemma protected_source_blob (N : RootedBinary V E X) (P : ProtectedIDs N)
    (e : E) (he : e ∈ P.edges) :
    N.graph.blobOf (N.graph.source e) ∈ protectedBlobs N P := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨e,he,rfl⟩

lemma protected_target_blob (N : RootedBinary V E X) (P : ProtectedIDs N)
    (e : E) (he : e ∈ P.edges) :
    N.graph.blobOf (N.graph.target e) ∈ protectedBlobs N P := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨e,he,rfl⟩

lemma protected_hybrid_blob (N : RootedBinary V E X) (P : ProtectedIDs N)
    (h : Hybrid N) (hh : h ∈ P.hybrids) :
    N.graph.blobOf h.val ∈ protectedBlobs N P :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨h,hh,rfl⟩)

/-- Every removed edge touches the original extracted blob. The protection
check therefore retains every marked raw edge, including adjacent connectors. -/
lemma removed_edge_touches_blob (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (e : E) (he : e ∈ removedEdges N b A) :
    N.graph.blobOf (N.graph.source e) = b ∨ N.graph.blobOf (N.graph.target e) = b := by
  simp only [removedEdges,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inr ((congrArg N.graph.blobOf A.entry_target).trans A.upper_in_blob)
  · exact Or.inl ((congrArg N.graph.blobOf A.child_source).trans A.hybrid_in_blob)
  · exact Or.inr ((congrArg N.graph.blobOf A.fragment.parents.target0).trans A.hybrid_in_blob)
  · exact Or.inr ((congrArg N.graph.blobOf A.fragment.parents.target1).trans A.hybrid_in_blob)

lemma protected_edge_retained (N : RootedBinary V E X) (P : ProtectedIDs N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P)
    (e : E) (he : e ∈ P.edges) : e ∉ removedEdges N b A := by
  intro h
  rcases removed_edge_touches_blob N b A e h with hs | ht
  · exact hb (hs ▸ protected_source_blob N P e he)
  · exact hb (ht ▸ protected_target_blob N P e he)

lemma protected_hybrid_retained (N : RootedBinary V E X) (P : ProtectedIDs N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P)
    (h : Hybrid N) (hh : h ∈ P.hybrids) :
    h.val ≠ A.fragment.upper ∧ h.val ≠ A.fragment.parents.hybrid := by
  have hn : N.graph.blobOf h.val ≠ b := by
    intro he
    exact hb (he ▸ protected_hybrid_blob N P h hh)
  exact ⟨fun he => hn ((congrArg N.graph.blobOf he).trans A.upper_in_blob),
    fun he => hn ((congrArg N.graph.blobOf he).trans A.hybrid_in_blob)⟩

noncomputable def protectedEdgeEmbedding (N : RootedBinary V E X) (P : ProtectedIDs N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P) :
    P.edges ↪ SplicedEdge N b A where
  toFun e := .inl ⟨e.val,protected_edge_retained N P b A hb e.val e.property⟩
  inj' e f h := by
    have hh := Sum.inl.inj h
    exact Subtype.ext (congrArg (fun z : RetainedEdge N b A => z.val) hh)

noncomputable def protectedHybridEmbedding (N : RootedBinary V E X) (hc : CutChild N)
    (P : ProtectedIDs N) (b : N.graph.Blob) (hroot : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P) :
    P.hybrids ↪ Hybrid (splicedNetwork N hc b hroot A) where
  toFun h := ⟨⟨h.val.val,protected_hybrid_retained N P b A hb h.val h.property⟩,
    (actual_splice_hybrid_iff N hc b A _).mpr h.val.property⟩
  inj' h k he := Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val) he))

/-- Protected identities are transported by explicit injective raw maps.
The newly created edge is anonymous and cannot replace a marked edge. -/
noncomputable def spliceProtectedIDs (N : RootedBinary V E X) (hc : CutChild N)
    (P : ProtectedIDs N) (b : N.graph.Blob) (hroot : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P) :
    ProtectedIDs (splicedNetwork N hc b hroot A) where
  edges := Finset.univ.map (protectedEdgeEmbedding N P b A hb)
  hybrids := Finset.univ.map (protectedHybridEmbedding N hc P b hroot A hb)

lemma spliceProtectedIDs_count (N : RootedBinary V E X) (hc : CutChild N)
    (P : ProtectedIDs N) (b : N.graph.Blob) (hroot : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P) :
    protectedCount (splicedNetwork N hc b hroot A)
      (spliceProtectedIDs N hc P b hroot A hb) = protectedCount N P := by
  simp only [protectedCount,spliceProtectedIDs,Finset.card_map,Finset.card_univ,Fintype.card_coe]

lemma splice_protected_edge_source (N : RootedBinary V E X) (hc : CutChild N)
    (P : ProtectedIDs N) (b : N.graph.Blob) (hroot : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P) (e : P.edges) :
    ((splicedNetwork N hc b hroot A).graph.source (protectedEdgeEmbedding N P b A hb e)).val =
      N.graph.source e.val := rfl

lemma splice_protected_edge_target (N : RootedBinary V E X) (hc : CutChild N)
    (P : ProtectedIDs N) (b : N.graph.Blob) (hroot : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (hb : b ∉ protectedBlobs N P) (e : P.edges) :
    ((splicedNetwork N hc b hroot A).graph.target (protectedEdgeEmbedding N P b A hb e)).val =
      N.graph.target e.val := rfl

end ProtectedSplice


section MarkedNormalization
open G1ActualGraphNormalization G1ActualTwoPortBlob G1DecoratedSpliceConstruction
open G1SplicedSourceAdmission G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ExactSemidirectedPartnerAdmission
universe u v w
variable {Y : Type w} [Fintype Y]

structure MarkedSource (Y : Type w) [Fintype Y] where
  source : Source.{u,v,w} Y
  marks : ProtectedIDs source.network

noncomputable def markedSplice (S : MarkedSource.{u,v,w} Y)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (hu : b ∉ protectedBlobs S.source.network S.marks) : MarkedSource Y :=
  let A := extractedBigon S.source.network S.source.cutChild b hb
    ((actual_quotient_port_card S.source.network b).symm.trans hp)
  ⟨splice S.source b hb hp,
    spliceProtectedIDs S.source.network S.source.cutChild S.marks b hb A hu⟩

inductive MarkedStep : MarkedSource.{u,v,w} Y → MarkedSource.{u,v,w} Y → Prop
  | splice (S : MarkedSource Y) (b : S.source.network.graph.Blob)
      (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
      (hp : Fintype.card (S.source.network.BlobPort b) = 2)
      (hu : b ∉ protectedBlobs S.source.network S.marks) :
      MarkedStep S (markedSplice S b hb hp hu)

abbrev MarkedSteps := Relation.ReflTransGen (MarkedStep (Y:=Y))

lemma markedStep_graph {S T : MarkedSource.{u,v,w} Y} (h : MarkedStep S T) :
    Step S.source T.source := by
  cases h with
  | splice b hb hp hu => exact Step.splice S.source b hb hp

lemma markedSteps_graph {S T : MarkedSource.{u,v,w} Y} (h : MarkedSteps S T) :
    Steps S.source T.source := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail prior step ih => exact Relation.ReflTransGen.tail ih (markedStep_graph step)

lemma markedStep_count {S T : MarkedSource.{u,v,w} Y} (h : MarkedStep S T) :
    protectedCount T.source.network T.marks = protectedCount S.source.network S.marks := by
  cases h with
  | splice b hb hp hu =>
    exact spliceProtectedIDs_count S.source.network S.source.cutChild S.marks b hb
      (extractedBigon S.source.network S.source.cutChild b hb
        ((actual_quotient_port_card S.source.network b).symm.trans hp)) hu

lemma markedSteps_count {S T : MarkedSource.{u,v,w} Y} (h : MarkedSteps S T) :
    protectedCount T.source.network T.marks = protectedCount S.source.network S.marks := by
  induction h with
  | refl => rfl
  | tail prior step ih => exact (markedStep_count step).trans ih

/-- Termination uses the existing actual two-vertex decrement. No reduced
output or desired preservation law is supplied. -/
theorem actual_finite_marked_normalization (S : MarkedSource.{u,v,w} Y) :
    ∃ T : MarkedSource Y, MarkedSteps S T ∧
      ReducedAway T.source.network (protectedBlobs T.source.network T.marks) := by
  have aux : ∀ n : Nat, ∀ S : MarkedSource Y, Fintype.card S.source.Vertex = n →
      ∃ T : MarkedSource Y, MarkedSteps S T ∧
        ReducedAway T.source.network (protectedBlobs T.source.network T.marks) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases hr : ReducedAway S.source.network (protectedBlobs S.source.network S.marks)
      · exact ⟨S,Relation.ReflTransGen.refl,hr⟩
      · unfold ReducedAway at hr
        push_neg at hr
        obtain ⟨b,hb,hu,hp⟩ := hr
        let T := markedSplice S b hb hp hu
        have hstep : MarkedStep S T := MarkedStep.splice S b hb hp hu
        have hsmall : Fintype.card T.source.Vertex < n :=
          hn ▸ actual_step_strictly_smaller (markedStep_graph hstep)
        obtain ⟨U,hTU,hU⟩ := ih _ hsmall T rfl
        exact ⟨U,(Relation.ReflTransGen.single hstep).trans hTU,hU⟩
  exact aux _ S rfl

/-- The actual protected structural core exists with the original numerical
allowances. This is graph/provenance normalization, not demographic collapse. -/
theorem actual_finite_marked_core (S : MarkedSource.{u,v,w} Y) :
    ∃ T : MarkedSource Y, MarkedSteps S T ∧
      protectedCount T.source.network T.marks = protectedCount S.source.network S.marks ∧
      ReducedAway T.source.network (protectedBlobs T.source.network T.marks) ∧
      (hybrids T.source.network).card ≤ 2 * Fintype.card Y - 2 +
        2 * protectedCount S.source.network S.marks ∧
      Fintype.card T.source.Vertex ≤ 6 * Fintype.card Y - 5 +
        4 * protectedCount S.source.network S.marks ∧
      Fintype.card T.source.Edge ≤ 8 * Fintype.card Y - 8 +
        6 * protectedCount S.source.network S.marks := by
  obtain ⟨T,hST,hr⟩ := actual_finite_marked_normalization S
  have hc := markedSteps_count hST
  obtain ⟨hh,hv,he⟩ := marked_reduced_core_budgets T.source.network T.source.cutChild T.marks hr
  rw [hc] at hh hv he
  exact ⟨T,hST,hc,hr,hh,hv,he⟩

lemma markedSteps_outer {S T : MarkedSource.{u,v,w} Y} (h : MarkedSteps S T)
    (hs : HasOuterSemidirectedPartner S.source) : HasOuterSemidirectedPartner T.source :=
  actual_steps_preserve_outer_semidirected_partner (markedSteps_graph h) hs

/-- The existing source-generated original-span decoration is reused on the
same graph chosen by marked normalization. Protected raw-ID preservation is
proved along these guarded steps separately. -/
theorem markedSteps_original_decoration (S T : MarkedSource.{u,v,w} Y)
    (H : OriginalParentRegistry S.source.network) (h : MarkedSteps S T) :
    ∃ D : Decoration S.source T.source, Originated S.source H D :=
  actual_steps_construct_decorations S.source H (markedSteps_graph h)
    (initialDecoration S.source) (Originated.initial)

/-- Every protected primitive remains a literal original coordinate of the
constructed decoration, rather than merely an unnamed isomorphic edge/site. -/
def ProtectedProvenance (O S : MarkedSource.{u,v,w} Y)
    (D : Decoration O.source S.source) : Prop :=
  (∀ e ∈ O.marks.edges, ∃ f ∈ S.marks.edges, D.recipe f = .raw e) ∧
  (∀ h ∈ O.marks.hybrids, ∃ k ∈ S.marks.hybrids, D.vertex k.val = h.val)

lemma protectedProvenance_initial (O : MarkedSource.{u,v,w} Y) :
    ProtectedProvenance O O (initialDecoration O.source) := by
  constructor
  · intro e he
    exact ⟨e,he,rfl⟩
  · intro h hh
    exact ⟨h,hh,rfl⟩

lemma protectedProvenance_splice (O S : MarkedSource.{u,v,w} Y)
    (H : OriginalParentRegistry O.source.network) (D : Decoration O.source S.source)
    (hd : ProtectedProvenance O S D)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (hu : b ∉ protectedBlobs S.source.network S.marks) :
    ProtectedProvenance O (markedSplice S b hb hp hu)
      (normalizedSpliceDecoration O.source S.source D H b hb hp) := by
  let A := extractedBigon S.source.network S.source.cutChild b hb
    ((actual_quotient_port_card S.source.network b).symm.trans hp)
  constructor
  · intro e he
    obtain ⟨f,hf,hraw⟩ := hd.1 e he
    let g := protectedEdgeEmbedding S.source.network S.marks b A hu ⟨f,hf⟩
    refine ⟨g,?_,?_⟩
    · exact Finset.mem_map.mpr ⟨⟨f,hf⟩,Finset.mem_univ _,rfl⟩
    · exact hraw
  · intro h hh
    obtain ⟨k,hk,hvertex⟩ := hd.2 h hh
    let l := protectedHybridEmbedding S.source.network S.source.cutChild S.marks
      b hb A hu ⟨k,hk⟩
    refine ⟨l,?_,?_⟩
    · exact Finset.mem_map.mpr ⟨⟨k,hk⟩,Finset.mem_univ _,rfl⟩
    · exact hvertex

/-- The same source-generated decoration witnesses every protected raw ID
through the entire constructed normalization. -/
theorem markedSteps_protected_decoration (O S T : MarkedSource.{u,v,w} Y)
    (H : OriginalParentRegistry O.source.network) (steps : MarkedSteps S T)
    (D : Decoration O.source S.source) (hd : Originated O.source H D)
    (hp : ProtectedProvenance O S D) :
    ∃ K : Decoration O.source T.source,
      Originated O.source H K ∧ ProtectedProvenance O T K := by
  induction steps with
  | refl => exact ⟨D,hd,hp⟩
  | @tail T U prior step ih =>
    obtain ⟨K,hK,hmarks⟩ := ih
    cases step with
    | splice b hb hc hu =>
      exact ⟨normalizedSpliceDecoration O.source T.source K H b hb hc,
        Originated.splice K hK b hb hc,
        protectedProvenance_splice O T H K hmarks b hb hc hu⟩

theorem actual_marked_core_original_provenance (O : MarkedSource.{u,v,w} Y)
    (H : OriginalParentRegistry O.source.network) :
    ∃ (T : MarkedSource Y) (D : Decoration O.source T.source),
      MarkedSteps O T ∧ Originated O.source H D ∧ ProtectedProvenance O T D ∧
      ReducedAway T.source.network (protectedBlobs T.source.network T.marks) := by
  obtain ⟨T,hT,hr⟩ := actual_finite_marked_normalization O
  obtain ⟨D,hd,hp⟩ := markedSteps_protected_decoration O O T H hT
    (initialDecoration O.source) Originated.initial (protectedProvenance_initial O)
  exact ⟨T,D,hT,hd,hp,hr⟩

end MarkedNormalization

section PhysicalSplice
open G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph G1SpliceDegrees
open G1SplicedSourceAdmission G1SplicedOriginalSwitching
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G7.OriginalSurvivalCoverage

/-- The remaining hybrid is the same original vertex; its private bit is not
renamed or reconstructed from an observed response. -/
noncomputable def retainedHybrid (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    Hybrid (splicedNetwork N hc b hb A) ↪ Hybrid N where
  toFun h := ⟨h.val.val,(actual_splice_hybrid_iff N hc b A h.val).mp h.property⟩
  inj' h k he := by
    have hv : h.val.val = k.val.val := congrArg (fun z : Hybrid N => z.val) he
    exact Subtype.ext (Subtype.ext hv)

lemma original_parent_retained (N : RootedBinary V E X) (hc : CutChild N)
    (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid (splicedNetwork N hc b hb A)) (bit : Bool) :
    (H.parents (retainedHybrid N hc b hb A h)).parent bit ∉ removedEdges N b A := by
  have ht := registry_parent_target N H (retainedHybrid N hc b hb A h) bit
  apply actual_in_edge_kept_of_ne_child N hc b A h.val _ ht
  intro he
  have hv := (retainedHybrid N hc b hb A h).property
  exact actual_child_target_not_hybrid N b A ((he ▸ ht).symm ▸ hv)

noncomputable def retainedParent (N : RootedBinary V E X) (hc : CutChild N)
    (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid (splicedNetwork N hc b hb A)) (bit : Bool) : SplicedEdge N b A :=
  .inl ⟨(H.parents (retainedHybrid N hc b hb A h)).parent bit,
    original_parent_retained N hc H b hb A h bit⟩

lemma retainedParent_target (N : RootedBinary V E X) (hc : CutChild N)
    (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid (splicedNetwork N hc b hb A)) (bit : Bool) :
    (splicedNetwork N hc b hb A).graph.target (retainedParent N hc H b hb A h bit) = h.val :=
  Subtype.ext (registry_parent_target N H (retainedHybrid N hc b hb A h) bit)

/-- Ordered parent occurrences, including parallel edges, are retained from the
original registry. No fresh arbitrary parent ordering is chosen. -/
noncomputable def splicedRegistry (N : RootedBinary V E X) (hc : CutChild N)
    (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    OriginalParentRegistry (splicedNetwork N hc b hb A) where
  parents h := {
    hybrid := h.val
    isHybrid := h.property
    parent0 := retainedParent N hc H b hb A h false
    parent1 := retainedParent N hc H b hb A h true
    target0 := retainedParent_target N hc H b hb A h false
    target1 := retainedParent_target N hc H b hb A h true
    different := by
      intro he
      have hh := congrArg Subtype.val (Sum.inl.inj he)
      exact (H.parents (retainedHybrid N hc b hb A h)).different hh }
  original_site _ := rfl

noncomputable def projectedBank (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (coin : Hybrid N → Bool) : Hybrid (splicedNetwork N hc b hb A) → Bool :=
  fun h => coin (retainedHybrid N hc b hb A h)

noncomputable def splicedProbabilities (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) : HybridProbabilities (splicedNetwork N hc b hb A) where
  gamma h := p.gamma (retainedHybrid N hc b hb A h)
  positive h := p.positive _
  below_one h := p.below_one _

/-- A single sample-independent physical tuple. Retained edge and ancestral
rates are literal; only the new bridge receives its summed exposure rate. -/
noncomputable def splicedRates (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    PositivePairRates (SplicedEdge N b A) where
  edge e := match e with
    | .inl f => r.edge f.val
    | .inr _ => (exposure N C r A.entry + exposure N C r A.fragment.parents.parent0 +
        exposure N C r A.child) /
      (C.age (N.graph.source A.entry) - C.age (N.graph.target A.child))
  edge_pos e := by
    cases e with
    | inl f => exact r.edge_pos f.val
    | inr u =>
      apply div_pos (add_pos (add_pos (exposure_pos N C r A.entry)
        (exposure_pos N C r A.fragment.parents.parent0)) (exposure_pos N C r A.child))
      exact sub_pos.mpr ((splicedCalendar N hc b hb A C).edge_older (.inr u))
  ancestral := r.ancestral
  ancestral_pos := r.ancestral_pos

lemma splicedRates_retained_exposure (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (e : RetainedEdge N b A) :
    exposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRates N hc C r b hb A) (.inl e) = exposure N C r e.val := rfl

lemma splicedRates_new_exposure (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    exposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRates N hc C r b hb A) (.inr ()) =
      exposure N C r A.entry + exposure N C r A.fragment.parents.parent0 + exposure N C r A.child := by
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr
    ((splicedCalendar N hc b hb A C).edge_older (.inr ()))))

lemma splicedRates_equal_arm_exposure (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (he : exposure N C r A.fragment.parents.parent0 = exposure N C r A.fragment.parents.parent1)
    (bit : Bool) :
    exposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRates N hc C r b hb A) (.inr ()) =
      exposure N C r A.entry + exposure N C r (A.fragment.parents.parent bit) + exposure N C r A.child := by
  rw [splicedRates_new_exposure]
  cases bit
  · rfl
  · exact congrArg (fun x => exposure N C r A.entry + x + exposure N C r A.child) he

open GProgram.G5.AttainedChronology UnifiedLean.Source.NativeCommonPairGerm
open G1SwitchingDescendantTransport DotG4.WeightedOrdinaryTreeLaw

lemma common_keep_at_original_hybrid (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) (h : Hybrid N)
    (e : E) (he : N.graph.target e = h.val) :
    (commonSwitching N H coin).keep e ↔ e = (H.parents h).parent (coin h) :=
  N.switchingOfChoices_keep_at_hybrid _ h e he

/-- Restriction of the actual bank induces exactly the actual spliced
switching with retained original parent ordering. -/
theorem commonSwitching_projectedBank (N : RootedBinary V E X) (hc : CutChild N)
    (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) (coin : CommonSeed N) :
    commonSwitching (splicedNetwork N hc b hb A) (splicedRegistry N hc H b hb A)
      (projectedBank N hc b hb A coin) =
      restrictSwitching N hc b hb A (commonSwitching N H coin) := by
  apply switching_ext
  intro e
  cases e with
  | inl e =>
    by_cases hh : N.graph.IsHybrid (N.graph.target e.val)
    · let h : Hybrid (splicedNetwork N hc b hb A) :=
        ⟨retainedTarget N hc b A e,(actual_splice_hybrid_iff N hc b A _).mpr hh⟩
      rw [common_keep_at_original_hybrid _ _ _ h _ rfl]
      change Sum.inl e = ((splicedRegistry N hc H b hb A).parents h).parent
          (projectedBank N hc b hb A coin h) ↔ (commonSwitching N H coin).keep e.val
      rw [common_keep_at_original_hybrid N H coin (retainedHybrid N hc b hb A h) e.val rfl]
      cases hbit : coin (retainedHybrid N hc b hb A h) <;>
        simp only [projectedBank,splicedRegistry,GProgram.G2.OriginalHybridParents.parent,hbit,
          retainedParent,Bool.false_eq_true,if_false,if_true,Sum.inl.injEq,Subtype.ext_iff]
    · have hh' : ¬(splicedNetwork N hc b hb A).graph.IsHybrid
          ((splicedNetwork N hc b hb A).graph.target (.inl e)) := by
        intro h
        exact hh ((actual_splice_hybrid_iff N hc b A _).mp h)
      exact iff_of_true ((commonSwitching _ _ _).ordinary _ hh')
        ((commonSwitching N H coin).ordinary e.val hh)
  | inr u =>
    have hn : ¬(splicedNetwork N hc b hb A).graph.IsHybrid
        ((splicedNetwork N hc b hb A).graph.target (.inr u)) := by
      intro h
      exact actual_child_target_not_hybrid N b A ((actual_splice_hybrid_iff N hc b A _).mp h)
    exact iff_of_true ((commonSwitching _ _ _).ordinary _ hn) True.intro

lemma edgeTaxa_of_not_kept (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) (e : E)
    (he : ¬(commonSwitching N H coin).keep e) : edgeTaxa N C H coin e = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact he (common_route_kept N C H coin x ((mem_edgeTaxa N C H coin e x).mp hx))

lemma retained_edgeTaxa (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (coin : CommonSeed N) (e : RetainedEdge N b A) :
    edgeTaxa (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc H b hb A) (projectedBank N hc b hb A coin) (.inl e) =
      edgeTaxa N C H coin e.val := by
  have hswitch := commonSwitching_projectedBank N hc H b hb A coin
  by_cases hk : (commonSwitching N H coin).keep e.val
  · have hk' : (commonSwitching (splicedNetwork N hc b hb A)
        (splicedRegistry N hc H b hb A) (projectedBank N hc b hb A coin)).keep (.inl e) := by
      rw [hswitch]
      exact hk
    ext x
    rw [edgeTaxa_selected_descendants (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc H b hb A) (projectedBank N hc b hb A coin) ⟨Sum.inl e,hk'⟩ x,
      edgeTaxa_selected_descendants N C H coin ⟨e.val,hk⟩ x]
    dsimp only
    rw [hswitch]
    exact actual_retained_selected_descendants_iff N hc b hb A (commonSwitching N H coin)
      (retainedTarget N hc b A e) (retainedTaxa N b A x)
  · have hk' : ¬(commonSwitching (splicedNetwork N hc b hb A)
        (splicedRegistry N hc H b hb A) (projectedBank N hc b hb A coin)).keep (.inl e) := by
      rw [hswitch]
      exact hk
    rw [edgeTaxa_of_not_kept _ _ _ _ _ hk',edgeTaxa_of_not_kept N C H coin e.val hk]

/-- The accepted raw descendant closure is lifted to each actual selected
switching by retaining its unique chosen parent occurrence. -/
lemma selected_hybrid_descendants (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (S : N.Switching) (x : X) :
    S.graph.DReach A.fragment.parents.hybrid (N.leaf x) ↔
      S.graph.DReach (N.graph.target A.child) (N.leaf x) :=
  G1ActualSelectedClusterTransport.actual_selected_hybrid_descendants N b A S x

lemma selected_upper_descendants (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (S : N.Switching) (x : X) :
    S.graph.DReach A.fragment.upper (N.leaf x) ↔
      S.graph.DReach (N.graph.target A.child) (N.leaf x) :=
  G1ActualSelectedClusterTransport.actual_selected_upper_descendants N hc b A S x

lemma entry_edgeTaxa (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (coin : CommonSeed N) :
    edgeTaxa N C H coin A.entry = edgeTaxa N C H coin A.child := by
  ext x
  rw [edgeTaxa_selected_descendants N C H coin ⟨A.entry,entry_kept N hc b A _⟩,
    edgeTaxa_selected_descendants N C H coin ⟨A.child,child_kept N b A _⟩ x,A.entry_target]
  exact selected_upper_descendants N hc b A _ x

lemma kept_parent_edgeTaxa (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (coin : CommonSeed N) (bit : Bool)
    (hk : (commonSwitching N H coin).keep (A.fragment.parents.parent bit)) :
    edgeTaxa N C H coin (A.fragment.parents.parent bit) = edgeTaxa N C H coin A.child := by
  ext x
  rw [edgeTaxa_selected_descendants N C H coin ⟨_,hk⟩,
    edgeTaxa_selected_descendants N C H coin ⟨A.child,child_kept N b A _⟩ x]
  have ht : N.graph.target (A.fragment.parents.parent bit) = A.fragment.parents.hybrid := by
    cases bit
    · exact A.fragment.parents.target0
    · exact A.fragment.parents.target1
  rw [ht]
  exact selected_hybrid_descendants N b A _ x

lemma new_edgeTaxa (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (coin : CommonSeed N) :
    edgeTaxa (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc H b hb A) (projectedBank N hc b hb A coin) (.inr ()) =
      edgeTaxa N C H coin A.child := by
  have hs := commonSwitching_projectedBank N hc H b hb A coin
  have hk : (commonSwitching (splicedNetwork N hc b hb A)
      (splicedRegistry N hc H b hb A) (projectedBank N hc b hb A coin)).keep (.inr ()) := by
    rw [hs]
    trivial
  ext x
  rw [edgeTaxa_selected_descendants (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc H b hb A) (projectedBank N hc b hb A coin) ⟨Sum.inr (),hk⟩ x,
    edgeTaxa_selected_descendants N C H coin ⟨A.child,child_kept N b A _⟩ x]
  dsimp only
  rw [hs]
  exact actual_retained_selected_descendants_iff N hc b hb A (commonSwitching N H coin)
    (descendantInterface N b A) (retainedTaxa N b A x)

lemma exactly_one_parent_kept (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (S : N.Switching) :
    (S.keep A.fragment.parents.parent0 ∧ ¬ S.keep A.fragment.parents.parent1) ∨
    (S.keep A.fragment.parents.parent1 ∧ ¬ S.keep A.fragment.parents.parent0) := by
  obtain ⟨e,ht,hk,hu⟩ := S.hybrid_unique A.fragment.parents.hybrid A.fragment.parents.isHybrid
  have hnot : ¬(S.keep A.fragment.parents.parent0 ∧ S.keep A.fragment.parents.parent1) := by
    rintro ⟨h0,h1⟩
    exact A.fragment.parents.different
      ((hu _ A.fragment.parents.target0 h0).trans (hu _ A.fragment.parents.target1 h1).symm)
  rcases actual_hybrid_parents_exhaustive N b A e ht with he | he
  · exact Or.inl ⟨he ▸ hk,fun h1 => hnot ⟨he ▸ hk,h1⟩⟩
  · exact Or.inr ⟨he ▸ hk,fun h0 => hnot ⟨h0,he ▸ hk⟩⟩

lemma sum_original_edges (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) {M : Type*} [AddCommMonoid M] (f : E → M) :
    (∑ e : E, f e) = (∑ e : RetainedEdge N b A, f e.val) +
      (f A.entry + f A.child + f A.fragment.parents.parent0 + f A.fragment.parents.parent1) := by
  have hm : (∑ e ∈ (removedEdges N b A)ᶜ, f e) =
      ∑ e : RetainedEdge N b A, f e.val :=
    Finset.sum_subtype ((removedEdges N b A)ᶜ) (fun e => Finset.mem_compl) f
  have hs := Finset.sum_compl_add_sum (removedEdges N b A) f
  rw [hm] at hs
  have hfour : (∑ e ∈ removedEdges N b A, f e) =
      f A.entry + f A.child + f A.fragment.parents.parent0 + f A.fragment.parents.parent1 := by
    simp [removedEdges,actual_entry_child_distinct N b A,actual_entry_parent0_distinct N b A,
      actual_entry_parent1_distinct N b A,actual_child_parent0_distinct N b A,
      actual_child_parent1_distinct N b A,A.fragment.parents.different,add_assoc]
  rw [hfour] at hs
  exact hs.symm

lemma spliced_edgeExposure_retained (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (e : RetainedEdge N b A) :
    edgeExposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRates N hc C r b hb A) (.inl e) = edgeExposure N C r e.val := rfl

lemma spliced_edgeExposure_new (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    edgeExposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRates N hc C r b hb A) (.inr ()) =
      edgeExposure N C r A.entry + edgeExposure N C r A.fragment.parents.parent0 +
        edgeExposure N C r A.child := by
  apply Subtype.ext
  exact splicedRates_new_exposure N hc C r b hb A

/-- The concrete equal-arm physical splice preserves the entire normalized
weighted tree for each original bank, before any averaging or sample choice. -/
theorem weightedNormalize_equal_arm_splice (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (he : exposure N C r A.fragment.parents.parent0 = exposure N C r A.fragment.parents.parent1)
    (coin : CommonSeed N) :
    weightedNormalize (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc H b hb A) (splicedRates N hc C r b hb A)
      (projectedBank N hc b hb A coin) = weightedNormalize N C H r coin := by
  funext D
  by_cases hD : D = ∅ ∨ D = Finset.univ
  · simp only [weightedNormalize,if_pos hD]
  have hempty : D ≠ ∅ := fun h => hD (Or.inl h)
  rw [weightedNormalize,if_neg hD,weightedNormalize,if_neg hD]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,show (default : Unit) = () from rfl]
  simp only [retained_edgeTaxa,spliced_edgeExposure_retained,new_edgeTaxa,spliced_edgeExposure_new]
  rw [sum_original_edges N b A]
  congr 1
  have he' : edgeExposure N C r A.fragment.parents.parent0 =
      edgeExposure N C r A.fragment.parents.parent1 := Subtype.ext he
  rw [entry_edgeTaxa N hc C H b A coin]
  rcases exactly_one_parent_kept N b A (commonSwitching N H coin) with ⟨h0,h1⟩ | ⟨h1,h0⟩
  · have hp0 : edgeTaxa N C H coin A.fragment.parents.parent0 = edgeTaxa N C H coin A.child := by
      simpa only [GProgram.G2.OriginalHybridParents.parent,Bool.false_eq_true,if_false] using
        kept_parent_edgeTaxa N C H b A coin false h0
    rw [hp0,edgeTaxa_of_not_kept N C H coin A.fragment.parents.parent1 h1]
    by_cases hd : edgeTaxa N C H coin A.child = D
    · simp only [if_pos hd,if_neg (Ne.symm hempty),add_zero]
      ac_rfl
    · simp only [if_neg hd,if_neg (Ne.symm hempty),add_zero]
  · have hp1 : edgeTaxa N C H coin A.fragment.parents.parent1 = edgeTaxa N C H coin A.child := by
      simpa only [GProgram.G2.OriginalHybridParents.parent,if_true] using
        kept_parent_edgeTaxa N C H b A coin true h1
    rw [edgeTaxa_of_not_kept N C H coin A.fragment.parents.parent0 h0,hp1]
    by_cases hd : edgeTaxa N C H coin A.child = D
    · simp only [if_pos hd,if_neg (Ne.symm hempty),add_zero,he']
      ac_rfl
    · simp only [if_neg hd,if_neg (Ne.symm hempty),add_zero]

open MeasureTheory ProbabilityTheory
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.OriginalFixedIDControls DotG4.WholeProfileDetermination

/-- Product-coordinate marginalization is applied to the actual original bank,
not to a product approximation of an observed joint forcing configuration. -/
lemma projected_original_bank (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) :
    ((originalRegisterMeasure N p).toPMF).map (projectedBank N hc b hb A) =
      (originalRegisterMeasure (splicedNetwork N hc b hb A) (splicedProbabilities N hc b hb A p)).toPMF := by
  classical
  letI : Fintype (Hybrid N) :=
    @Subtype.fintype V N.graph.IsHybrid (fun h => Classical.propDecidable _) inferInstance
  letI : Fintype (Hybrid (splicedNetwork N hc b hb A)) :=
    @Subtype.fintype _ (splicedNetwork N hc b hb A).graph.IsHybrid
      (fun h => Classical.propDecidable _) inferInstance
  let μ : Hybrid N → Measure Bool := fun h : Hybrid N => bitMeasure (originalGamma p h)
  have hind : iIndepFun (fun h (coin : Hybrid N → Bool) => coin h) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hret := iIndepFun.precomp (retainedHybrid N hc b hb A).injective hind
  have hm := hret.map_fun_eq_pi_map
    (fun h => (measurable_pi_apply (retainedHybrid N hc b hb A h)).aemeasurable)
  have hmeasure : (originalRegisterMeasure N p).map (projectedBank N hc b hb A) =
      originalRegisterMeasure (splicedNetwork N hc b hb A) (splicedProbabilities N hc b hb A p) := by
    unfold originalRegisterMeasure projectedBank
    change (Measure.pi μ).map (fun coin h => coin (retainedHybrid N hc b hb A h)) = _
    rw [hm]
    congr 1
    funext h
    rw [(measurePreserving_eval μ (retainedHybrid N hc b hb A h)).map_eq]
    rfl
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (projectedBank N hc b hb A) (originalRegisterMeasure N p).toPMF (measurable_of_countable _),Measure.toPMF_toMeasure,
    Measure.toPMF_toMeasure]
  exact hmeasure

noncomputable def projectedMask (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mask : OriginalMask N) : OriginalMask (splicedNetwork N hc b hb A) :=
  fun h => mask (retainedHybrid N hc b hb A h)

lemma projectedBank_override (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mask : OriginalMask N) (coin : CommonSeed N) :
    projectedBank N hc b hb A (overrideBank N mask coin) =
      overrideBank (splicedNetwork N hc b hb A) (projectedMask N hc b hb A mask)
        (projectedBank N hc b hb A coin) := rfl

/-- Full completed passive law of the actual physical splice, for every copy
allocation and every fixed original mask, with one unchanged original bank. -/
theorem actual_equal_arm_full_forest_splice
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (N : RootedBinary V E X) (hc : CutChild N) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (he : exposure N C r A.fragment.parents.parent0 = exposure N C r A.fragment.parents.parent1)
    (mask : OriginalMask N) (sample : Copy → X) :
    controlledFullForestLaw (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc H b hb A) (splicedProbabilities N hc b hb A p)
      (splicedRates N hc C r b hb A) (projectedMask N hc b hb A mask) sample =
      controlledFullForestLaw N C H p r mask sample := by
  rw [controlledFullForestLaw_tree_average,controlledFullForestLaw_tree_average,
    ← projected_original_bank N hc b hb A p,PMF.bind_map]
  congr 1
  funext coin
  dsimp only [Function.comp_apply]
  unfold maskedNormalizedTree
  rw [← projectedBank_override,weightedNormalize_equal_arm_splice N hc C H r b hb A he]

/-- The supplied whole-configuration law is retained verbatim. Its bits may be
correlated, and no deterministic summand has to be separately observed. -/
theorem actual_equal_arm_joint_row_splice
    {Copy Config : Type*} [Fintype Copy] [DecidableEq Copy] [Fintype Config]
    (N : RootedBinary V E X) (hc : CutChild N) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (he : exposure N C r A.fragment.parents.parent0 = exposure N C r A.fragment.parents.parent1)
    (ν : PMF Config) (masks : Config → OriginalMask N) (sample : Copy → X) :
    randomizedFullForestLaw (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc H b hb A) (splicedProbabilities N hc b hb A p)
      (splicedRates N hc C r b hb A) ν (fun cfg => projectedMask N hc b hb A (masks cfg)) sample =
      randomizedFullForestLaw N C H p r ν masks sample := by
  unfold randomizedFullForestLaw
  congr 1
  funext cfg
  exact actual_equal_arm_full_forest_splice N hc C H p r b hb A he (masks cfg) sample

end PhysicalSplice

section OriginalWordAccounting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1OriginalSpanRegion G1OriginalDecoratedSpan
open G1RetainedActorBoundarySites
universe u v w
variable {Y : Type w} [Fintype Y]

noncomputable def decorationHybrid (O T : Source.{u,v,w} Y) (D : Decoration O T) :
    Hybrid T.network ↪ Hybrid O.network where
  toFun h := ⟨D.vertex h.val,(actual_decoration_hybrid_iff O T D h.val).mp h.property⟩
  inj' h k he := Subtype.ext (D.vertex.injective (congrArg Subtype.val he))

noncomputable def actorHybrids (O T : Source.{u,v,w} Y) (D : Decoration O T)
    (e : BridgeActor T) : Finset (Hybrid O.network) :=
  Finset.univ.filter (fun h => h.val ∈ nodeRegion O (bridgeSpan O T D e.val e.property))

lemma actual_hybrid_owner_cover (O T : Source.{u,v,w} Y)
    (H : OriginalParentRegistry O.network) (D : Decoration O T) (hD : Originated O H D) :
    (Finset.univ : Finset (Hybrid O.network)) ⊆
      Finset.univ.map (decorationHybrid O T D) ∪
        Finset.univ.biUnion (actorHybrids O T D) := by
  intro h _
  rcases actual_original_node_retained_or_actor O H D hD h.val with ⟨v,hv⟩ | ⟨e,he⟩
  · apply Finset.mem_union_left
    have hh : T.network.graph.IsHybrid v :=
      (actual_decoration_hybrid_iff O T D v).mpr (hv.symm ▸ h.property)
    exact Finset.mem_map.mpr ⟨⟨v,hh⟩,Finset.mem_univ _,Subtype.ext hv⟩
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩

/-- Source-generated ownership, rather than a supplied graph-size assumption,
reduces the total physical hybrid count to the actual bridge-word counts. -/
theorem actual_hybrid_count_from_word_bounds (O T : Source.{u,v,w} Y)
    (H : OriginalParentRegistry O.network) (D : Decoration O T) (hD : Originated O H D)
    (L : Nat) (hL : ∀ e : BridgeActor T, (actorHybrids O T D e).card ≤ L) :
    Fintype.card (Hybrid O.network) ≤ Fintype.card (Hybrid T.network) + Fintype.card T.Edge * L := by
  have hcover := Finset.card_le_card (actual_hybrid_owner_cover O T H D hD)
  have hu := Finset.card_union_le (Finset.univ.map (decorationHybrid O T D))
    (Finset.univ.biUnion (actorHybrids O T D))
  have hb := Finset.card_biUnion_le (s := (Finset.univ : Finset (BridgeActor T)))
    (t := actorHybrids O T D)
  have hsum : (∑ e : BridgeActor T, (actorHybrids O T D e).card) ≤ Fintype.card (BridgeActor T) * L := by
    calc
      _ ≤ ∑ _ : BridgeActor T, L := Finset.sum_le_sum (fun e _ => hL e)
      _ = _ := by simp
  have hactors : Fintype.card (BridgeActor T) ≤ Fintype.card T.Edge :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Finset.card_univ,Finset.card_map] at hcover hu
  exact hcover.trans (hu.trans (Nat.add_le_add_left
    (hb.trans (hsum.trans (Nat.mul_le_mul_right L hactors))) _))

lemma actor_hybrid_not_retained (O T : Source.{u,v,w} Y)
    (H : OriginalParentRegistry O.network) (D : Decoration O T) (hD : Originated O H D)
    (e : BridgeActor T) (h : Hybrid O.network) (hh : h ∈ actorHybrids O T D e) :
    ¬ ∃ v : T.Vertex, D.vertex v = h.val := by
  rintro ⟨v,hv⟩
  have hm := (Finset.mem_filter.mp hh).2
  have he := actual_retained_actor_node_is_its_input O H D hD e.val e.property v (hv.symm ▸ hm)
  have hh' : T.network.graph.IsHybrid v :=
    (actual_decoration_hybrid_iff O T D v).mpr (hv.symm ▸ h.property)
  have hd := actual_original_bridge_target_ordinary T e.val e.property
  have htwo := hh'.1
  rw [he,hd] at htwo
  omega

end OriginalWordAccounting

section SpanSites
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanRegion
open G1OriginalSpanCalendarDecomposition G1NonrootBigonKernel
universe u v w
variable {Y : Type w} [Fintype Y]

noncomputable def spanSites (O : Source.{u,v,w} Y) {a b : O.Vertex} :
    OriginalSpan O.network a b → List (Hybrid O.network)
  | .edge _ _ => []
  | .bigon B => [⟨B.parents.hybrid,B.parents.isHybrid⟩]
  | .append first last => spanSites O first ++ spanSites O last

lemma spanSite_age_bounds (O : Source.{u,v,w} Y) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (h : Hybrid O.network) (hh : h ∈ spanSites O word) :
    O.calendar.age a ≤ O.calendar.age h.val ∧ O.calendar.age h.val < O.calendar.age b := by
  induction word with
  | edge e hd => simp only [spanSites,List.not_mem_nil] at hh
  | bigon B =>
    have he : h = ⟨B.parents.hybrid,B.parents.isHybrid⟩ := List.mem_singleton.mp hh
    subst h
    exact ⟨le_rfl,actual_span_dates_strict O.network O.calendar (.bigon B)⟩
  | @append a b c first last ihfirst ihlast =>
    rcases List.mem_append.mp hh with hh | hh
    · have hi := ihfirst hh
      exact ⟨hi.1,hi.2.trans (actual_span_dates_strict O.network O.calendar last)⟩
    · have hi := ihlast hh
      exact ⟨(actual_span_dates_strict O.network O.calendar first).le.trans hi.1,hi.2⟩

lemma spanSites_nodup (O : Source.{u,v,w} Y) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) : (spanSites O word).Nodup := by
  induction word with
  | edge e hd => exact List.nodup_nil
  | bigon B => exact List.nodup_singleton _
  | append first last ihfirst ihlast =>
    rw [spanSites,List.nodup_append]
    refine ⟨ihfirst,ihlast,?_⟩
    intro h hh k hk he
    subst k
    exact (not_lt_of_ge (spanSite_age_bounds O last h hk).1)
      (spanSite_age_bounds O first h hh).2

lemma hybrid_mem_nodeRegion_iff (O : Source.{u,v,w} Y) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (h : Hybrid O.network) :
    h.val ∈ nodeRegion O word ↔ h ∈ spanSites O word := by
  induction word with
  | edge e hd =>
    have hn : h.val ≠ O.network.graph.target e := by
      intro he
      have hh := h.property.1
      rw [he,hd] at hh
      omega
    simp only [nodeRegion,spanSites,Finset.mem_singleton,List.not_mem_nil,iff_false]
    exact hn
  | bigon B =>
    simp only [nodeRegion,spanSites,Finset.mem_singleton,List.mem_singleton]
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  | append first last ihfirst ihlast =>
    simp only [nodeRegion,spanSites,Finset.mem_union,List.mem_append,ihfirst,ihlast]

lemma actorHybrids_eq_sites (O T : Source.{u,v,w} Y) (D : G1DecoratedOriginalProvenance.Decoration O T)
    (e : G1OriginalActorOperationOwnership.BridgeActor T) :
    actorHybrids O T D e =
      (spanSites O (G1DecoratedOriginalProvenance.bridgeSpan O T D e.val e.property)).toFinset := by
  ext h
  simp only [actorHybrids,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset,
    hybrid_mem_nodeRegion_iff]

lemma actorHybrids_card_sites (O T : Source.{u,v,w} Y) (D : G1DecoratedOriginalProvenance.Decoration O T)
    (e : G1OriginalActorOperationOwnership.BridgeActor T) :
    (actorHybrids O T D e).card =
      (spanSites O (G1DecoratedOriginalProvenance.bridgeSpan O T D e.val e.property)).length := by
  rw [actorHybrids_eq_sites,List.toFinset_card_of_nodup (spanSites_nodup O _)]

end SpanSites

section PhysicalNormalization
open G1ActualGraphNormalization G1ActualTwoPortBlob G1SplicedSourceAdmission
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.OriginalFixedIDControls DotG4.WholeProfileDetermination
open GProgram.G7.OriginalSurvivalCoverage
universe u v w z q
variable {Y : Type w} [Fintype Y]

/-- Actual physical data only. In particular no kernel equality, source-size
bound or desired representative property is stored in this structure. -/
structure PhysicalMarkedSource (Y : Type w) [Fintype Y] where
  marked : MarkedSource.{u,v,w} Y
  registry : OriginalParentRegistry marked.source.network
  probabilities : HybridProbabilities marked.source.network
  rates : PositivePairRates marked.source.Edge

noncomputable def physicalSplice (S : PhysicalMarkedSource.{u,v,w} Y)
    (b : S.marked.source.network.graph.Blob)
    (hb : b ≠ S.marked.source.network.graph.blobOf S.marked.source.network.root)
    (hp : Fintype.card (S.marked.source.network.BlobPort b) = 2)
    (hu : b ∉ protectedBlobs S.marked.source.network S.marked.marks) : PhysicalMarkedSource Y :=
  let A := extractedBigon S.marked.source.network S.marked.source.cutChild b hb
    ((actual_quotient_port_card S.marked.source.network b).symm.trans hp)
  { marked := markedSplice S.marked b hb hp hu
    registry := splicedRegistry S.marked.source.network S.marked.source.cutChild S.registry b hb A
    probabilities := splicedProbabilities S.marked.source.network S.marked.source.cutChild b hb A S.probabilities
    rates := splicedRates S.marked.source.network S.marked.source.cutChild S.marked.source.calendar S.rates b hb A }

def EqualExtractedArms (S : PhysicalMarkedSource.{u,v,w} Y)
    (b : S.marked.source.network.graph.Blob)
    (hb : b ≠ S.marked.source.network.graph.blobOf S.marked.source.network.root)
    (hp : Fintype.card (S.marked.source.network.BlobPort b) = 2) : Prop :=
  let A := extractedBigon S.marked.source.network S.marked.source.cutChild b hb
    ((actual_quotient_port_card S.marked.source.network b).symm.trans hp)
  exposure S.marked.source.network S.marked.source.calendar S.rates A.fragment.parents.parent0 =
    exposure S.marked.source.network S.marked.source.calendar S.rates A.fragment.parents.parent1

inductive PhysicalStep : PhysicalMarkedSource.{u,v,w} Y → PhysicalMarkedSource.{u,v,w} Y → Prop
  | splice (S : PhysicalMarkedSource Y) (b : S.marked.source.network.graph.Blob)
      (hb : b ≠ S.marked.source.network.graph.blobOf S.marked.source.network.root)
      (hp : Fintype.card (S.marked.source.network.BlobPort b) = 2)
      (hu : b ∉ protectedBlobs S.marked.source.network S.marked.marks)
      (he : EqualExtractedArms S b hb hp) : PhysicalStep S (physicalSplice S b hb hp hu)

abbrev PhysicalSteps := Relation.ReflTransGen (PhysicalStep (Y:=Y))

lemma physicalStep_marked {S T : PhysicalMarkedSource.{u,v,w} Y} (h : PhysicalStep S T) :
    MarkedStep S.marked T.marked := by
  cases h with
  | splice b hb hp hu he => exact MarkedStep.splice S.marked b hb hp hu

lemma physicalSteps_marked {S T : PhysicalMarkedSource.{u,v,w} Y} (h : PhysicalSteps S T) :
    MarkedSteps S.marked T.marked := by
  induction h with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (physicalStep_marked step)

def EqualArmReduced (S : PhysicalMarkedSource.{u,v,w} Y) : Prop :=
  ∀ b (hb : b ≠ S.marked.source.network.graph.blobOf S.marked.source.network.root)
    (hp : Fintype.card (S.marked.source.network.BlobPort b) = 2),
    b ∉ protectedBlobs S.marked.source.network S.marked.marks → ¬ EqualExtractedArms S b hb hp

/-- Termination constructs an actual positive physical source with no remaining
eligible equal-arm cell. All rates and probabilities were defined before any
copy allocation or experimental row. -/
theorem actual_finite_equal_arm_reduction (S : PhysicalMarkedSource.{u,v,w} Y) :
    ∃ T : PhysicalMarkedSource Y, PhysicalSteps S T ∧ EqualArmReduced T := by
  have aux : ∀ n : Nat, ∀ S : PhysicalMarkedSource Y,
      Fintype.card S.marked.source.Vertex = n →
      ∃ T : PhysicalMarkedSource Y, PhysicalSteps S T ∧ EqualArmReduced T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases hr : EqualArmReduced S
      · exact ⟨S,.refl,hr⟩
      · unfold EqualArmReduced at hr
        push_neg at hr
        obtain ⟨b,hb,hp,hu,he⟩ := hr
        let T := physicalSplice S b hb hp hu
        have hs : PhysicalStep S T := PhysicalStep.splice S b hb hp hu he
        have hsmall : Fintype.card T.marked.source.Vertex < n :=
          hn ▸ actual_step_strictly_smaller (markedStep_graph (physicalStep_marked hs))
        obtain ⟨U,hTU,hU⟩ := ih _ hsmall T rfl
        exact ⟨U,(Relation.ReflTransGen.single hs).trans hTU,hU⟩
  exact aux _ S rfl

/- Whole-row law transport is derived from actual splice steps. The existential
embedding is a retained original hybrid-ID map and precedes all allocations. -/

end PhysicalNormalization

section OriginalBlobRetention
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1DecoratedSpliceConstruction G1ActualTwoPortBlob G1BigonSpliceGraph G1SplicedSourceAdmission
open G1LiftedOriginalBigon
universe u v w
variable {Y : Type w} [Fintype Y]

/-- Splices delete whole blobs. Every blob containing a retained vertex keeps
all of its original vertices, not merely the original root blob. -/
def WholeRetainedBlobs (O T : Source.{u,v,w} Y) (D : Decoration O T) : Prop :=
  ∀ x : T.Vertex, ∀ v : O.Vertex,
    O.network.graph.SameBlob (D.vertex x) v → ∃ y : T.Vertex, D.vertex y = v

lemma wholeRetainedBlobs_splice (O T : Source.{u,v,w} Y)
    (D : Decoration O T) (H : OriginalParentRegistry O.network)
    (hD : WholeRetainedBlobs O T D) (b : T.network.graph.Blob)
    (hb : b ≠ T.network.graph.blobOf T.network.root) (A : ActualBlobBigon T.network b) :
    WholeRetainedBlobs O (actualSplicedSource T b hb A) (spliceDecoration O T D H b hb A) := by
  intro x v hv
  obtain ⟨y,hy⟩ := hD x.val v hv
  have hxy : T.network.graph.SameBlob x.val y :=
    (D.sameBlob x.val y).mpr (hy.symm ▸ hv)
  have hxb : T.network.graph.blobOf x.val ≠ b := by
    intro hx
    rcases (A.vertices_exact x.val).mp hx with h | h
    · exact x.property.1 h
    · exact x.property.2 h
  have hykeep : y ≠ A.fragment.upper ∧ y ≠ A.fragment.parents.hybrid := by
    have he : T.network.graph.blobOf x.val = T.network.graph.blobOf y := Quotient.sound hxy
    constructor
    · intro h
      exact hxb (he.trans ((congrArg T.network.graph.blobOf h).trans A.upper_in_blob))
    · intro h
      exact hxb (he.trans ((congrArg T.network.graph.blobOf h).trans A.hybrid_in_blob))
  exact ⟨⟨y,hykeep⟩,hy⟩

lemma actual_originated_whole_retained_blobs (O : Source.{u,v,w} Y)
    (H : OriginalParentRegistry O.network) {T : Source Y}
    (D : Decoration O T) (hD : Originated O H D) : WholeRetainedBlobs O T D := by
  induction hD with
  | initial => exact fun x v _ => ⟨v,rfl⟩
  | @splice T D prior b hb hp ih =>
    exact wholeRetainedBlobs_splice O T D H ih b hb _

lemma lifted_blob_nonroot (O T : Source.{u,v,w} Y) (D : Decoration O T)
    (b : T.network.graph.Blob) (hb : b ≠ T.network.graph.blobOf T.network.root)
    (A : ActualBlobBigon T.network b) :
    O.network.graph.blobOf (D.vertex A.fragment.upper) ≠ O.network.graph.blobOf O.network.root := by
  intro h
  have hsame : O.network.graph.SameBlob (D.vertex A.fragment.upper) (D.vertex T.network.root) := by
    exact @Quotient.exact _ O.network.graph.blobSetoid _ _
      (h.trans (congrArg O.network.graph.blobOf D.root).symm)
  have ht := @Quotient.sound _ T.network.graph.blobSetoid _ _ ((D.sameBlob _ _).mpr hsame)
  exact hb (A.upper_in_blob.symm.trans ht)

lemma lifted_blob_vertices (O T : Source.{u,v,w} Y) (H : OriginalParentRegistry O.network)
    (D : Decoration O T) (hD : Originated O H D)
    (b : T.network.graph.Blob) (A : ActualBlobBigon T.network b) (v : O.Vertex) :
    O.network.graph.blobOf v = O.network.graph.blobOf (D.vertex A.fragment.upper) ↔
      v = D.vertex A.fragment.upper ∨ v = D.vertex A.fragment.parents.hybrid := by
  constructor
  · intro hv
    obtain ⟨y,hy⟩ := actual_originated_whole_retained_blobs O H D hD A.fragment.upper v
      (Quotient.exact hv.symm)
    have hsame : T.network.graph.SameBlob y A.fragment.upper :=
      (D.sameBlob _ _).mpr (hy.symm ▸ Quotient.exact hv)
    have hyb : T.network.graph.blobOf y = b := (Quotient.sound hsame).trans A.upper_in_blob
    rcases (A.vertices_exact y).mp hyb with he | he
    · exact Or.inl (hy.symm.trans (congrArg D.vertex he))
    · exact Or.inr (hy.symm.trans (congrArg D.vertex he))
  · rintro (rfl | rfl)
    · rfl
    · apply Quotient.sound
      apply (D.sameBlob _ _).mp
      exact Quotient.exact (A.hybrid_in_blob.trans A.upper_in_blob.symm)

lemma lifted_blob_two_ports (O T : Source.{u,v,w} Y) (H : OriginalParentRegistry O.network)
    (D : Decoration O T) (hD : Originated O H D)
    (b : T.network.graph.Blob) (hb : b ≠ T.network.graph.blobOf T.network.root)
    (A : ActualBlobBigon T.network b) :
    Fintype.card (O.network.BlobPort (O.network.graph.blobOf (D.vertex A.fragment.upper))) = 2 := by
  let u := D.vertex A.fragment.upper
  let h := D.vertex A.fragment.parents.hybrid
  let blob := O.network.graph.blobOf u
  have hh : O.network.graph.IsHybrid h :=
    (actual_decoration_hybrid_iff O T D _).mp A.fragment.parents.isHybrid
  let child := hybridChild O.network h hh
  have hcs : O.network.graph.source child = h := hybridChild_source O.network h hh
  have hcb : O.network.graph.IsBridge child := O.cutChild child (hcs.symm ▸ hh)
  have hhb : O.network.graph.blobOf h = blob :=
    (lifted_blob_vertices O T H D hD b A h).mpr (Or.inr rfl)
  have hout : outPorts O.network blob = {child} := by
    ext e
    constructor
    · intro he
      have he' := he
      simp only [outPorts,Finset.mem_filter,Finset.mem_univ,true_and] at he'
      obtain ⟨hebridge,hes⟩ := he' 
      rcases (lifted_blob_vertices O T H D hD b A (O.network.graph.source e)).mp hes with hs | hs
      · let es := Finset.univ.filter (fun f : O.Edge => O.network.graph.source f = u)
        have h0 : rawOriginalParent O T D b A false ∈ es :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,actual_raw_original_parent_source O T D b A false⟩
        have h1 : rawOriginalParent O T D b A true ∈ es :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,actual_raw_original_parent_source O T D b A true⟩
        have hd : es.card = 2 :=
          (D.outdegree A.fragment.upper).symm.trans
            (G1BigonFootprint.actual_upper_tree_degrees T.network T.cutChild b A).2
        have hex := edge_pair_exhaustive es _ _ (actual_raw_original_parents_different O T D b A)
          h0 h1 hd e (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩)
        have heh : O.network.graph.IsHybrid (O.network.graph.target e) := by
          rcases hex with he | he
          · rw [he,actual_raw_original_parent_target]
            exact hh
          · rw [he,actual_raw_original_parent_target]
            exact hh
        exact False.elim (actual_hybrid_parent_nonbridge O.network e heh hebridge)
      · apply Finset.mem_singleton.mpr
        exact (Classical.choose_spec (hybrid_child_exists_unique O.network h hh)).2 e hs
    · intro he
      have he := Finset.mem_singleton.mp he
      subst e
      simp only [outPorts,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hcb,(congrArg O.network.graph.blobOf hcs).trans hhb⟩
  rw [actual_quotient_port_card,actual_port_count,hout,Finset.card_singleton,
    actual_nonroot_incoming_port_one O.network blob (lifted_blob_nonroot O T D b hb A)]

lemma protected_blob_pulls_back (O T : MarkedSource.{u,v,w} Y)
    (D : Decoration O.source T.source) (hp : ProtectedProvenance O T D)
    (x : T.source.Vertex)
    (hx : O.source.network.graph.blobOf (D.vertex x) ∈ protectedBlobs O.source.network O.marks) :
    T.source.network.graph.blobOf x ∈ protectedBlobs T.source.network T.marks := by
  have hblob : ∀ y : T.source.Vertex,
      O.source.network.graph.blobOf (D.vertex y) = O.source.network.graph.blobOf (D.vertex x) →
        T.source.network.graph.blobOf y = T.source.network.graph.blobOf x := by
    intro y he
    exact Quotient.sound ((D.sameBlob y x).mpr (Quotient.exact he))
  unfold protectedBlobs at hx ⊢
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨e,he,hex⟩ := Finset.mem_image.mp hx
      obtain ⟨f,hf,hraw⟩ := hp.1 e he
      have ht := (D.endpoints f).2
      rw [hraw] at ht
      have hfx := hblob (T.source.network.graph.source f) ((congrArg O.source.network.graph.blobOf ht.symm).trans hex)
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f,hf,hfx⟩))
    · obtain ⟨e,he,hex⟩ := Finset.mem_image.mp hx
      obtain ⟨f,hf,hraw⟩ := hp.1 e he
      have ht := (D.endpoints f).1
      rw [hraw] at ht
      have hfx := hblob (T.source.network.graph.target f) ((congrArg O.source.network.graph.blobOf ht.symm).trans hex)
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f,hf,hfx⟩))
  · obtain ⟨h,hh,hhx⟩ := Finset.mem_image.mp hx
    obtain ⟨k,hk,hkv⟩ := hp.2 h hh
    have hkx := hblob k.val ((congrArg O.source.network.graph.blobOf hkv).trans hhx)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,hk,hkx⟩)

lemma equal_parent_exposure_order_invariant (N : RootedBinary V E X)
    (P Q : GProgram.G2.OriginalHybridParents N) (hs : P.hybrid = Q.hybrid) (f : E → ℝ) :
    f P.parent0 = f P.parent1 ↔ f Q.parent0 = f Q.parent1 := by
  have aux : ∀ (P Q : GProgram.G2.OriginalHybridParents N), P.hybrid = Q.hybrid →
      f P.parent0 = f P.parent1 → f Q.parent0 = f Q.parent1 := by
    intro P Q hs he
    have hh : ∀ e, N.graph.target e = P.hybrid → f e = f P.parent0 := by
      intro e ht
      obtain ⟨bit,hbit⟩ := GProgram.G5.ParentCalendar.incoming_edge_is_original_parent P ht
      rw [← hbit]
      cases bit
      · rfl
      · exact he.symm
    exact (hh Q.parent0 (Q.target0.trans hs.symm)).trans
      (hh Q.parent1 (Q.target1.trans hs.symm)).symm
  exact ⟨aux P Q hs,aux Q P hs.symm⟩

lemma original_extracted_hybrid (O T : Source.{u,v,w} Y)
    (H : OriginalParentRegistry O.network) (D : Decoration O T) (hD : Originated O H D)
    (b : T.network.graph.Blob) (hb : b ≠ T.network.graph.blobOf T.network.root)
    (A : ActualBlobBigon T.network b)
    (B : ActualBlobBigon O.network (O.network.graph.blobOf (D.vertex A.fragment.upper))) :
    B.fragment.parents.hybrid = D.vertex A.fragment.parents.hybrid := by
  rcases (lifted_blob_vertices O T H D hD b A B.fragment.parents.hybrid).mp B.hybrid_in_blob with h | h
  · have hd := B.fragment.parents.isHybrid.1
    rw [h,← D.indegree A.fragment.upper,
      (G1BigonFootprint.actual_upper_tree_degrees T.network T.cutChild b A).1] at hd
    omega
  · exact h

/-- Equal-arm reduction in the ORIGINAL physical source excludes equality at
any later generated private cell. Eligibility and parent order are derived. -/
lemma generated_cell_unequal (O : PhysicalMarkedSource.{u,v,w} Y)
    (T : MarkedSource.{u,v,w} Y) (D : Decoration O.marked.source T.source)
    (hD : Originated O.marked.source O.registry D)
    (hmarks : ProtectedProvenance O.marked T D) (hred : EqualArmReduced O)
    (b : T.source.network.graph.Blob)
    (hb : b ≠ T.source.network.graph.blobOf T.source.network.root)
    (A : ActualBlobBigon T.source.network b)
    (hu : b ∉ protectedBlobs T.source.network T.marks) :
    GProgram.G7.OriginalSurvivalCoverage.exposure O.marked.source.network O.marked.source.calendar O.rates
        (O.registry.parents (originalHybridSite O.marked.source T.source D b A)).parent0 ≠
      GProgram.G7.OriginalSurvivalCoverage.exposure O.marked.source.network O.marked.source.calendar O.rates
        (O.registry.parents (originalHybridSite O.marked.source T.source D b A)).parent1 := by
  let b0 := O.marked.source.network.graph.blobOf (D.vertex A.fragment.upper)
  have hb0 := lifted_blob_nonroot O.marked.source T.source D b hb A
  have hp0 := lifted_blob_two_ports O.marked.source T.source O.registry D hD b hb A
  have hu0 : b0 ∉ protectedBlobs O.marked.source.network O.marked.marks := by
    intro hm
    have ht := protected_blob_pulls_back O.marked T D hmarks A.fragment.upper hm
    rw [A.upper_in_blob] at ht
    exact hu ht
  intro he
  apply hred b0 hb0 hp0 hu0
  let B := extractedBigon O.marked.source.network O.marked.source.cutChild b0 hb0
    ((actual_quotient_port_card O.marked.source.network b0).symm.trans hp0)
  have hsite : B.fragment.parents.hybrid =
      (O.registry.parents (originalHybridSite O.marked.source T.source D b A)).hybrid := by
    rw [O.registry.original_site]
    exact original_extracted_hybrid O.marked.source T.source O.registry D hD b hb A B
  exact (equal_parent_exposure_order_invariant O.marked.source.network
    B.fragment.parents (O.registry.parents (originalHybridSite O.marked.source T.source D b A)) hsite
    (GProgram.G7.OriginalSurvivalCoverage.exposure O.marked.source.network O.marked.source.calendar O.rates)).mpr he

end OriginalBlobRetention

section UnequalGeneratedWords
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1DecoratedSpliceConstruction G1LiftedOriginalBigon
open G1OriginatedSpanRegistryAdmission G1ActualTwoPortBlob
open GProgram.G7.OriginalSurvivalCoverage
universe u v w
variable {Y : Type w} [Fintype Y]

def UnequalSite (O : PhysicalMarkedSource.{u,v,w} Y) (h : Hybrid O.marked.source.network) : Prop :=
  exposure O.marked.source.network O.marked.source.calendar O.rates (O.registry.parents h).parent0 ≠
    exposure O.marked.source.network O.marked.source.calendar O.rates (O.registry.parents h).parent1

def SitesSatisfy (O : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    {a b : O.Vertex} (word : OriginalSpan O.network a b) : Prop := ∀ h ∈ spanSites O word, P h

def RecipeSitesSatisfy (O : Source.{u,v,w} Y) (P : Hybrid O.network → Prop) : Recipe O → Prop
  | .raw _ => True
  | .span _ _ word => SitesSatisfy O P word

lemma sitesSatisfy_append (O : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    {a b c : O.Vertex} (first : OriginalSpan O.network a b) (last : OriginalSpan O.network b c) :
    SitesSatisfy O P (.append first last) ↔ SitesSatisfy O P first ∧ SitesSatisfy O P last := by
  simp only [SitesSatisfy,spanSites,List.mem_append,or_imp,forall_and]

lemma sitesSatisfy_mpr_left (O : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    {a a' b : O.Vertex} (h : a = a') (word : OriginalSpan O.network a' b) :
    SitesSatisfy O P ((congrArg (fun v => OriginalSpan O.network v b) h).mpr word) ↔
      SitesSatisfy O P word := by subst a'; rfl

lemma sitesSatisfy_mpr_right (O : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    {a b b' : O.Vertex} (h : b = b') (word : OriginalSpan O.network a b') :
    SitesSatisfy O P ((congrArg (OriginalSpan O.network a) h).mpr word) ↔
      SitesSatisfy O P word := by subst b'; rfl

lemma sitesSatisfy_cast_left (O : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    {a a' b : O.Vertex} (h : a = a') (word : OriginalSpan O.network a b) :
    SitesSatisfy O P (cast (congrArg (fun v => OriginalSpan O.network v b) h) word) ↔
      SitesSatisfy O P word := by subst a'; rfl

lemma physicalRecipe_sites (O : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    {a b : O.Vertex} (label : Recipe O) (ep : label.input = a ∧ label.output = b)
    (hb : ∀ f, label = .raw f → O.network.graph.IsBridge f)
    (hr : RecipeSitesSatisfy O P label) : SitesSatisfy O P (physicalRecipeSpan O label ep hb) := by
  cases label with
  | raw f =>
    simp only [Recipe.input,Recipe.output] at ep
    obtain ⟨rfl,rfl⟩ := ep
    simp [physicalRecipeSpan,SitesSatisfy,spanSites]
  | span c d word =>
    simp only [Recipe.input,Recipe.output] at ep
    obtain ⟨rfl,rfl⟩ := ep
    simpa [physicalRecipeSpan,RecipeSitesSatisfy] using hr

lemma bridgeSpan_sites (O T : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    (D : Decoration O T) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (hr : RecipeSitesSatisfy O P (D.recipe e)) : SitesSatisfy O P (bridgeSpan O T D e he) :=
  physicalRecipe_sites O P (D.recipe e) (D.endpoints e) (fun f hf => (D.raw_bridge e f hf).mp he) hr

lemma newOriginalSpan_sites (O T : Source.{u,v,w} Y) (P : Hybrid O.network → Prop)
    (D : Decoration O T) (H : OriginalParentRegistry O.network)
    (b : T.network.graph.Blob) (A : ActualBlobBigon T.network b)
    (hr : ∀ e, RecipeSitesSatisfy O P (D.recipe e))
    (hs : P (originalHybridSite O T D b A)) : SitesSatisfy O P (newOriginalSpan O T D H b A) := by
  have hchild := bridgeSpan_sites O T P D A.child A.child_bridge (hr A.child)
  have hentry := bridgeSpan_sites O T P D A.entry A.entry_bridge (hr A.entry)
  have hbigon : SitesSatisfy O P (.bigon (liftedOriginalFragment O T D H b A)) := by
    intro h hh
    have he : h = ⟨(liftedOriginalFragment O T D H b A).parents.hybrid,
        (liftedOriginalFragment O T D H b A).parents.isHybrid⟩ := List.mem_singleton.mp hh
    have he' : h = originalHybridSite O T D b A := by
      apply Subtype.ext
      exact (congrArg Subtype.val he).trans (H.original_site _)
    exact he'.symm ▸ hs
  unfold newOriginalSpan
  rw [sitesSatisfy_append,sitesSatisfy_append]
  refine ⟨(sitesSatisfy_mpr_right O P (congrArg D.vertex A.child_source).symm _).mpr hchild,?_,
    (sitesSatisfy_mpr_left O P (congrArg D.vertex A.entry_target).symm _).mpr hentry⟩
  have hsite : (liftedOriginalFragment O T D H b A).parents.hybrid = D.vertex A.fragment.parents.hybrid :=
    H.original_site _
  exact (sitesSatisfy_cast_left O P hsite _).mpr hbigon

/-- Marked structural normalization of an equal-arm-reduced physical source
creates words consisting only of unequal original sites. -/
theorem markedSteps_unequal_decoration (O : PhysicalMarkedSource.{u,v,w} Y)
    (T : MarkedSource.{u,v,w} Y) (hred : EqualArmReduced O) (steps : MarkedSteps O.marked T) :
    ∃ D : Decoration O.marked.source T.source,
      Originated O.marked.source O.registry D ∧ ProtectedProvenance O.marked T D ∧
      ∀ e, RecipeSitesSatisfy O.marked.source (UnequalSite O) (D.recipe e) := by
  induction steps with
  | refl => exact ⟨initialDecoration O.marked.source,Originated.initial,
      protectedProvenance_initial O.marked,fun _ => trivial⟩
  | @tail S U prior step ih =>
    obtain ⟨D,hD,hmarks,hr⟩ := ih
    cases step with
    | splice b hb hp hu =>
      let A := extractedBigon S.source.network S.source.cutChild b hb
        ((actual_quotient_port_card S.source.network b).symm.trans hp)
      refine ⟨normalizedSpliceDecoration O.marked.source S.source D O.registry b hb hp,
        Originated.splice D hD b hb hp,
        protectedProvenance_splice O.marked S O.registry D hmarks b hb hp hu,?_⟩
      intro e
      cases e with
      | inl e => exact hr e.val
      | inr z =>
        exact newOriginalSpan_sites O.marked.source S.source (UnequalSite O)
          D O.registry b A hr (generated_cell_unequal O S D hD hmarks hred b hb A hu)

end UnequalGeneratedWords

section DirectedWordWitnesses
open G1ActualCutDescendants GProgram.G5.AttainedChronology
open UnifiedLean.Source.NativeCommonPairGerm
open DotG4.PairedNaturalTreeCertificate DotG4.ActualSelectedPathExposure

lemma actual_bridge_inside_outside (N : RootedBinary V E X) (e : E) (he : N.graph.IsBridge e) :
    ∃ i j : X, N.graph.DReach (N.graph.target e) (N.leaf i) ∧
      ¬ N.graph.DReach (N.graph.target e) (N.leaf j) := by
  obtain ⟨i,hi⟩ := N.every_vertex_reaches_leaf (N.graph.target e)
  obtain ⟨j,hj⟩ := N.exists_leaf_avoiding_of_ne_root (N.edge_target_ne_root e)
  refine ⟨i,j,hi,?_⟩
  intro hd
  have hs := (N.root_on_source_side e).trans (N.graph.avoid_target_reach_without e hj)
  have ht := (actual_bridge_target_side_descendant N e he (N.leaf j)).mpr hd
  exact N.graph.bridge_sides_disjoint he hs ht

lemma actual_hybrid_descendant_parent_visit (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (coin : CommonSeed N)
    (h : Hybrid N) (i : X) (hi : N.graph.DReach h.val (N.leaf i)) :
    (H.parents h).parent (coin h) ∈ (commonRoutes N C H coin).edges i := by
  let child := hybridChild N h.val h.property
  have hcs := hybridChild_source N h.val h.property
  have hcb : N.graph.IsBridge child := hc child (hcs.symm ▸ h.property)
  have hdesc : N.graph.DReach (N.graph.target child) (N.leaf i) := by
    rcases Relation.ReflTransGen.cases_head hi with he | ⟨v,⟨e,hs,ht⟩,hrest⟩
    · exact False.elim (N.no_edge_source_leaf i child (hcs.trans he))
    · have he : e = child := (Classical.choose_spec (hybrid_child_exists_unique N h.val h.property)).2 e hs
      exact (he ▸ ht).symm ▸ hrest
  have hm := bridge_mem_every_descendant_route N hcb
    ((commonRoutes N C H coin).valid i) hdesc
  obtain ⟨pre,post,hs,hpre,hpost⟩ := GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge
    ((commonRoutes N C H coin).valid i) hm
  have hp : (commonSwitching N H coin).graph.DReach (N.graph.target child) (N.leaf i) := by
    apply kept_original_path_selected_reach N _ hpost
    intro e he
    apply common_route_kept N C H coin i
    rw [hs]
    exact List.mem_append_right _ (List.mem_cons_of_mem child he)
  have hkchild := common_route_kept N C H coin i hm
  have hfull : (commonSwitching N H coin).graph.DReach h.val (N.leaf i) :=
    (Relation.ReflTransGen.single ⟨⟨child,hkchild⟩,hcs,rfl⟩).trans hp
  have hk : (commonSwitching N H coin).keep ((H.parents h).parent (coin h)) :=
    (common_keep_at_original_hybrid N H coin h _ (registry_parent_target N H h _)).mpr rfl
  apply (common_route_edge_iff_selected_descendant N C H coin i ⟨_,hk⟩).mpr
  rw [registry_parent_target]
  exact hfull

lemma route_avoids_nondescendant (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) (h : Hybrid N)
    (j : X) (hj : ¬ N.graph.DReach h.val (N.leaf j)) :
    ∀ e ∈ (commonRoutes N C H coin).edges j, N.graph.target e ≠ h.val := by
  intro e he ht
  obtain ⟨pre,post,hs,hpre,hpost⟩ := GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge
    ((commonRoutes N C H coin).valid j) he
  apply hj
  rw [← ht]
  exact hpost.directed

end DirectedWordWitnesses

section ProperWordCut
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalActorOperationOwnership G1OriginatedTaxonReachTransport
open G1OriginatedNeutralSpanRegion G1OriginalSpanRegion
universe u v w
variable {Y : Type w} [Fintype Y]

/-- One original ordered taxon pair exposes every private site of this actual
bridge word, in every bank. The pair is derived from the retained-root cut. -/
theorem actual_word_has_directed_pair (O T : Source.{u,v,w} Y)
    (H : OriginalParentRegistry O.network) (D : Decoration O T) (hD : Originated O H D)
    (e : BridgeActor T) :
    ∃ i j : Y, i ≠ j ∧ ∀ h ∈ spanSites O (bridgeSpan O T D e.val e.property),
      O.network.graph.DReach h.val (O.network.leaf i) ∧
        ¬ O.network.graph.DReach h.val (O.network.leaf j) := by
  obtain ⟨i,j,hi,hj⟩ := actual_bridge_inside_outside T.network e.val e.property
  have hi' := (actual_originated_taxon_reach O H D hD _ i).mp hi
  have hj' : ¬ O.network.graph.DReach (D.vertex (T.network.graph.target e.val)) (O.network.leaf j) :=
    fun h => hj ((actual_originated_taxon_reach O H D hD _ j).mpr h)
  have hn := actual_originated_bridge_region_neutral O H D hD e.val e.property
  refine ⟨i,j,?_,?_⟩
  · intro he
    exact hj (he ▸ hi)
  · intro h hh
    have hm := (hybrid_mem_nodeRegion_iff O _ h).mpr hh
    exact ⟨(hn h.val hm i).mpr hi',fun hd => hj' ((hn h.val hm j).mp hd)⟩

end ProperWordCut

section ParallelBitVariation
open G1ActualCutDescendants GProgram.G5.AttainedChronology GProgram.G5.NonbridgeRoutes
open UnifiedLean.Source.NativeCommonPairGerm UnifiedLean.Source.NativePairClockLaw
open DotG4.PairedNaturalTreeCertificate DotG4.ActualSelectedPathExposure
open GProgram.G7.OriginalSurvivalCoverage

lemma compiledRoute_above_changed_site (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a b : CommonSeed N) (h : Hybrid N)
    (hab : ∀ k, k ≠ h → a k = b k) (u : V) (hu : C.age h.val < C.age u) :
    compiledRoute N C (coinSelector N H a) u = compiledRoute N C (coinSelector N H b) u := by
  have ha := compiledRoute_source_spec N C (coinSelector N H a) u
  have hb := compiledRoute_source_spec N C (coinSelector N H b) u
  apply List.reverse_inj.mp
  apply upPath_avoiding_agreement N _ _ h.val (coin_selectors_agree_except N H a b h hab)
    (EdgePath.to_upPath_reverse ha.1 (fun _ _ => trivial))
    (EdgePath.to_upPath_reverse hb.1 (fun _ _ => trivial))
    (respectsSelector_reverse N _ ha.2) (respectsSelector_reverse N _ hb.2)
  intro e he ht
  obtain ⟨pre,post,hs,hpre,hpost⟩ := GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge
    ha.1 (List.mem_reverse.mp he)
  have hc := actual_calendar_directed_age N C hpost.directed
  rw [ht] at hc
  exact not_lt_of_ge hc hu

lemma parallel_bit_route_change (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (a b : CommonSeed N)
    (h : Hybrid N) (hab : ∀ k, k ≠ h → a k = b k)
    (u : V) (hpar : ∀ bit, N.graph.source ((H.parents h).parent bit) = u)
    (i : X) (hi : N.graph.DReach h.val (N.leaf i)) :
    ∃ pre post,
      (commonRoutes N C H a).edges i = pre ++ [(H.parents h).parent (a h)] ++ post ∧
      (commonRoutes N C H b).edges i = pre ++ [(H.parents h).parent (b h)] ++ post := by
  have hvis := actual_hybrid_descendant_parent_visit N hc C H a h i hi
  obtain ⟨pa,pb,post,ha,hb,hpa,hpb,hpost,hselpost⟩ :=
    route_through_changed_site N C H a b h hab i
      ⟨_,hvis,registry_parent_target N H h _⟩
  have hu : C.age h.val < C.age u := by
    have hh := C.edge_older ((H.parents h).parent false)
    rw [registry_parent_target,hpar] at hh
    exact hh
  let pre := compiledRoute N C (coinSelector N H a) u
  have preeq := compiledRoute_above_changed_site N C H a b h hab u hu
  have hpref : ∀ coin : CommonSeed N, ∀ xs : List E,
      EdgePath N.graph N.root h.val xs → RespectsSelector N (coinSelector N H coin) xs →
      xs = compiledRoute N C (coinSelector N H coin) u ++ [(H.parents h).parent (coin h)] := by
    intro coin xs hxs hsxs
    have hr := compiledRoute_source_spec N C (coinSelector N H coin) u
    have hp : EdgePath N.graph u h.val [(H.parents h).parent (coin h)] := by
      have ht := registry_parent_target N H h (coin h)
      exact .cons (hpar _) (ht.symm ▸ EdgePath.nil h.val)
    have hk : RespectsSelector N (coinSelector N H coin) [(H.parents h).parent (coin h)] := by
      intro e he
      have he := List.mem_singleton.mp he
      subst e
      apply common_kept_edge_respects N H coin
      exact (common_keep_at_original_hybrid N H coin h _ (registry_parent_target N H h _)).mpr rfl
    exact selected_path_unique N _ hxs (hr.1.append hp) hsxs (respects_append N _ hr.2 hk)
  have hsa := (compiledRoute_source_spec N C (coinSelector N H a) (N.leaf i)).2
  have hsb := (compiledRoute_source_spec N C (coinSelector N H b) (N.leaf i)).2
  have hpa' := hpref a pa hpa (respects_sublist N _ hsa (by
    intro e he
    change e ∈ (commonRoutes N C H a).edges i
    rw [ha]
    exact List.mem_append_left _ he))
  have hpb' := hpref b pb hpb (respects_sublist N _ hsb (by
    intro e he
    change e ∈ (commonRoutes N C H b).edges i
    rw [hb]
    exact List.mem_append_left _ he))
  refine ⟨pre,post,?_,?_⟩
  · simpa only [hpa',List.append_assoc] using ha
  · simpa only [hpb',← preeq,List.append_assoc] using hb

lemma selectedDirectedExposure_list (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (coin : CommonSeed N) (i j : X) :
    selectedDirectedExposure N C H r coin i j =
      ((commonRoutes N C H coin).edges i |>.map
        (fun e => if e ∉ (commonRoutes N C H coin).edges j then exposure N C r e else 0)).sum := by
  let es := (commonRoutes N C H coin).edges i
  let f := fun e => if e ∉ (commonRoutes N C H coin).edges j then exposure N C r e else 0
  have hfilter : Finset.univ.filter (fun e => e ∈ es) = es.toFinset := by ext e; simp
  change (∑ e : E, if e ∈ es ∧ e ∉ (commonRoutes N C H coin).edges j then exposure N C r e else 0) = _
  simp_rw [ite_and]
  rw [← Finset.sum_filter,hfilter]
  exact List.sum_toFinset f (edgePath_nodup N C ((commonRoutes N C H coin).valid i))

/-- The actual directed path changes only by the two original parallel edge
exposures. No fitted word hazard or independent-genealogy assumption is used. -/
theorem parallel_bit_directed_exposure_change (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (a b : CommonSeed N) (h : Hybrid N) (hab : ∀ k, k ≠ h → a k = b k)
    (u : V) (hpar : ∀ bit, N.graph.source ((H.parents h).parent bit) = u)
    (i j : X) (hi : N.graph.DReach h.val (N.leaf i)) (hj : ¬ N.graph.DReach h.val (N.leaf j)) :
    selectedDirectedExposure N C H r b i j - selectedDirectedExposure N C H r a i j =
      exposure N C r ((H.parents h).parent (b h)) - exposure N C r ((H.parents h).parent (a h)) := by
  obtain ⟨pre,post,ha,hb⟩ := parallel_bit_route_change N hc C H a b h hab u hpar i hi
  have hjroute := route_avoiding_changed_site N C H a b h hab j (route_avoids_nondescendant N C H a h j hj)
  have hpa : (H.parents h).parent (a h) ∉ (commonRoutes N C H a).edges j := by
    intro hm
    exact route_avoids_nondescendant N C H a h j hj _ hm (registry_parent_target N H h _)
  have hpb : (H.parents h).parent (b h) ∉ (commonRoutes N C H a).edges j := by
    intro hm
    exact route_avoids_nondescendant N C H a h j hj _ hm (registry_parent_target N H h _)
  rw [selectedDirectedExposure_list,selectedDirectedExposure_list,← hjroute,ha,hb]
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    if_pos hpa,if_pos hpb,add_zero]
  ring

end ParallelBitVariation

section FiniteFlipChain
variable {I : Type*} [DecidableEq I]

noncomputable def flipChain (high : I → Bool) : List I → (I → Bool) → List (I → Bool)
  | [], base => [base]
  | h :: rest, base => base :: flipChain high rest (Function.update base h (high h))

lemma flipChain_length (high : I → Bool) (sites : List I) (base : I → Bool) :
    (flipChain high sites base).length = sites.length + 1 := by
  induction sites generalizing base with
  | nil => rfl
  | cons h rest ih => simp only [flipChain,List.length_cons,ih]

lemma flipChain_increasing (low high : I → Bool) (F : (I → Bool) → ℝ)
    (sites : List I) (hn : sites.Nodup)
    (hstep : ∀ h ∈ sites, ∀ coin, coin h = low h → F coin < F (Function.update coin h (high h)))
    (base : I → Bool) (hbase : ∀ h ∈ sites, base h = low h) :
    (flipChain high sites base).Pairwise (fun a b => F a < F b) ∧
      ∀ coin ∈ flipChain high sites base, F base ≤ F coin := by
  induction sites generalizing base with
  | nil => simp [flipChain]
  | cons h rest ih =>
    obtain ⟨hnot,hn⟩ := List.nodup_cons.mp hn
    have hbase' : ∀ k ∈ rest, Function.update base h (high h) k = low k := by
      intro k hk
      rw [Function.update_of_ne (show k ≠ h from fun he => hnot (he ▸ hk))]
      exact hbase k (List.mem_cons_of_mem h hk)
    have hi := ih hn (fun k hk => hstep k (List.mem_cons_of_mem h hk)) _ hbase'
    have hs := hstep h List.mem_cons_self base (hbase h List.mem_cons_self)
    constructor
    · apply List.pairwise_cons.mpr
      exact ⟨fun coin hc => hs.trans_le (hi.2 coin hc),hi.1⟩
    · intro coin hc
      rcases List.mem_cons.mp hc with he | he
      · exact he ▸ le_rfl
      · exact (hs.trans_le (hi.2 coin he)).le

lemma flipChain_exponential_card (low high : I → Bool) (F : (I → Bool) → ℝ)
    (sites : List I) (hn : sites.Nodup)
    (hstep : ∀ h ∈ sites, ∀ coin, coin h = low h → F coin < F (Function.update coin h (high h)))
    (A : Finset ℝ) (hA : ∀ coin, Real.exp (-F coin) ∈ A) : sites.length + 1 ≤ A.card := by
  let chain := flipChain high sites low
  have hi := (flipChain_increasing low high F sites hn hstep low (fun _ _ => rfl)).1
  have hn' : (chain.map (fun coin => Real.exp (-F coin))).Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    apply List.pairwise_map.mpr
    apply hi.imp
    intro a b hab he
    exact (ne_of_lt hab) (neg_injective (Real.exp_injective he))
  have hsub : (chain.map (fun coin => Real.exp (-F coin))).toFinset ⊆ A := by
    intro x hx
    obtain ⟨coin,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hA coin
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn',List.length_map,flipChain_length] at hcard
  exact hcard

end FiniteFlipChain

section WordSupport
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalActorOperationOwnership G1OriginalSpanCalendarDecomposition
open G1OriginatedSpanRegistryAdmission
open GProgram.G7.OriginalSurvivalCoverage
open UnifiedLean.Source.OriginalFixedIDControls UnifiedLean.Source.NativeCommonPairGerm
open DotG4.ActualSelectedPathExposure DotG4.PairedNaturalTreeCertificate
open DotG4.WeightedOrdinaryTreeLaw DotG4.ActualObservableBankCertificate
universe u v w
variable {Y : Type w} [Fintype Y]

lemma registered_span_site_parallel (O : Source.{u,v,w} Y) (H : OriginalParentRegistry O.network)
    {a b : O.Vertex} (word : OriginalSpan O.network a b) (hr : RegistrySpan O.network H word)
    (h : Hybrid O.network) (hh : h ∈ spanSites O word) :
    ∃ upper : O.Vertex, ∀ bit, O.network.graph.source ((H.parents h).parent bit) = upper := by
  induction word with
  | edge e hd => simp only [spanSites,List.not_mem_nil] at hh
  | bigon B =>
    have he := List.mem_singleton.mp hh
    subst h
    refine ⟨B.upper,?_⟩
    intro bit
    change B.parents = H.parents ⟨B.parents.hybrid,B.parents.isHybrid⟩ at hr
    rw [← hr]
    exact B.arm_sources bit
  | append first last ihfirst ihlast =>
    rcases List.mem_append.mp hh with hh | hh
    · exact ihfirst hr.1 hh
    · exact ihlast hr.2 hh

def ProtectedMask (O : MarkedSource.{u,v,w} Y) (mask : OriginalMask O.source.network) : Prop :=
  ∀ h, h ∉ O.marks.hybrids → mask h = none

lemma actor_site_unforced (O T : MarkedSource.{u,v,w} Y)
    (H : OriginalParentRegistry O.source.network) (D : Decoration O.source T.source)
    (hD : Originated O.source H D) (hp : ProtectedProvenance O T D)
    (e : BridgeActor T.source) (mask : OriginalMask O.source.network) (hm : ProtectedMask O mask)
    (h : Hybrid O.source.network) (hh : h ∈ spanSites O.source (bridgeSpan O.source T.source D e.val e.property)) :
    mask h = none := by
  apply hm
  intro hhmark
  obtain ⟨k,hk,hv⟩ := hp.2 h hhmark
  apply actor_hybrid_not_retained O.source T.source H D hD e h
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hybrid_mem_nodeRegion_iff O.source _ h).mpr hh⟩)
  exact ⟨k.val,hv⟩

noncomputable def lowerArm (O : PhysicalMarkedSource.{u,v,w} Y) (h : Hybrid O.marked.source.network) : Bool :=
  if exposure O.marked.source.network O.marked.source.calendar O.rates (O.registry.parents h).parent0 <
      exposure O.marked.source.network O.marked.source.calendar O.rates (O.registry.parents h).parent1 then false else true

lemma lowerArm_strict (O : PhysicalMarkedSource.{u,v,w} Y) (h : Hybrid O.marked.source.network)
    (hh : UnequalSite O h) :
    exposure O.marked.source.network O.marked.source.calendar O.rates ((O.registry.parents h).parent (lowerArm O h)) <
      exposure O.marked.source.network O.marked.source.calendar O.rates ((O.registry.parents h).parent (!(lowerArm O h))) := by
  unfold lowerArm
  split_ifs with he
  · exact he
  · exact lt_of_le_of_ne (le_of_not_gt he) (Ne.symm hh)

/-- Actual support has at least one more atom than the number of unequal
private sites in an originated bridge word. The same fixed row is used. -/
theorem actual_word_directed_support_lower_bound (O : PhysicalMarkedSource.{u,v,w} Y)
    (T : MarkedSource.{u,v,w} Y) (D : Decoration O.marked.source T.source)
    (hD : Originated O.marked.source O.registry D) (hp : ProtectedProvenance O.marked T D)
    (e : BridgeActor T.source)
    (hu : SitesSatisfy O.marked.source (UnequalSite O) (bridgeSpan O.marked.source T.source D e.val e.property))
    (mask : OriginalMask O.marked.source.network) (hm : ProtectedMask O.marked mask) :
    ∃ i j : Y, i ≠ j ∧ ∀ A : Finset ℝ,
      (∀ coin : CommonSeed O.marked.source.network,
        realSurvival O.marked.source.network O.marked.source.calendar O.registry O.probabilities O.rates i j
          (overrideBank O.marked.source.network mask coin) ∈ A) →
      (actorHybrids O.marked.source T.source D e).card + 1 ≤ A.card := by
  obtain ⟨i,j,hij,hpair⟩ := actual_word_has_directed_pair O.marked.source T.source O.registry D hD e
  refine ⟨i,j,hij,?_⟩
  intro A hA
  let word := bridgeSpan O.marked.source T.source D e.val e.property
  let F := fun coin : CommonSeed O.marked.source.network =>
    selectedDirectedExposure O.marked.source.network O.marked.source.calendar O.registry O.rates
      (overrideBank O.marked.source.network mask coin) i j
  have hstep : ∀ h ∈ spanSites O.marked.source word, ∀ coin, coin h = lowerArm O h →
      F coin < F (Function.update coin h (!(lowerArm O h))) := by
    intro h hh coin hlo
    have hmask := actor_site_unforced O.marked T O.registry D hD hp e mask hm h hh
    obtain ⟨upper,hpar⟩ := registered_span_site_parallel O.marked.source O.registry word
      (actual_originated_bridge_word_registered O.marked.source O.registry D hD e.val e.property) h hh
    have hab : ∀ k, k ≠ h →
        overrideBank O.marked.source.network mask coin k =
          overrideBank O.marked.source.network mask (Function.update coin h (!(lowerArm O h))) k := by
      intro k hk
      simp only [overrideBank,Function.update_of_ne hk]
    have he := parallel_bit_directed_exposure_change O.marked.source.network O.marked.source.cutChild
      O.marked.source.calendar O.registry O.rates _ _ h hab upper hpar i j (hpair h hh).1 (hpair h hh).2
    have hstrict := lowerArm_strict O h (hu h hh)
    simp only [overrideBank,hmask,Option.getD_none,Function.update_self,hlo] at he
    change F (Function.update coin h (!(lowerArm O h))) - F coin = _ at he
    linarith
  rw [actorHybrids_card_sites]
  apply flipChain_exponential_card (lowerArm O) (fun h => !(lowerArm O h)) F
    (spanSites O.marked.source word) (spanSites_nodup O.marked.source word) hstep A
  intro coin
  simpa only [realSurvival_eq_selected_path] using hA coin

end WordSupport

section ExposingRowGrids
open UnifiedLean.Source.NativePairClockLaw
open DotG4.WholeProfileDetermination DotG4.ActualSparseCertificateExistence
open DotG4.ActualObservableBankCertificate DotG4.WeightedOrdinaryTreeLaw
open UnifiedLean.Source.NativeCommonPairGerm UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls UnifiedLean.Source.NativeIndependentPairMixture

/-- Zero configuration weights are discarded only inside the proof. The
certificate still tests the supplied mixed row itself. -/
lemma finiteBank_uniform_grid_supported {I : Type*} [Fintype I]
    (p : PMF I) (x : I → ℝ) (hx : ∀ a, 0 < x a ∧ x a ≤ 1) :
    ∃ L : Nat, ∃ grid : Finset ℝ, 0 < L ∧
      ∀ (J : Type*) [Fintype J] (q : PMF J) (y : J → ℝ),
        (∀ a, 0 < y a ∧ y a ≤ 1) →
        (∀ k ∈ momentLevels L, finiteBankMoment q y k = finiteBankMoment p x k) →
        ∀ a, q a ≠ 0 → y a ∈ grid := by
  obtain ⟨L,grid,hL,_,hgrid⟩ := finiteBank_exists_uniform_grid p x hx
  refine ⟨L,grid,hL,?_⟩
  intro J _ q y hy hm a ha
  apply hgrid {a : J // q a ≠ 0} (positiveSupportPMF q)
    (positiveSupportPMF_positive q) (fun a => y a.val) (fun a => hy a.val) ?_ ⟨a,ha⟩
  intro k hk
  change (∑ a : {a : J // q a ≠ 0}, (positiveSupportPMF q a).toReal *
    y a.val ^ k.choose 2) = _
  rw [positiveSupportPMF_sum q (fun a => y a ^ k.choose 2)]
  exact hm k hk

/-- Enumeration does not change the literal finite-bank moment. -/
lemma finiteBankMoment_enumeration {ι : Type*} (I J : Fintype ι)
    (p : PMF ι) (x : ι → ℝ) (k : Nat) :
    @finiteBankMoment ι I p x k = @finiteBankMoment ι J p x k := by
  cases Subsingleton.elim I J
  rfl

/-- One target-only finite comb certificate controls every supported original
bank of every finite rival supplied row. It never observes a deterministic
configuration separately. -/
theorem actual_exposing_row_uniform_grids [DecidableEq X]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    {Config : Type*} [Fintype Config] (ν : PMF Config) (masks : Config → OriginalMask N) :
    ∃ L : X × X → Nat, ∃ grid : X × X → Finset ℝ, (∀ ij, 0 < L ij) ∧
      ∀ (V' E' Config' : Type*) [Fintype V'] [Fintype E'] [Fintype Config']
        [DecidableEq V'] [DecidableEq E']
        (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
        (p' : HybridProbabilities N') (r' : PositivePairRates E')
        (ν' : PMF Config') (masks' : Config' → OriginalMask N'),
        (∀ i j k, k ∈ momentLevels (L (i,j)) →
          randomizedLegalCombMoment N' C' H' p' r' ν' masks' i j k =
            randomizedLegalCombMoment N C H p r ν masks i j k) →
        ∀ cfg, ν' cfg ≠ 0 → ∀ coin i j,
          realSurvival N' C' H' p' r' i j (overrideBank N' (masks' cfg) coin) ∈ grid (i,j) := by
  classical
  have hg (ij : X × X) := finiteBank_uniform_grid_supported
    (configurationBankPMF ν (originalRegisterMeasure N p).toPMF)
    (fun z => directedSurvival (maskedNormalizedTree N C H r (masks z.1) z.2) ij.1 ij.2)
    (fun z => directedSurvival_bounds _ _ _)
  choose L grid hL hg using hg
  refine ⟨L,grid,hL,?_⟩
  intro V' E' Config' _ _ _ _ _ N' C' H' p' r' ν' masks' hm cfg hcfg coin i j
  have hb : (originalRegisterMeasure N' p').toPMF coin ≠ 0 := by
    intro hz
    have hp := original_bank_real_weight_positive N' p' coin
    simp only [hz,ENNReal.toReal_zero] at hp
    exact lt_irrefl _ hp
  have hz : configurationBankPMF ν' (originalRegisterMeasure N' p').toPMF (cfg,coin) ≠ 0 := by
    rw [configurationBankPMF_apply]
    exact mul_ne_zero hcfg hb
  have hmem := hg (i,j) (Config' × CommonSeed N')
    (configurationBankPMF ν' (originalRegisterMeasure N' p').toPMF)
    (fun z => directedSurvival (maskedNormalizedTree N' C' H' r' (masks' z.1) z.2) i j)
    (fun z => directedSurvival_bounds _ _ _)
    (by
      intro k hk
      have hr : randomizedLegalCombMoment N' C' H' p' r' ν' masks' i j k =
          finiteBankMoment (configurationBankPMF ν' (originalRegisterMeasure N' p').toPMF)
            (fun z => directedSurvival (maskedNormalizedTree N' C' H' r' (masks' z.1) z.2) i j) k :=
        (actual_randomized_legal_moment N' C' H' p' r' ν' masks' i j k
          (momentLevels_positive _ k hk)).trans (finiteBankMoment_enumeration _ _ _ _ _)
      have ht : randomizedLegalCombMoment N C H p r ν masks i j k =
          finiteBankMoment (configurationBankPMF ν (originalRegisterMeasure N p).toPMF)
            (fun z => directedSurvival (maskedNormalizedTree N C H r (masks z.1) z.2) i j) k :=
        (actual_randomized_legal_moment N C H p r ν masks i j k
          (momentLevels_positive _ k hk)).trans (finiteBankMoment_enumeration _ _ _ _ _)
      exact hr.symm.trans ((hm i j k hk).trans ht)) (cfg,coin) hz
  simpa only [maskedNormalizedTree_survival N' C' H' p' r' (masks' cfg) coin i j] using hmem

end ExposingRowGrids

section ReducedPhysicalBudget
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership DotG4.ActualObservableBankCertificate
open DotG4.WeightedOrdinaryTreeLaw UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.NativeCommonPairGerm
universe u v w
variable {Y : Type w} [Fintype Y]

/-- The accepted whole-COMMON physical bound, now derived from actual word
ownership and original-bank exposure variation. This adapter takes a finite
directed support cap; the preceding mixed-row certificate supplies that cap. -/
theorem equalArmReduced_physical_hybrid_bound
    (O : PhysicalMarkedSource.{u,v,w} Y) (hred : EqualArmReduced O)
    (mask : OriginalMask O.marked.source.network) (hm : ProtectedMask O.marked mask)
    (grid : Y × Y → Finset ℝ) (Smax : Nat)
    (hcard : ∀ ij, (grid ij).card ≤ Smax)
    (hgrid : ∀ coin i j,
      realSurvival O.marked.source.network O.marked.source.calendar O.registry O.probabilities O.rates i j
        (overrideBank O.marked.source.network mask coin) ∈ grid (i,j)) :
    Fintype.card (Hybrid O.marked.source.network) ≤
      (2 * Fintype.card Y - 2 + 2 * protectedCount O.marked.source.network O.marked.marks) +
      (8 * Fintype.card Y - 8 + 6 * protectedCount O.marked.source.network O.marked.marks) * (Smax - 1) := by
  obtain ⟨T,hOT,_,_,hhyb,_,hedge⟩ := actual_finite_marked_core O.marked
  obtain ⟨D,hD,hp,hu⟩ := markedSteps_unequal_decoration O T hred hOT
  have hword (e : BridgeActor T.source) : (actorHybrids O.marked.source T.source D e).card ≤ Smax - 1 := by
    obtain ⟨i,j,_,hbound⟩ := actual_word_directed_support_lower_bound O T D hD hp e
      (bridgeSpan_sites O.marked.source T.source (UnequalSite O) D e.val e.property (hu e.val)) mask hm
    have hc := (hbound (grid (i,j)) (fun coin => hgrid coin i j)).trans (hcard (i,j))
    omega
  have hcore : Fintype.card (Hybrid T.source.network) ≤
      2 * Fintype.card Y - 2 + 2 * protectedCount O.marked.source.network O.marked.marks := by
    have hc : Fintype.card (Hybrid T.source.network) = (hybrids T.source.network).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext x
      simp only [hybrids,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hc]
    exact hhyb
  exact (actual_hybrid_count_from_word_bounds O.marked.source T.source O.registry D hD
    (Smax - 1) hword).trans (Nat.add_le_add hcore (Nat.mul_le_mul_right (Smax - 1) hedge))

end ReducedPhysicalBudget

section ProtectedPhysicalLaw
open G1ActualGraphNormalization G1ActualTwoPortBlob G1SplicedSourceAdmission
open G1DecoratedOriginalProvenance G1ExactSemidirectedPartnerAdmission
open DotG4.WholeProfileDetermination UnifiedLean.Source.OriginalFixedIDControls
universe u v w z q
variable {Y : Type w} [Fintype Y]

lemma retainedHybrid_marked_iff (N : RootedBinary V E X) (hc : CutChild N)
    (P : ProtectedIDs N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (hu : b ∉ protectedBlobs N P)
    (h : Hybrid (splicedNetwork N hc b hb A)) :
    retainedHybrid N hc b hb A h ∈ P.hybrids ↔
      h ∈ (spliceProtectedIDs N hc P b hb A hu).hybrids := by
  constructor
  · intro hh
    apply Finset.mem_map.mpr
    refine ⟨⟨retainedHybrid N hc b hb A h,hh⟩,Finset.mem_univ _,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro hh
    obtain ⟨k,_,hk⟩ := Finset.mem_map.mp hh
    have he : retainedHybrid N hc b hb A h = k.val := by
      rw [← hk]
      rfl
    exact he.symm ▸ k.property

/-- The same embedding transports the full row law and exactly the protected
hybrid identities. Thus an exposing row remains exposing after reduction. -/

lemma projected_protected_mask (O T : MarkedSource.{u,v,w} Y)
    (J : Hybrid T.source.network ↪ Hybrid O.source.network)
    (hJ : ∀ h, J h ∈ O.marks.hybrids ↔ h ∈ T.marks.hybrids)
    (mask : OriginalMask O.source.network) (hm : ProtectedMask O mask) :
    ProtectedMask T (fun h => mask (J h)) := by
  intro h hh
  exact hm (J h) (fun ho => hh ((hJ h).mp ho))

end ProtectedPhysicalLaw

section PhysicalPrimitiveProvenance
open G1ActualGraphNormalization G1ActualTwoPortBlob G1SplicedSourceAdmission
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1DecoratedSpliceConstruction
open DotG4.WholeProfileDetermination UnifiedLean.Source.OriginalFixedIDControls
universe u v w z q
variable {Y : Type w} [Fintype Y]

/-- These are literal original-ID and parameter identities, independent of any
copy allocation. The decoration also retains roots, taxa, dates and endpoints. -/
structure PhysicalPrimitiveProvenance (O T : PhysicalMarkedSource.{u,v,w} Y)
    (J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network)
    (D : Decoration O.marked.source T.marked.source) : Prop where
  originated : Originated O.marked.source O.registry D
  protected_primitives : ProtectedProvenance O.marked T.marked D
  hybrid_vertex : ∀ h, D.vertex h.val = (J h).val
  probability : ∀ h, T.probabilities.gamma h = O.probabilities.gamma (J h)
  parents : ∀ h bit, D.recipe ((T.registry.parents h).parent bit) =
    Recipe.raw ((O.registry.parents (J h)).parent bit)
  raw_rate : ∀ e f, D.recipe e = Recipe.raw f → T.rates.edge e = O.rates.edge f
  ancestral_rate : T.rates.ancestral = O.rates.ancestral

lemma physicalPrimitive_initial (O : PhysicalMarkedSource.{u,v,w} Y) :
    PhysicalPrimitiveProvenance O O (Function.Embedding.refl _) (initialDecoration O.marked.source) := by
  refine ⟨Originated.initial,protectedProvenance_initial O.marked,fun _ => rfl,
    fun _ => rfl,fun _ _ => rfl,?_,rfl⟩
  intro e f he
  cases he
  rfl

lemma physicalPrimitive_splice (O S : PhysicalMarkedSource.{u,v,w} Y)
    (J : Hybrid S.marked.source.network ↪ Hybrid O.marked.source.network)
    (D : Decoration O.marked.source S.marked.source) (hd : PhysicalPrimitiveProvenance O S J D)
    (b : S.marked.source.network.graph.Blob)
    (hb : b ≠ S.marked.source.network.graph.blobOf S.marked.source.network.root)
    (hp : Fintype.card (S.marked.source.network.BlobPort b) = 2)
    (hu : b ∉ protectedBlobs S.marked.source.network S.marked.marks) :
    let A := extractedBigon S.marked.source.network S.marked.source.cutChild b hb
      ((actual_quotient_port_card S.marked.source.network b).symm.trans hp)
    PhysicalPrimitiveProvenance O (physicalSplice S b hb hp hu)
      ((retainedHybrid S.marked.source.network S.marked.source.cutChild b hb A).trans J)
      (normalizedSpliceDecoration O.marked.source S.marked.source D O.registry b hb hp) := by
  dsimp only
  refine ⟨Originated.splice D hd.originated b hb hp,
    protectedProvenance_splice O.marked S.marked O.registry D hd.protected_primitives b hb hp hu,
    ?_,?_,?_,?_,hd.ancestral_rate⟩
  · intro h
    exact hd.hybrid_vertex (retainedHybrid S.marked.source.network S.marked.source.cutChild b hb _ h)
  · intro h
    exact hd.probability (retainedHybrid S.marked.source.network S.marked.source.cutChild b hb _ h)
  · intro h bit
    have hp' := hd.parents (retainedHybrid S.marked.source.network S.marked.source.cutChild b hb _ h) bit
    cases bit <;>
      simpa only [physicalSplice,splicedRegistry,retainedParent,GProgram.G2.OriginalHybridParents.parent,
        Bool.false_eq_true,if_false,if_true,normalizedSpliceDecoration,spliceDecoration,splicedRecipe,
        Function.Embedding.trans_apply,retainedHybrid,Function.Embedding.coeFn_mk] using hp' 
  · intro e f he
    cases e with
    | inl e => exact hd.raw_rate e.val f he
    | inr z => cases he

/- Parameter provenance and the full source law are constructed with the same
retained-ID embedding, rather than selected independently after the fact. -/

end PhysicalPrimitiveProvenance

section ConcretePhysicalTrace
open G1ActualGraphNormalization G1ActualTwoPortBlob G1SplicedSourceAdmission
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1DecoratedSpliceConstruction
open DotG4.WholeProfileDetermination UnifiedLean.Source.OriginalFixedIDControls
universe u v w z q
variable {Y : Type w} [Fintype Y]

/-- A finite construction trace in Type supports a literal recursive ID map.
No probability law is stored in the trace. -/
inductive PhysicalTrace : PhysicalMarkedSource.{u,v,w} Y → PhysicalMarkedSource.{u,v,w} Y → Type (max (u+1) (v+1) (w+1))
  | refl (O : PhysicalMarkedSource Y) : PhysicalTrace O O
  | splice {O S : PhysicalMarkedSource Y} (prior : PhysicalTrace O S)
      (b : S.marked.source.network.graph.Blob)
      (hb : b ≠ S.marked.source.network.graph.blobOf S.marked.source.network.root)
      (hp : Fintype.card (S.marked.source.network.BlobPort b) = 2)
      (hu : b ∉ protectedBlobs S.marked.source.network S.marked.marks)
      (he : EqualExtractedArms S b hb hp) : PhysicalTrace O (physicalSplice S b hb hp hu)

lemma physicalSteps_trace {O T : PhysicalMarkedSource.{u,v,w} Y} (steps : PhysicalSteps O T) :
    Nonempty (PhysicalTrace O T) := by
  induction steps with
  | refl => exact ⟨PhysicalTrace.refl _⟩
  | tail prior step ih =>
    obtain ⟨tr⟩ := ih
    cases step with
    | splice b hb hp hu he => exact ⟨PhysicalTrace.splice tr b hb hp hu he⟩

noncomputable def traceHybrid {O T : PhysicalMarkedSource.{u,v,w} Y}
    (tr : PhysicalTrace O T) : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network :=
  match tr with
  | .refl _ => Function.Embedding.refl _
  | .splice (S := S) prior b hb hp hu he =>
    let A := extractedBigon S.marked.source.network S.marked.source.cutChild b hb
      ((actual_quotient_port_card S.marked.source.network b).symm.trans hp)
    (retainedHybrid S.marked.source.network S.marked.source.cutChild b hb A).trans (traceHybrid prior)

noncomputable def traceDecoration {O T : PhysicalMarkedSource.{u,v,w} Y}
    (tr : PhysicalTrace O T) : Decoration O.marked.source T.marked.source :=
  match tr with
  | .refl _ => initialDecoration O.marked.source
  | .splice (S := S) prior b hb hp hu he =>
    normalizedSpliceDecoration O.marked.source S.marked.source (traceDecoration prior) O.registry b hb hp

lemma tracePrimitive {O T : PhysicalMarkedSource.{u,v,w} Y} (tr : PhysicalTrace O T) :
    PhysicalPrimitiveProvenance O T (traceHybrid tr) (traceDecoration tr) := by
  induction tr with
  | refl => exact physicalPrimitive_initial O
  | @splice S prior b hb hp hu he ih => exact physicalPrimitive_splice O S _ _ ih b hb hp hu

lemma traceHybrid_marks {O T : PhysicalMarkedSource.{u,v,w} Y} (tr : PhysicalTrace O T) :
    ∀ h, traceHybrid tr h ∈ O.marked.marks.hybrids ↔ h ∈ T.marked.marks.hybrids := by
  induction tr with
  | refl => intro h; exact Iff.rfl
  | @splice S prior b hb hp hu he ih =>
    intro h
    exact (ih _).trans (retainedHybrid_marked_iff S.marked.source.network S.marked.source.cutChild
      S.marked.marks b hb _ hu h)

/-- This theorem can be instantiated independently at each Copy universe; its
ID map is the same concrete traceHybrid in every instantiation. -/
theorem trace_joint_row_law {O T : PhysicalMarkedSource.{u,v,w} Y} (tr : PhysicalTrace O T)
    (Copy : Type z) [Fintype Copy] [DecidableEq Copy]
    (Config : Type q) [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask O.marked.source.network) (sample : Copy → Y) :
    randomizedFullForestLaw T.marked.source.network T.marked.source.calendar T.registry
      T.probabilities T.rates ν (fun cfg h => masks cfg (traceHybrid tr h)) sample =
    randomizedFullForestLaw O.marked.source.network O.marked.source.calendar O.registry
      O.probabilities O.rates ν masks sample := by
  induction tr generalizing masks with
  | refl => rfl
  | @splice S prior b hb hp hu he ih =>
    let A := extractedBigon S.marked.source.network S.marked.source.cutChild b hb
      ((actual_quotient_port_card S.marked.source.network b).symm.trans hp)
    calc
      _ = randomizedFullForestLaw S.marked.source.network S.marked.source.calendar S.registry
          S.probabilities S.rates ν (fun cfg h => masks cfg (traceHybrid prior h)) sample :=
        actual_equal_arm_joint_row_splice S.marked.source.network S.marked.source.cutChild
          S.marked.source.calendar S.registry S.probabilities S.rates b hb A he ν
          (fun cfg h => masks cfg (traceHybrid prior h)) sample
      _ = _ := ih masks


theorem physicalSteps_joint_row_laws (O T : PhysicalMarkedSource.{u,v,w} Y)
    (steps : PhysicalSteps O T) :
    ∃ J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network,
      ∀ (Copy : Type z) [Fintype Copy] [DecidableEq Copy]
        (Config : Type q) [Fintype Config] (ν : PMF Config)
        (masks : Config → OriginalMask O.marked.source.network) (sample : Copy → Y),
      randomizedFullForestLaw T.marked.source.network T.marked.source.calendar T.registry
        T.probabilities T.rates ν (fun cfg h => masks cfg (J h)) sample =
      randomizedFullForestLaw O.marked.source.network O.marked.source.calendar O.registry
        O.probabilities O.rates ν masks sample := by
  let tr := Classical.choice (physicalSteps_trace steps)
  exact ⟨traceHybrid tr,trace_joint_row_law tr⟩


theorem physicalSteps_protected_joint_row_laws (O T : PhysicalMarkedSource.{u,v,w} Y)
    (steps : PhysicalSteps O T) :
    ∃ J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network,
      (∀ h, J h ∈ O.marked.marks.hybrids ↔ h ∈ T.marked.marks.hybrids) ∧
      ∀ (Copy : Type z) [Fintype Copy] [DecidableEq Copy]
        (Config : Type q) [Fintype Config] (ν : PMF Config)
        (masks : Config → OriginalMask O.marked.source.network) (sample : Copy → Y),
      randomizedFullForestLaw T.marked.source.network T.marked.source.calendar T.registry
        T.probabilities T.rates ν (fun cfg h => masks cfg (J h)) sample =
      randomizedFullForestLaw O.marked.source.network O.marked.source.calendar O.registry
        O.probabilities O.rates ν masks sample := by
  let tr := Classical.choice (physicalSteps_trace steps)
  exact ⟨traceHybrid tr,traceHybrid_marks tr,trace_joint_row_law tr⟩


theorem physicalSteps_complete_transport (O T : PhysicalMarkedSource.{u,v,w} Y)
    (steps : PhysicalSteps O T) :
    ∃ J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network,
      ∃ D : Decoration O.marked.source T.marked.source,
      PhysicalPrimitiveProvenance O T J D ∧
      (∀ h, J h ∈ O.marked.marks.hybrids ↔ h ∈ T.marked.marks.hybrids) ∧
      ∀ (Copy : Type z) [Fintype Copy] [DecidableEq Copy]
        (Config : Type q) [Fintype Config] (ν : PMF Config)
        (masks : Config → OriginalMask O.marked.source.network) (sample : Copy → Y),
      randomizedFullForestLaw T.marked.source.network T.marked.source.calendar T.registry
        T.probabilities T.rates ν (fun cfg h => masks cfg (J h)) sample =
      randomizedFullForestLaw O.marked.source.network O.marked.source.calendar O.registry
        O.probabilities O.rates ν masks sample := by
  let tr := Classical.choice (physicalSteps_trace steps)
  exact ⟨traceHybrid tr,traceDecoration tr,tracePrimitive tr,traceHybrid_marks tr,trace_joint_row_law tr⟩

end ConcretePhysicalTrace

section WholeRowBuckets
open UnifiedLean.Source.NativePairClockLaw
open G1ActualGraphNormalization G1ActualTwoPortBlob G1SplicedSourceAdmission
open GProgram.G7.OriginalSurvivalCoverage
open DotG4.WholeProfileDetermination DotG4.WeightedOrdinaryTreeLaw
open UnifiedLean.Source.OriginalFixedIDControls UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeIndependentPairMixture
universe u v w q
variable {Y : Type w} [Fintype Y]

lemma randomizedTreeLaw_configuration_bind {Config : Type*} [Fintype Config]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (ν : PMF Config) (masks : Config → OriginalMask N) :
    randomizedTreeLaw N C H p r ν masks =
      ν.bind (fun cfg => (originalRegisterMeasure N p).toPMF.map
        (maskedNormalizedTree N C H r (masks cfg))) := by
  simp only [randomizedTreeLaw,configurationBankPMF,PMF.map_bind,PMF.map_comp,Function.comp_def]

lemma actual_equal_arm_tree_buckets {Config : Type*} [Fintype Config]
    (N : RootedBinary V E X) (hc : CutChild N) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (he : exposure N C r A.fragment.parents.parent0 = exposure N C r A.fragment.parents.parent1)
    (ν : PMF Config) (masks : Config → OriginalMask N) :
    randomizedTreeLaw (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc H b hb A) (splicedProbabilities N hc b hb A p)
      (splicedRates N hc C r b hb A) ν (fun cfg => projectedMask N hc b hb A (masks cfg)) =
      randomizedTreeLaw N C H p r ν masks := by
  rw [randomizedTreeLaw_configuration_bind,randomizedTreeLaw_configuration_bind]
  congr 1
  funext cfg
  rw [← projected_original_bank N hc b hb A p,PMF.map_comp]
  congr 1
  funext coin
  dsimp only [Function.comp_apply]
  unfold maskedNormalizedTree
  rw [← projectedBank_override,weightedNormalize_equal_arm_splice N hc C H r b hb A he]

/-- Duplicate configurations are aggregated by this PMF equality. Every row
retains its own supplied joint configuration law and the same physical tuple. -/
theorem trace_tree_bucket_law {O T : PhysicalMarkedSource.{u,v,w} Y} (tr : PhysicalTrace O T)
    (Config : Type q) [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask O.marked.source.network) :
    randomizedTreeLaw T.marked.source.network T.marked.source.calendar T.registry T.probabilities T.rates
      ν (fun cfg h => masks cfg (traceHybrid tr h)) =
    randomizedTreeLaw O.marked.source.network O.marked.source.calendar O.registry O.probabilities O.rates
      ν masks := by
  induction tr generalizing masks with
  | refl => rfl
  | @splice S prior b hb hp hu he ih =>
    let A := extractedBigon S.marked.source.network S.marked.source.cutChild b hb
      ((actual_quotient_port_card S.marked.source.network b).symm.trans hp)
    calc
      _ = randomizedTreeLaw S.marked.source.network S.marked.source.calendar S.registry
          S.probabilities S.rates ν (fun cfg h => masks cfg (traceHybrid prior h)) :=
        actual_equal_arm_tree_buckets S.marked.source.network S.marked.source.cutChild
          S.marked.source.calendar S.registry S.probabilities S.rates b hb A he ν
          (fun cfg h => masks cfg (traceHybrid prior h))
      _ = _ := ih masks

end WholeRowBuckets

section PhysicalRepresentative
open G1ActualGraphNormalization G1ExactSemidirectedPartnerAdmission
open DotG4.WholeProfileDetermination DotG4.ActualSparseCertificateExistence
open DotG4.ActualObservableBankCertificate DotG4.WeightedOrdinaryTreeLaw
open UnifiedLean.Source.NativeCommonPairGerm UnifiedLean.Source.OriginalFixedIDControls
universe u v w z q
variable {Y : Type w} [Fintype Y] [DecidableEq Y]

/-- A single physical tuple, chosen before all future allocations and rows,
with the accepted protected COMMON budget. The only finite observations are
mixed-row comb moments. Rival graph size and its complete hybrid registry are
not supplied as inputs to the target's certificate. -/
theorem actual_target_uniform_protected_physical_representative
    (O : PhysicalMarkedSource.{u,v,w} Y)
    {Config : Type q} [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask O.marked.source.network) :
    ∃ L : Y × Y → Nat, ∃ grid : Y × Y → Finset ℝ, ∃ Smax : Nat,
      (∀ ij, 0 < L ij) ∧ (∀ ij, (grid ij).card ≤ Smax) ∧
      ∀ (P : PhysicalMarkedSource.{u,v,w} Y) (Config' : Type q) [Fintype Config']
        (ν' : PMF Config') (masks' : Config' → OriginalMask P.marked.source.network),
        (∀ cfg, ProtectedMask P.marked (masks' cfg)) →
        (∀ i j k, k ∈ momentLevels (L (i,j)) →
          randomizedLegalCombMoment P.marked.source.network P.marked.source.calendar P.registry
            P.probabilities P.rates ν' masks' i j k =
          randomizedLegalCombMoment O.marked.source.network O.marked.source.calendar O.registry
            O.probabilities O.rates ν masks i j k) →
        ∃ R : PhysicalMarkedSource.{u,v,w} Y,
          ∃ J : Hybrid R.marked.source.network ↪ Hybrid P.marked.source.network,
          ∃ D : G1DecoratedOriginalProvenance.Decoration P.marked.source R.marked.source,
          PhysicalPrimitiveProvenance P R J D ∧ PhysicalSteps P R ∧ EqualArmReduced R ∧
          (∀ h, J h ∈ P.marked.marks.hybrids ↔ h ∈ R.marked.marks.hybrids) ∧
          Fintype.card (Hybrid R.marked.source.network) ≤
            (2 * Fintype.card Y - 2 + 2 * protectedCount P.marked.source.network P.marked.marks) +
            (8 * Fintype.card Y - 8 + 6 * protectedCount P.marked.source.network P.marked.marks) * (Smax - 1) ∧
          (HasOuterSemidirectedPartner P.marked.source → HasOuterSemidirectedPartner R.marked.source) ∧
          (∀ (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
            (controls : Cfg → OriginalMask P.marked.source.network),
            randomizedTreeLaw R.marked.source.network R.marked.source.calendar R.registry R.probabilities R.rates
              μ (fun cfg h => controls cfg (J h)) =
            randomizedTreeLaw P.marked.source.network P.marked.source.calendar P.registry P.probabilities P.rates μ controls) ∧
          ∀ (Copy : Type z) [Fintype Copy] [DecidableEq Copy]
            (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
            (controls : Cfg → OriginalMask P.marked.source.network) (sample : Copy → Y),
            randomizedFullForestLaw R.marked.source.network R.marked.source.calendar R.registry
              R.probabilities R.rates μ (fun cfg h => controls cfg (J h)) sample =
            randomizedFullForestLaw P.marked.source.network P.marked.source.calendar P.registry
              P.probabilities P.rates μ controls sample := by
  cases Subsingleton.elim (inferInstance : DecidableEq Y) (Classical.decEq Y)
  obtain ⟨L,grid,hL,hrestrict⟩ := actual_exposing_row_uniform_grids
    O.marked.source.network O.marked.source.calendar O.registry O.probabilities O.rates ν masks
  let Smax := (Finset.univ : Finset (Y × Y)).sup (fun ij => (grid ij).card)
  have hcard (ij : Y × Y) : (grid ij).card ≤ Smax := Finset.le_sup (f := fun ij => (grid ij).card) (Finset.mem_univ ij)
  refine ⟨L,grid,Smax,hL,hcard,?_⟩
  intro P Config' _ ν' masks' hprotected hmatch
  obtain ⟨R,hPR,hred⟩ := actual_finite_equal_arm_reduction P
  let tr := Classical.choice (physicalSteps_trace hPR)
  let J := traceHybrid tr
  let D := traceDecoration tr
  have hprov := tracePrimitive tr
  have hmarks := traceHybrid_marks tr
  have hmom (i j : Y) (k : Nat) :
      randomizedLegalCombMoment R.marked.source.network R.marked.source.calendar R.registry
        R.probabilities R.rates ν' (fun cfg h => masks' cfg (J h)) i j k =
      randomizedLegalCombMoment P.marked.source.network P.marked.source.calendar P.registry
        P.probabilities P.rates ν' masks' i j k := by
    unfold randomizedLegalCombMoment
    rw [trace_joint_row_law tr _ Config' ν' masks' _]
  have hgrid := hrestrict R.marked.source.Vertex R.marked.source.Edge Config'
    R.marked.source.network R.marked.source.calendar R.registry R.probabilities R.rates
    ν' (fun cfg h => masks' cfg (J h))
    (fun i j k hk => (hmom i j k).trans (hmatch i j k hk))
  obtain ⟨cfg,hcfg⟩ := ν'.support_nonempty
  have hcfg' : ν' cfg ≠ 0 := hcfg
  have hbound := equalArmReduced_physical_hybrid_bound R hred
    (fun h => masks' cfg (J h)) (projected_protected_mask P.marked R.marked J hmarks _ (hprotected cfg))
    grid Smax hcard (hgrid cfg hcfg')
  have hcount := markedSteps_count (physicalSteps_marked hPR)
  rw [hcount] at hbound
  exact ⟨R,J,D,hprov,hPR,hred,hmarks,hbound,markedSteps_outer (physicalSteps_marked hPR),trace_tree_bucket_law tr,trace_joint_row_law tr⟩

end PhysicalRepresentative

section FiniteOriginalCodes
open G1ActualGraphNormalization G1DecoratedOriginalProvenance
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
universe u v w
variable {Y : Type w} [Fintype Y] [DecidableEq Y]

/-- Every possible complete candidate registry is enumerated internally.
Only the finite protected label carriers are external. -/
abbrev ProtectedCode (Y PE PH : Type*) [Fintype Y] (B : Nat) :=
  (rr : Fin (B+1)) ×
    (Code Y (Fin rr.val) ×
      (PE → Fin (edgeCount (Fintype.card Y) rr.val)) × (PH → Fin rr.val))

noncomputable def protectedCodes (PE PH : Type*) [Fintype PE] [Fintype PH] (B : Nat) :
    Finset (ProtectedCode Y PE PH B) := Finset.univ

/-- Normalize the finite registry cardinality explicitly in edge numbering. -/
noncomputable def finiteEdgeNumbering (N : RootedBinary V E X) {r : Nat}
    (ids : Fin r ≃ Hybrid N) : E ≃ Fin (edgeCount (Fintype.card X) r) :=
  (edgeNumbering N ids).trans (finCongr (by simp))

/-- Exact graph and ordered-registry coverage, plus maps for all supplied
protected primitives. The outer witness is retained on the actual source;
this finite binary/registry filter is not advertised as an outer oracle. -/
theorem protected_original_code_coverage
    (O T : PhysicalMarkedSource.{u,v,w} Y)
    (J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network)
    (D : Decoration O.marked.source T.marked.source) (hp : PhysicalPrimitiveProvenance O T J D)
    (B : Nat) (hb : Fintype.card (Hybrid T.marked.source.network) ≤ B)
    (PE PH : Type*) [Fintype PE] [Fintype PH]
    (edgeLabels : PE ≃ O.marked.marks.edges) (hybridLabels : PH ≃ O.marked.marks.hybrids) :
    ∃ rr : Fin (B+1), ∃ ids : Fin rr.val ≃ Hybrid T.marked.source.network,
      ∃ em : PE → Fin (edgeCount (Fintype.card Y) rr.val), ∃ hm : PH → Fin rr.val,
        (⟨rr,encode T.marked.source.network ids T.registry,em,hm⟩ : ProtectedCode Y PE PH B)
          ∈ protectedCodes PE PH B ∧
        encode T.marked.source.network ids T.registry ∈
          (registeredBinaryCutChildCodes : Finset (Code Y (Fin rr.val))) ∧
        Function.Injective em ∧ Function.Injective hm ∧
        (∀ a, D.recipe ((finiteEdgeNumbering T.marked.source.network ids).symm (em a)) =
          Recipe.raw (edgeLabels a).val) ∧
        (∀ a, J (ids (hm a)) = (hybridLabels a).val) := by
  let rr : Fin (B+1) := ⟨Fintype.card (Hybrid T.marked.source.network),by omega⟩
  let ids : Fin rr.val ≃ Hybrid T.marked.source.network := (Fintype.equivFin _).symm
  have hedge (a : PE) := hp.protected_primitives.1 (edgeLabels a).val (edgeLabels a).property
  choose ef hef hrecipe using hedge
  have hhybrid (a : PH) := hp.protected_primitives.2 (hybridLabels a).val (hybridLabels a).property
  choose hf hhf hvertex using hhybrid
  have hJ (a : PH) : J (hf a) = (hybridLabels a).val := by
    apply Subtype.ext
    exact (hp.hybrid_vertex (hf a)).symm.trans (hvertex a)
  let em := fun a => finiteEdgeNumbering T.marked.source.network ids (ef a)
  let hm := fun a => ids.symm (hf a)
  refine ⟨rr,ids,em,hm,Finset.mem_univ _,?_,?_,?_,?_,?_⟩
  · exact every_registered_source_survives_filter T.marked.source.network ids T.registry T.marked.source.cutChild
  · intro a b hab
    have he : ef a = ef b := (finiteEdgeNumbering T.marked.source.network ids).injective hab
    apply edgeLabels.injective
    apply Subtype.ext
    have hr := (hrecipe a).symm.trans ((congrArg D.recipe he).trans (hrecipe b))
    exact Recipe.raw.inj hr
  · intro a b hab
    have he : hf a = hf b := ids.symm.injective hab
    apply hybridLabels.injective
    apply Subtype.ext
    exact (hJ a).symm.trans ((congrArg J he).trans (hJ b))
  · intro a
    simpa only [em,Equiv.symm_apply_apply] using hrecipe a
  · intro a
    simpa only [hm,Equiv.apply_symm_apply] using hJ a

end FiniteOriginalCodes

section ProtectedParameterConstraints
open G1ActualGraphNormalization G1DecoratedOriginalProvenance
universe u v w
variable {Y : Type w} [Fintype Y]

/-- Every predicate on the fully expanded protected rates, endpoint dates and
inheritance coordinates is preserved. This includes finite fixed/tied data;
unknown dependencies are not silently treated as protected. -/
theorem protected_parameter_constraints_preserved
    (O T : PhysicalMarkedSource.{u,v,w} Y)
    (J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network)
    (D : Decoration O.marked.source T.marked.source) (hp : PhysicalPrimitiveProvenance O T J D)
    {PE PH : Type*} (oe : PE → O.marked.source.Edge) (te : PE → T.marked.source.Edge)
    (oh : PH → Hybrid O.marked.source.network) (th : PH → Hybrid T.marked.source.network)
    (he : ∀ a, D.recipe (te a) = Recipe.raw (oe a)) (hh : ∀ a, J (th a) = oh a)
    (Q : (PE → ℝ) → (PE → ℝ) → (PE → ℝ) → (PH → ℝ) → Prop) :
    Q (fun a => T.rates.edge (te a))
      (fun a => T.marked.source.calendar.age (T.marked.source.network.graph.source (te a)))
      (fun a => T.marked.source.calendar.age (T.marked.source.network.graph.target (te a)))
      (fun a => T.probabilities.gamma (th a)) ↔
    Q (fun a => O.rates.edge (oe a))
      (fun a => O.marked.source.calendar.age (O.marked.source.network.graph.source (oe a)))
      (fun a => O.marked.source.calendar.age (O.marked.source.network.graph.target (oe a)))
      (fun a => O.probabilities.gamma (oh a)) := by
  have hr : (fun a => T.rates.edge (te a)) = (fun a => O.rates.edge (oe a)) :=
    funext (fun a => hp.raw_rate _ _ (he a))
  have hg : (fun a => T.probabilities.gamma (th a)) = (fun a => O.probabilities.gamma (oh a)) := by
    funext a
    rw [hp.probability,hh a]
  have hs (a : PE) : D.vertex (T.marked.source.network.graph.source (te a)) =
      O.marked.source.network.graph.source (oe a) := by
    have h := (D.endpoints (te a)).2
    rw [he a] at h
    exact h.symm
  have ht (a : PE) : D.vertex (T.marked.source.network.graph.target (te a)) =
      O.marked.source.network.graph.target (oe a) := by
    have h := (D.endpoints (te a)).1
    rw [he a] at h
    exact h.symm
  have hsource : (fun a => T.marked.source.calendar.age (T.marked.source.network.graph.source (te a))) =
      (fun a => O.marked.source.calendar.age (O.marked.source.network.graph.source (oe a))) := by
    funext a
    rw [D.calendar,hs a]
  have htarget : (fun a => T.marked.source.calendar.age (T.marked.source.network.graph.target (te a))) =
      (fun a => O.marked.source.calendar.age (O.marked.source.network.graph.target (oe a))) := by
    funext a
    rw [D.calendar,ht a]
  rw [hr,hg,hsource,htarget]

end ProtectedParameterConstraints

section CompleteFiniteCoverage
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1ExactSemidirectedPartnerAdmission
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open DotG4.WholeProfileDetermination DotG4.ActualSparseCertificateExistence
open UnifiedLean.Source.OriginalFixedIDControls
universe u v w z q a b
variable {Y : Type w} [Fintype Y] [DecidableEq Y]

/-- Complete protected COMMON representative/code-coverage connection.
The fixed primitive-label budget precedes the unknown rival. The candidate's
complete registry is enumerated; only protected labels are supplied. All future
laws use the same constructed positive physical tuple and original-ID maps. -/
theorem actual_protected_common_finite_original_code_coverage
    (O : PhysicalMarkedSource.{u,v,w} Y)
    {Config : Type q} [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask O.marked.source.network)
    (PE : Type a) (PH : Type b) [Fintype PE] [Fintype PH]
    (h : Nat) (hlabels : Fintype.card PE + Fintype.card PH ≤ h) (_hn : 4 ≤ Fintype.card Y) :
    ∃ L : Y × Y → Nat, ∃ Smax B : Nat,
      (∀ ij, 0 < L ij) ∧
      B = (2 * Fintype.card Y - 2 + 2*h) + (8 * Fintype.card Y - 8 + 6*h) * (Smax-1) ∧
      ∀ (P : PhysicalMarkedSource.{u,v,w} Y) (Config' : Type q) [Fintype Config']
        (ν' : PMF Config') (masks' : Config' → OriginalMask P.marked.source.network)
        (edgeLabels : PE ≃ P.marked.marks.edges) (hybridLabels : PH ≃ P.marked.marks.hybrids),
        HasOuterSemidirectedPartner P.marked.source →
        (∀ cfg, ProtectedMask P.marked (masks' cfg)) →
        (∀ i j k, k ∈ momentLevels (L (i,j)) →
          randomizedLegalCombMoment P.marked.source.network P.marked.source.calendar P.registry
            P.probabilities P.rates ν' masks' i j k =
          randomizedLegalCombMoment O.marked.source.network O.marked.source.calendar O.registry
            O.probabilities O.rates ν masks i j k) →
        ∃ R : PhysicalMarkedSource.{u,v,w} Y,
          ∃ J : Hybrid R.marked.source.network ↪ Hybrid P.marked.source.network,
          ∃ D : Decoration P.marked.source R.marked.source,
          PhysicalPrimitiveProvenance P R J D ∧ PhysicalSteps P R ∧
          HasOuterSemidirectedPartner R.marked.source ∧
          Fintype.card (Hybrid R.marked.source.network) ≤ B ∧
          (∃ rr : Fin (B+1), ∃ ids : Fin rr.val ≃ Hybrid R.marked.source.network,
            ∃ em : PE → Fin (edgeCount (Fintype.card Y) rr.val), ∃ hm : PH → Fin rr.val,
              (⟨rr,encode R.marked.source.network ids R.registry,em,hm⟩ : ProtectedCode Y PE PH B)
                ∈ protectedCodes PE PH B ∧
              encode R.marked.source.network ids R.registry ∈
                (registeredBinaryCutChildCodes : Finset (Code Y (Fin rr.val))) ∧
              Function.Injective em ∧ Function.Injective hm ∧
              (∀ a, D.recipe ((finiteEdgeNumbering R.marked.source.network ids).symm (em a)) =
                Recipe.raw (edgeLabels a).val) ∧
              (∀ a, J (ids (hm a)) = (hybridLabels a).val)) ∧
          (∀ (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
            (controls : Cfg → OriginalMask P.marked.source.network),
            randomizedTreeLaw R.marked.source.network R.marked.source.calendar R.registry R.probabilities R.rates
              μ (fun cfg h => controls cfg (J h)) =
            randomizedTreeLaw P.marked.source.network P.marked.source.calendar P.registry P.probabilities P.rates μ controls) ∧
          ∀ (Copy : Type z) [Fintype Copy] [DecidableEq Copy]
            (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
            (controls : Cfg → OriginalMask P.marked.source.network) (sample : Copy → Y),
            randomizedFullForestLaw R.marked.source.network R.marked.source.calendar R.registry
              R.probabilities R.rates μ (fun cfg h => controls cfg (J h)) sample =
            randomizedFullForestLaw P.marked.source.network P.marked.source.calendar P.registry
              P.probabilities P.rates μ controls sample := by
  obtain ⟨L,grid,Smax,hL,hgrid,hrep⟩ := actual_target_uniform_protected_physical_representative O ν masks
  let B := (2 * Fintype.card Y - 2 + 2*h) + (8 * Fintype.card Y - 8 + 6*h) * (Smax-1)
  refine ⟨L,Smax,B,hL,rfl,?_⟩
  intro P Config' _ ν' masks' edgeLabels hybridLabels houter hprotected hmatch
  obtain ⟨R,J,D,hprov,hsteps,hred,hmarks,hbound,houterR,hbuckets,hlaw⟩ :=
    hrep P Config' ν' masks' hprotected hmatch
  have hprimitive : protectedCount P.marked.source.network P.marked.marks ≤ h := by
    have he := Fintype.card_congr edgeLabels
    have hh := Fintype.card_congr hybridLabels
    simp only [Fintype.card_coe] at he hh
    unfold protectedCount
    omega
  have hb : Fintype.card (Hybrid R.marked.source.network) ≤ B := by
    apply hbound.trans
    apply Nat.add_le_add
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hprimitive) _
    · exact Nat.mul_le_mul_right (Smax-1)
        (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hprimitive) _)
  exact ⟨R,J,D,hprov,hsteps,houterR houter,hb,
    protected_original_code_coverage P R J D hprov B hb PE PH edgeLabels hybridLabels,hbuckets,hlaw⟩

end CompleteFiniteCoverage

end DotG4.ProtectedCommonRepresentative
