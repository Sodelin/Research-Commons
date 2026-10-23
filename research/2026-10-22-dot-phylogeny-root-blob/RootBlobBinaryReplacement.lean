import RootBlobMaximalSource

/-!
# The actual degree-two-suppressed replacement and source admission
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No execution or verification.

The target here has a fresh root and the ORIGINAL outside vertices. Its
edge type is precisely the original edges with outside targets. It does
not retain degree-two ports. Binary/simple admission is proved separately
from the state-sum image equality assembled in the identification module.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobEdgeIndexed RootBlobBoundaryGraph
open RootBlobMaximalSource RootBlobBoundaryAdapter
namespace RootBlobBinaryReplacement
universe u v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable {G : Network V E O}
variable (R : RootTwoBoundaryRegion G)

abbrev Outside := {v : V // v ∉ R.vertices}
abbrev OuterEdge := {e : E // G.target e ∉ R.vertices}
noncomputable instance : Fintype R.Outside := Fintype.ofFinite _
noncomputable instance : Fintype R.OuterEdge := Fintype.ofFinite _

noncomputable def replacement : Network (Sum Unit R.Outside) R.OuterEdge O := by
  classical
  exact {
    root := Sum.inl ()
    observed := fun o => Sum.inr ⟨G.observed o, R.hidden o⟩
    source := fun e => if h : G.source e.val ∈ R.vertices then Sum.inl ()
      else Sum.inr ⟨G.source e.val, h⟩
    target := fun e => Sum.inr ⟨G.target e.val, e.property⟩
    rank := fun v => match v with
      | Sum.inl _ => 0
      | Sum.inr v => G.rank v.val + 2 }

def replacementWeights (W : E → ℝ) : R.OuterEdge → ℝ := fun e => W e.val

noncomputable def exitEdge (hG : GraphAdmitted G) (i : Fin 2) : R.OuterEdge :=
  ⟨R.boundaryEdge i, (R.boundary_out hG i).2⟩

theorem exit_distinct (hG : GraphAdmitted G) : R.exitEdge hG 0 ≠ R.exitEdge hG 1 := by
  intro h
  have hv := congrArg Subtype.val h
  exact R.pair.distinct (by simpa [exitEdge, boundaryEdge] using hv)

theorem source_root_iff (e : R.OuterEdge) :
    R.replacement.source e = Sum.inl () ↔ G.source e.val ∈ R.vertices := by
  classical
  unfold replacement
  split_ifs <;> simp_all

theorem source_outside_iff (e : R.OuterEdge) (v : R.Outside) :
    R.replacement.source e = Sum.inr v ↔ G.source e.val = v.val := by
  classical
  by_cases hs : G.source e.val ∈ R.vertices
  · have hn : G.source e.val ≠ v.val := by intro h; exact v.property (h ▸ hs)
    simp [replacement, hs, hn]
  · simp only [replacement, dif_neg hs, Sum.inr.injEq]
    exact Subtype.ext_iff

theorem target_outside_iff (e : R.OuterEdge) (v : R.Outside) :
    R.replacement.target e = Sum.inr v ↔ G.target e.val = v.val := by
  simp only [replacement, Sum.inr.injEq]
  exact Subtype.ext_iff

theorem outside_target_of_source (hG : GraphAdmitted G) {e : E}
    (hs : G.source e ∉ R.vertices) : G.target e ∉ R.vertices := by
  intro ht
  exact hs (R.ancestral hG e ht)

theorem replacement_admitted (hG : GraphAdmitted G) : GraphAdmitted R.replacement := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact hG.1 (congrArg Subtype.val (Sum.inr.inj h))
  · intro o h
    exact Sum.noConfusion h
  · intro e
    by_cases hs : G.source e.val ∈ R.vertices
    · simp [replacement, hs]
    · have hr := hG.2.2.1 e.val
      simpa [replacement, hs] using Nat.add_lt_add_right hr 2
  · intro e h
    exact Sum.noConfusion h
  · intro v hv
    cases v with
    | inl v => cases v; exact False.elim (hv rfl)
    | inr v =>
      have hn : v.val ≠ G.root := by intro h; exact v.property (by simpa [h] using R.root_mem)
      obtain ⟨e, he⟩ := hG.2.2.2.2.1 v.val hn
      have ht : G.target e ∉ R.vertices := by simpa [he] using v.property
      exact ⟨⟨e, ht⟩, (R.target_outside_iff _ v).mpr he⟩
  · intro v
    cases v with
    | inl v =>
      cases v
      constructor
      · intro hs
        exact False.elim (hs (R.exitEdge hG 0)
          ((R.source_root_iff _).mpr (R.boundary_out hG 0).1))
      · rintro ⟨o, ho⟩
        exact False.elim (Sum.noConfusion ho)
    | inr v =>
      constructor
      · intro hs
        have hold : ∀ e, G.source e ≠ v.val := by
          intro e he
          have hsource : G.source e ∉ R.vertices := by simpa [he] using v.property
          let e' : R.OuterEdge := ⟨e, R.outside_target_of_source hG hsource⟩
          exact hs e' ((R.source_outside_iff e' v).mpr he)
        obtain ⟨o, ho⟩ := (hG.2.2.2.2.2 v.val).mp hold
        exact ⟨o, congrArg Sum.inr (Subtype.ext ho)⟩
      · rintro ⟨o, ho⟩ e he
        have ho' : G.observed o = v.val := congrArg Subtype.val (Sum.inr.inj ho)
        have he' := (R.source_outside_iff e v).mp he
        exact ((hG.2.2.2.2.2 v.val).mpr ⟨o, ho'⟩) e.val he'

theorem replacement_weights_admitted (W : E → ℝ) (hW : WeightsAdmitted G W) :
    WeightsAdmitted R.replacement (R.replacementWeights W) := by
  classical
  constructor
  · intro e
    exact hW.1 e.val
  · intro v hv
    cases v with
    | inl v => cases v; exact False.elim (hv rfl)
    | inr v =>
      have hn : v.val ≠ G.root := by intro h; exact v.property (by simpa [h] using R.root_mem)
      have hsum : (∑ e : R.OuterEdge, if G.target e.val = v.val then W e.val else 0) =
          ∑ e : E, if G.target e = v.val then W e else 0 := by
        rw [← Finset.sum_subtype (Finset.univ.filter (fun e => G.target e ∉ R.vertices))
          (by intro e; simp) (fun e => if G.target e = v.val then W e else 0)]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : G.target e = v.val
        · have hout : G.target e ∉ R.vertices := by simpa [he] using v.property
          simp [he, hout]
        · simp [he]
      have ht : ∀ e : R.OuterEdge,
          (if R.replacement.target e = Sum.inr v then R.replacementWeights W e else 0) =
            if G.target e.val = v.val then W e.val else 0 := by
        intro e
        rw [R.target_outside_iff]
        rfl
      simp_rw [ht]
      rw [hsum]
      exact hW.2 v.val hn

theorem incoming_card_outside (v : R.Outside) :
    (incomingEdges R.replacement (Sum.inr v)).card = (incomingEdges G v.val).card := by
  classical
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    have ht : R.replacement.target e = Sum.inr v := by simpa [incomingEdges] using he
    simpa [incomingEdges] using (R.target_outside_iff e v).mp ht
  · intro a ha b hb h
    exact Subtype.ext h
  · intro e he
    have ht : G.target e = v.val := by simpa [incomingEdges] using he
    let e' : R.OuterEdge := ⟨e, by simpa [ht] using v.property⟩
    refine ⟨e', ?_, rfl⟩
    simpa [incomingEdges] using (R.target_outside_iff e' v).mpr ht

theorem outgoing_card_outside (hG : GraphAdmitted G) (v : R.Outside) :
    (outgoingEdges R.replacement (Sum.inr v)).card = (outgoingEdges G v.val).card := by
  classical
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    have hs : R.replacement.source e = Sum.inr v := by simpa [outgoingEdges] using he
    simpa [outgoingEdges] using (R.source_outside_iff e v).mp hs
  · intro a ha b hb h
    exact Subtype.ext h
  · intro e he
    have hs : G.source e = v.val := by simpa [outgoingEdges] using he
    have hout : G.source e ∉ R.vertices := by simpa [hs] using v.property
    let e' : R.OuterEdge := ⟨e, R.outside_target_of_source hG hout⟩
    refine ⟨e', ?_, rfl⟩
    simpa [outgoingEdges] using (R.source_outside_iff e' v).mpr hs

theorem outgoing_root (hG : GraphAdmitted G) :
    outgoingEdges R.replacement R.replacement.root = {R.exitEdge hG 0, R.exitEdge hG 1} := by
  classical
  ext e
  simp only [outgoingEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  rw [R.source_root_iff]
  constructor
  · intro hs
    rcases (R.pair.cover e.val).mp (Or.inl ⟨hs, e.property⟩) with he | he
    · exact Or.inl (Subtype.ext (by simpa [exitEdge, boundaryEdge] using he))
    · exact Or.inr (Subtype.ext (by simpa [exitEdge, boundaryEdge] using he))
  · rintro (rfl | rfl)
    · exact (R.boundary_out hG 0).1
    · exact (R.boundary_out hG 1).1

theorem replacement_binary (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    BinaryAdmission R.replacement := by
  classical
  constructor
  · constructor
    · simp [incomingEdges, replacement]
    · rw [R.outgoing_root hG]
      simp [R.exit_distinct hG]
  · intro o
    change (incomingEdges R.replacement (Sum.inr ⟨G.observed o, R.hidden o⟩)).card = 1 ∧
      (outgoingEdges R.replacement (Sum.inr ⟨G.observed o, R.hidden o⟩)).card = 0
    rw [R.incoming_card_outside, R.outgoing_card_outside hG]
    exact hB.leaf_degrees o
  · intro v hv ho
    cases v with
    | inl v => cases v; exact False.elim (hv rfl)
    | inr v =>
      have hn : v.val ≠ G.root := by intro h; exact v.property (by simpa [h] using R.root_mem)
      have hobs : ∀ o, G.observed o ≠ v.val := by
        intro o he
        exact ho o (congrArg Sum.inr (Subtype.ext he))
      rw [R.incoming_card_outside, R.outgoing_card_outside hG]
      exact hB.internal_degrees v.val hn hobs

def NoParallel {V E O : Type*} (N : Network V E O) : Prop :=
  ∀ e f, N.source e = N.source f → N.target e = N.target f → e = f

/-- Exact edge-cardinality alone is insufficient here. Distinct outside
targets follows from maximality in the original source, not from R alone. -/
theorem replacement_noParallel (hG : GraphAdmitted G) (hNP : NoParallel G)
    (htargets : G.target R.pair.first ≠ G.target R.pair.second) :
    NoParallel R.replacement := by
  classical
  intro e f hs ht
  have ht' : G.target e.val = G.target f.val := congrArg Subtype.val (Sum.inr.inj ht)
  by_cases he : G.source e.val ∈ R.vertices
  · have hr : R.replacement.source f = Sum.inl () := hs.symm.trans ((R.source_root_iff e).mpr he)
    have hf := (R.source_root_iff f).mp hr
    rcases (R.pair.cover e.val).mp (Or.inl ⟨he, e.property⟩) with he0 | he1 <;>
      rcases (R.pair.cover f.val).mp (Or.inl ⟨hf, f.property⟩) with hf0 | hf1
    · exact Subtype.ext (he0.trans hf0.symm)
    · exact False.elim (htargets (by simpa [he0, hf1] using ht'))
    · exact False.elim (htargets (by simpa [he1, hf0] using ht'.symm))
    · exact Subtype.ext (he1.trans hf1.symm)
  · let v : R.Outside := ⟨G.source e.val, he⟩
    have hes : R.replacement.source e = Sum.inr v := (R.source_outside_iff e v).mpr rfl
    have hfs : G.source f.val = G.source e.val :=
      (R.source_outside_iff f v).mp (hs.symm.trans hes)
    exact Subtype.ext (hNP e.val f.val hfs.symm ht')

theorem maximal_replacement_noParallel (B : MaximalRootTwoBlob G)
    (hG : GraphAdmitted G) (hB : BinaryAdmission G) (hNP : NoParallel G) :
    NoParallel (B.region hG hB).replacement := by
  let R := B.region hG hB
  apply R.replacement_noParallel hG hNP
  exact B.exit_targets_distinct R.pair.distinct
    (R.first_outgoing hG) (R.second_outgoing hG)

def AvoidArc {V E O : Type*} (N : Network V E O) (forbidden : V) (a b : V) : Prop :=
  a ≠ forbidden ∧ b ≠ forbidden ∧ RootBlobBoundaryGraph.Arc N a b

/-- No nonroot vertex is on every root-to-observed-leaf path. This is the
last-stable-ancestor clause in Brits Definition 2.1, stated as an avoiding
path for each candidate vertex. -/
def RootLSA {V E O : Type*} (N : Network V E O) : Prop :=
  ∀ v, v ≠ N.root → ∃ o,
    Relation.ReflTransGen (AvoidArc N v) N.root (N.observed o)

noncomputable def collapseVertex (v : V) : Sum Unit R.Outside := by
  classical
  exact if h : v ∈ R.vertices then Sum.inl () else Sum.inr ⟨v, h⟩

theorem collapse_avoids (v : R.Outside) {a : V} (ha : a ≠ v.val) :
    R.collapseVertex a ≠ Sum.inr v := by
  classical
  unfold collapseVertex
  split_ifs with h
  · simp
  · intro he
    exact ha (congrArg Subtype.val (Sum.inr.inj he))

theorem collapse_avoiding_path (hG : GraphAdmitted G) (v : R.Outside) {a b : V}
    (hp : Relation.ReflTransGen (AvoidArc G v.val) a b) :
    Relation.ReflTransGen (AvoidArc R.replacement (Sum.inr v))
      (R.collapseVertex a) (R.collapseVertex b) := by
  classical
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    rcases hbc with ⟨hb, hc, e, hs, ht⟩
    by_cases htarget : G.target e ∈ R.vertices
    · have hsource := R.ancestral hG e htarget
      have hsame : R.collapseVertex b = R.collapseVertex c := by
        simp [collapseVertex, ← hs, ← ht, hsource, htarget]
      exact hsame ▸ ih
    · let e' : R.OuterEdge := ⟨e, htarget⟩
      have hsrc : R.replacement.source e' = R.collapseVertex b := by
        simp [replacement, collapseVertex, e', hs]
      have htgt : R.replacement.target e' = R.collapseVertex c := by
        simp [replacement, collapseVertex, e', ← ht, htarget]
      exact ih.tail ⟨R.collapse_avoids v hb, R.collapse_avoids v hc, e', hsrc, htgt⟩

theorem replacement_rootLSA (hG : GraphAdmitted G) (hLSA : RootLSA G) :
    RootLSA R.replacement := by
  classical
  intro v hv
  cases v with
  | inl v => cases v; exact False.elim (hv rfl)
  | inr v =>
    have hn : v.val ≠ G.root := by
      intro h
      exact v.property (by simpa [h] using R.root_mem)
    obtain ⟨o, ho⟩ := hLSA v.val hn
    refine ⟨o, ?_⟩
    have hh := R.collapse_avoiding_path hG v ho
    simpa [collapseVertex, R.root_mem, R.hidden o, replacement] using hh

end RootBlobBinaryReplacement
