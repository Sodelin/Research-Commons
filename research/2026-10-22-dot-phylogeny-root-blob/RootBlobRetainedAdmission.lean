import RootBlobRetainedMaximal

/-!
# Simple/root-LSA admission for the retained-port target
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler or verification claim.

The target retains degree-two ports; it is NOT declared binary. This module
proves the actual DAG, no-parallel and root-LSA obligations separately from
the fixed-parameter image equality. No arbitrary target rank is accepted.
-/

open RootBlobInterfaces RootBlobEdgeIndexed RootBlobBoundaryGraph
open RootBlobMaximalSource RootBlobBinaryReplacement RootBlobCutFactorization
open RootBlobRetainedPortGraph RootBlobRetainedPortModel RootBlobRetainedMaximal
namespace RootBlobRetainedAdmission
universe u v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable {G : Network V E O} (R : PortComponent G)

theorem fork_boundarySource_injective :
    Function.Injective (boundarySource (B := R.Outside) rootedFork) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg Sum.inl (RootBlobTreeMarginals.rootedFork_graph.1 (Sum.inl.inj h))
    | inr b => exact False.elim (Sum.noConfusion h)
  | inr a =>
    cases b with
    | inl b => exact False.elim (Sum.noConfusion h)
    | inr b => exact congrArg Sum.inr (Sum.inr.inj h)

theorem retainedFork_noParallel (hG : GraphAdmitted G) (hNP : NoParallel G) :
    NoParallel (R.retainedFork hG) := by
  intro e f hs ht
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      exact congrArg Sum.inl (RootBlobTreeMarginals.rootedFork_graph.1 (Sum.inl.inj ht))
    | inr f => exact False.elim (Sum.noConfusion ht)
  | inr e =>
    cases f with
    | inl f => exact False.elim (Sum.noConfusion ht)
    | inr f =>
      have hext : R.exteriorSource e = R.exteriorSource f :=
        R.fork_boundarySource_injective hs
      have hsrc : G.source e.val = G.source f.val := by
        apply R.vertexEquiv.injective
        rw [R.exterior_source_partition e, R.exterior_source_partition f, hext]
      have htgt : G.target e.val = G.target f.val :=
        congrArg Subtype.val (Sum.inr.inj ht)
      exact congrArg Sum.inr (Subtype.ext (hNP e.val f.val hsrc htgt))

def originalOf : Sum (Fin 3) R.Outside → V
  | Sum.inl v => if v = 0 then G.root else if v = 1 then R.ports 0 else R.ports 1
  | Sum.inr v => v.val

theorem originalOf_port (p : Fin 2) :
    R.originalOf (Sum.inl (rootedFork.observed p)) = R.ports p := by
  fin_cases p <;> simp [originalOf, rootedFork]

theorem originalOf_nonroot (hG : GraphAdmitted G)
    (z : Sum (Fin 3) R.Outside) (hz : z ≠ (R.retainedFork hG).root) :
    R.originalOf z ≠ G.root := by
  cases z with
  | inl z =>
    fin_cases z
    · exact False.elim (hz rfl)
    · simpa [originalOf] using R.ports_nonroot 0
    · simpa [originalOf] using R.ports_nonroot 1
  | inr z =>
    intro he
    have hzval : z.val = G.root := he
    exact z.property (by simpa [hzval] using R.root_mem)

noncomputable def collapseVertex (v : V) : Sum (Fin 3) R.Outside := by
  classical
  exact if h : v ∈ R.vertices then Sum.inl 0 else Sum.inr ⟨v, h⟩

theorem collapse_avoids (hG : GraphAdmitted G)
    (z : Sum (Fin 3) R.Outside) (hz : z ≠ (R.retainedFork hG).root)
    {v : V} (hv : v ≠ R.originalOf z) : R.collapseVertex v ≠ z := by
  classical
  cases z with
  | inl z =>
    fin_cases z
    · exact False.elim (hz rfl)
    · by_cases hm : v ∈ R.vertices <;> simp [collapseVertex, hm]
    · by_cases hm : v ∈ R.vertices <;> simp [collapseVertex, hm]
  | inr z =>
    unfold collapseVertex
    split_ifs with hm
    · simp
    · intro he
      exact hv (congrArg Subtype.val (Sum.inr.inj he))

theorem port_avoids (z : Sum (Fin 3) R.Outside) (p : Fin 2)
    (hp : R.ports p ≠ R.originalOf z) : Sum.inl (rootedFork.observed p) ≠ z := by
  intro he
  apply hp
  have hh := congrArg R.originalOf he
  rwa [R.originalOf_port p] at hh

/-- An original crossing edge is lifted to TWO actual fork edges; it is
never replaced by a nonexistent direct root-to-outside edge. -/
theorem collapse_avoiding_path (hG : GraphAdmitted G)
    (z : Sum (Fin 3) R.Outside) (hz : z ≠ (R.retainedFork hG).root)
    {a b : V} (hp : Relation.ReflTransGen (AvoidArc G (R.originalOf z)) a b) :
    Relation.ReflTransGen (AvoidArc (R.retainedFork hG) z)
      (R.collapseVertex a) (R.collapseVertex b) := by
  classical
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    rcases hbc with ⟨hb, hc, e, hs, ht⟩
    by_cases htarget : G.target e ∈ R.vertices
    · have hsource := R.ancestral e htarget
      have hsame : R.collapseVertex b = R.collapseVertex c := by
        simp [collapseVertex, ← hs, ← ht, hsource, htarget]
      exact hsame ▸ ih
    · let e' : R.OuterEdge := ⟨e, htarget⟩
      have htgt : (R.retainedFork hG).target (Sum.inr e') = R.collapseVertex c := by
        simp [retainedFork, cutNetwork, exterior, collapseVertex, e', ← ht, htarget]
      by_cases hsource : G.source e ∈ R.vertices
      · obtain ⟨p, hp⟩ := R.outgoing_ports e hsource htarget
        have hpa : R.ports p ≠ R.originalOf z := by simpa [hp, hs] using hb
        have hpz := R.port_avoids z p hpa
        have hsrc0 : (R.retainedFork hG).source (Sum.inl p) = R.collapseVertex b := by
          fin_cases p <;>
            simp [retainedFork, cutNetwork, rootedFork, collapseVertex, ← hs, hsource]
        have htgt0 : (R.retainedFork hG).target (Sum.inl p) =
            Sum.inl (rootedFork.observed p) := rfl
        have hsrc1 : (R.retainedFork hG).source (Sum.inr e') =
            Sum.inl (rootedFork.observed p) :=
          (R.fork_source_port hG e' p).mpr hp.symm
        exact (ih.tail ⟨R.collapse_avoids hG z hz hb, hpz,
          Sum.inl p, hsrc0, htgt0⟩).tail
          ⟨hpz, R.collapse_avoids hG z hz hc, Sum.inr e', hsrc1, htgt⟩
      · have hsrc : (R.retainedFork hG).source (Sum.inr e') = R.collapseVertex b := by
          have hh := (R.fork_source_outside hG e' ⟨G.source e, hsource⟩).mpr rfl
          simpa [collapseVertex, ← hs, hsource] using hh
        exact ih.tail ⟨R.collapse_avoids hG z hz hb,
          R.collapse_avoids hG z hz hc, Sum.inr e', hsrc, htgt⟩

theorem retainedFork_rootLSA (hG : GraphAdmitted G) (hLSA : RootLSA G) :
    RootLSA (R.retainedFork hG) := by
  classical
  intro z hz
  obtain ⟨o, ho⟩ := hLSA (R.originalOf z) (R.originalOf_nonroot hG z hz)
  refine ⟨o, ?_⟩
  have hh := R.collapse_avoiding_path hG z hz ho
  simpa [collapseVertex, R.root_mem, R.hidden o, retainedFork, cutNetwork,
    rootedFork, labels, boundarySource] using hh

/-- The final open-H source-to-source endpoint, with target admission and
fixed original exterior matrices explicit in the conclusion. The source
remains binary/simple/root-LSA. The target is its admitted retained-port
DAG, not a claim of binary admission for degree-two vertices. -/
theorem maximal_fixed_exterior_admitted {S : Type u} [Fintype S] [Nonempty S]
    (B : MaximalRootTwoBlob G) (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    (hNP : NoParallel G) (hLSA : RootLSA G)
    (W : E → ℝ) (hW : WeightsAdmitted G W)
    (MX : (B.component hG hB).OuterEdge → Mat S)
    (H : Subgroup (Equiv.Perm S)) (hMX : ∀ e, OpenTransition H (MX e))
    (_hS : 1 < Fintype.card S) :
    let R := B.component hG hB
    GraphAdmitted (R.retainedFork hG) ∧ NoParallel (R.retainedFork hG) ∧
    RootLSA (R.retainedFork hG) ∧
    WeightsAdmitted (R.retainedFork hG) (R.retainedWeights W) ∧
    R.fixedImage W MX H =
      cutImage rootedFork (R.exterior hG) R.labels R.forkRank
        forkWeights (R.outsideWeights W) MX H := by
  let R := B.component hG hB
  obtain ⟨hF, hFW, hImage⟩ := R.fixed_exterior_full hG W hW MX H hMX
  exact ⟨hF, R.retainedFork_noParallel hG hNP, R.retainedFork_rootLSA hG hLSA,
    hFW, hImage⟩

end RootBlobRetainedAdmission
