import G7OriginalCensus
import UnifiedLean.Source.NativePairClockLaw
import UnifiedLean.Source.NativeIndependentPairMixture

/-!
Original edge-indexed relabelling for the G7 finite-registry census.
Contributor: dot, 2026-10-09. No source law or canonicalization completeness
is assumed. Graph admission beyond the inherited RootedBinary carrier and
whole-forest law equivariance are separate obligations.
-/
namespace GProgram.G7.OriginalRelabelling
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open scoped BigOperators
variable {V E W F X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]

def graph (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) : EdgeGraph W F where
  source f := v (G.source (e.symm f))
  target f := v (G.target (e.symm f))

@[simp] theorem graph_source (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : E) :
    (graph G v e).source (e a) = v (G.source a) := by simp [graph]
@[simp] theorem graph_target (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : E) :
    (graph G v e).target (e a) = v (G.target a) := by simp [graph]

@[simp] theorem dstep_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a b : W) :
    (graph G v e).DStep a b ↔ G.DStep (v.symm a) (v.symm b) := by
  constructor
  · rintro ⟨f, hs, ht⟩
    exact ⟨e.symm f, by simpa [graph] using congrArg v.symm hs,
      by simpa [graph] using congrArg v.symm ht⟩
  · rintro ⟨f, hs, ht⟩
    refine ⟨e f, ?_, ?_⟩
    · simpa using congrArg v hs
    · simpa using congrArg v ht

@[simp] theorem dreach_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a b : W) :
    (graph G v e).DReach a b ↔ G.DReach (v.symm a) (v.symm b) := by
  constructor
  · exact Relation.ReflTransGen.lift v.symm (fun a b h => (dstep_iff G v e a b).mp h) a b
  · intro h
    have h' := Relation.ReflTransGen.lift v
      (fun a b h => (dstep_iff G v e (v a) (v b)).mpr (by simpa using h)) _ _ h
    simpa [Function.onFun, EdgeGraph.DReach, EdgeGraph.UReach] using h'

theorem acyclic (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (h : G.Acyclic) : (graph G v e).Acyclic := by
  intro a ha
  apply h (v.symm a)
  exact Relation.TransGen.lift v.symm (fun a b h => (dstep_iff G v e a b).mp h) _ _ ha

@[simp] theorem avoidReach_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (z a b : W) : (graph G v e).AvoidReach z a b ↔
      G.AvoidReach (v.symm z) (v.symm a) (v.symm b) := by
  constructor
  · rintro ⟨ha, hb, hp⟩
    refine ⟨fun h => ha (v.symm.injective h), fun h => hb (v.symm.injective h), ?_⟩
    exact Relation.ReflTransGen.lift v.symm
      (fun a b h => ⟨(dstep_iff G v e a b).mp h.1,
        fun he => h.2.1 (v.symm.injective he), fun he => h.2.2 (v.symm.injective he)⟩) _ _ hp
  · rintro ⟨ha, hb, hp⟩
    refine ⟨fun h => ha (congrArg v.symm h), fun h => hb (congrArg v.symm h), ?_⟩
    have hp' := Relation.ReflTransGen.lift (p := fun x y => (graph G v e).DStep x y ∧ x ≠ z ∧ y ≠ z) v (fun x y h =>
      show (graph G v e).DStep (v x) (v y) ∧ v x ≠ z ∧ v y ≠ z from
        ⟨(dstep_iff G v e (v x) (v y)).mpr (by simpa using h.1),
          fun he => h.2.1 (by simpa using congrArg v.symm he),
          fun he => h.2.2 (by simpa using congrArg v.symm he)⟩) _ _ hp
    simpa [Function.onFun] using hp'

@[simp] theorem dominates_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (r z a : W) : (graph G v e).Dominates r z a ↔
      G.Dominates (v.symm r) (v.symm z) (v.symm a) := by
  simp only [EdgeGraph.Dominates, avoidReach_iff]

@[simp] theorem inDegree_eq (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : W) :
    (graph G v e).inDegree a = G.inDegree (v.symm a) := by
  classical
  simp only [EdgeGraph.inDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv e
  intro f
  simp only [graph_target]
  simp only [v.eq_symm_apply]

@[simp] theorem outDegree_eq (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : W) :
    (graph G v e).outDegree a = G.outDegree (v.symm a) := by
  classical
  simp only [EdgeGraph.outDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv e
  intro f
  simp only [graph_source]
  simp only [v.eq_symm_apply]

@[simp] theorem hybrid_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : W) :
    (graph G v e).IsHybrid a ↔ G.IsHybrid (v.symm a) := by
  simp only [EdgeGraph.IsHybrid, inDegree_eq, outDegree_eq]

/-- The same taxon type X is retained, with no permutation of the named taxa. -/
def network (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) : RootedBinary W F X where
  graph := graph N.graph v e
  root := v N.root
  leaf := N.leaf.trans v.toEmbedding
  at_least_two_taxa := N.at_least_two_taxa
  root_degrees := by simpa using N.root_degrees
  leaf_degrees x := by simpa using N.leaf_degrees x
  internal_degrees a hr hl := by
    have hr' : v.symm a ≠ N.root := fun h => hr (by simpa using congrArg v h)
    have hl' : ∀ x, N.leaf x ≠ v.symm a := by
      intro x hx
      exact hl x (by simpa using congrArg v hx)
    simpa using N.internal_degrees (v.symm a) hr' hl'
  acyclic := acyclic N.graph v e N.acyclic
  rooted a := by simpa using N.rooted (v.symm a)
  least_stable a h := by
    have ho : ∀ x, N.graph.Dominates N.root (v.symm a) (N.leaf x) := by
      intro x
      simpa using h x
    have he := N.least_stable (v.symm a) ho
    simpa using congrArg v he

/-- Strict physical durations are carried through a bijection, not refitted. -/
def calendar (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Calendar N.graph) : Calendar (network N v e).graph where
  age a := c.age (v.symm a)
  edge_older f := by simpa [network, graph] using c.edge_older (e.symm f)

/-- One positive physical rate per original edge occurrence, with ancestral rate unchanged. -/
def rates (e : E ≃ F) (r : PositivePairRates E) : PositivePairRates F where
  edge f := r.edge (e.symm f)
  edge_pos f := r.edge_pos (e.symm f)
  ancestral := r.ancestral
  ancestral_pos := r.ancestral_pos

def hybrids (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) :
    Hybrid N ≃ Hybrid (network N v e) where
  toFun h := ⟨v h.val, by simpa [network] using h.property⟩
  invFun h := ⟨v.symm h.val, by simpa [network] using h.property⟩
  left_inv h := by apply Subtype.ext; simp
  right_inv h := by apply Subtype.ext; simp

def inheritance (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (g : HybridProbabilities N) : HybridProbabilities (network N v e) where
  gamma h := g.gamma ((hybrids N v e).symm h)
  positive h := g.positive _
  below_one h := g.below_one _

theorem calendar_duration_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Calendar N.graph) (f : E) :
    (calendar N v e c).age ((network N v e).graph.source (e f)) -
      (calendar N v e c).age ((network N v e).graph.target (e f)) =
      c.age (N.graph.source f) - c.age (N.graph.target f) := by
  simp [calendar, network, graph]

theorem hazard_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Calendar N.graph) (r : PositivePairRates E) (f : E) :
    (rates e r).edge (e f) *
      ((calendar N v e c).age ((network N v e).graph.source (e f)) -
       (calendar N v e c).age ((network N v e).graph.target (e f))) =
      r.edge f * (c.age (N.graph.source f) - c.age (N.graph.target f)) := by
  rw [calendar_duration_preserved]
  simp [rates]

/-- Ordered incoming occurrences are transported separately, even when their
older endpoints coincide. The Boolean parent labels are not swapped. -/
def parents (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (h : GProgram.G2.OriginalHybridParents N) :
    GProgram.G2.OriginalHybridParents (network N v e) where
  hybrid := v h.hybrid
  isHybrid := by simpa [network] using h.isHybrid
  parent0 := e h.parent0
  parent1 := e h.parent1
  target0 := by simpa [network] using congrArg v h.target0
  target1 := by simpa [network] using congrArg v h.target1
  different := fun he => h.different (e.injective he)

def registry (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (H : OriginalParentRegistry N) : OriginalParentRegistry (network N v e) where
  parents h := parents N v e (H.parents ((hybrids N v e).symm h))
  original_site h := by
    have he := congrArg v (H.original_site ((hybrids N v e).symm h))
    simpa [parents, hybrids] using he

theorem parent_bit_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (H : OriginalParentRegistry N) (h : Hybrid N) (b : Bool) :
    ((registry N v e H).parents ((hybrids N v e) h)).parent b =
      e ((H.parents h).parent b) := by
  cases b <;> simp [registry, parents, GProgram.G2.OriginalHybridParents.parent]

theorem inheritance_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (g : HybridProbabilities N) (h : Hybrid N) :
    (inheritance N v e g).gamma ((hybrids N v e) h) = g.gamma h := by
  simp [inheritance]

@[simp] theorem inc_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (f : F) (a b : W) : (graph G v e).Inc f a b ↔
      G.Inc (e.symm f) (v.symm a) (v.symm b) := by
  simp only [EdgeGraph.Inc, graph]
  simp only [← v.eq_symm_apply]

@[simp] theorem ustep_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (keep : F → Prop) (a b : W) : (graph G v e).UStep keep a b ↔
      G.UStep (fun f => keep (e f)) (v.symm a) (v.symm b) := by
  constructor
  · rintro ⟨f, hf, hp⟩
    exact ⟨e.symm f, by simpa using hf, (inc_iff G v e f a b).mp hp⟩
  · rintro ⟨f, hf, hp⟩
    exact ⟨e f, hf, (inc_iff G v e (e f) a b).mpr (by simpa using hp)⟩

@[simp] theorem ureach_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (keep : F → Prop) (a b : W) : (graph G v e).UReach keep a b ↔
      G.UReach (fun f => keep (e f)) (v.symm a) (v.symm b) := by
  constructor
  · exact Relation.ReflTransGen.lift v.symm
      (fun a b h => (ustep_iff G v e keep a b).mp h) a b
  · intro h
    have h' := Relation.ReflTransGen.lift v
      (fun a b h => (ustep_iff G v e keep (v a) (v b)).mpr (by simpa using h)) _ _ h
    simpa [Function.onFun, EdgeGraph.DReach, EdgeGraph.UReach] using h'

@[simp] theorem bridge_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (f : F) :
    (graph G v e).IsBridge f ↔ G.IsBridge (e.symm f) := by
  change ¬ (graph G v e).UReach (fun a => a ≠ f)
    ((graph G v e).source f) ((graph G v e).target f) ↔
    ¬ G.UReach (fun a => a ≠ e.symm f) (G.source (e.symm f)) (G.target (e.symm f))
  rw [ureach_iff]
  simp only [graph, Equiv.symm_apply_apply]
  have hk : (fun a => e a ≠ f) = (fun a => a ≠ e.symm f) := by
    funext a
    apply propext
    constructor
    · intro h he
      apply h
      simpa using congrArg e he
    · intro h he
      apply h
      simpa using congrArg e.symm he
  rw [hk]

theorem cut_child_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (hc : ∀ f, N.graph.IsHybrid (N.graph.source f) → N.graph.IsBridge f) :
    ∀ f, (network N v e).graph.IsHybrid ((network N v e).graph.source f) →
      (network N v e).graph.IsBridge f := by
  intro f hf
  apply (bridge_iff N.graph v e f).mpr
  apply hc (e.symm f)
  change (graph N.graph v e).IsHybrid ((graph N.graph v e).source f) at hf
  rw [hybrid_iff] at hf
  simpa [graph] using hf

#print axioms network
#print axioms hazard_preserved
end GProgram.G7.OriginalRelabelling
