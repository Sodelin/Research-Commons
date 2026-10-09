import G7OriginalRelabelling
import SourceLabelledForest

/-!
Actual full labelled-forest/history transport under original graph relabelling.
Contributor: dot, 2026-10-09. Continuation beyond the frozen structural census.
No probability-kernel equivalence is an input. Stochastic clock/coin and complete
calendar-law intertwining remain to be connected after this state interface.
-/
namespace GProgram.G7.SourceStateRelabelling
open Nanuq.Source GProgram.SourceForest
open GProgram.G7.OriginalRelabelling
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

def location (v : V ≃ W) (e : E ≃ F) : Location V E ≃ Location W F where
  toFun
    | .node a => .node (v a)
    | .edge f => .edge (e f)
    | .rootPopulation a => .rootPopulation (v a)
  invFun
    | .node a => .node (v.symm a)
    | .edge f => .edge (e.symm f)
    | .rootPopulation a => .rootPopulation (v.symm a)
  left_inv p := by cases p <;> simp
  right_inv p := by cases p <;> simp

@[simp] theorem location_node (v : V ≃ W) (e : E ≃ F) (a : V) :
    location v e (.node a) = .node (v a) := rfl
@[simp] theorem location_edge (v : V ≃ W) (e : E ≃ F) (f : E) :
    location v e (.edge f) = .edge (e f) := rfl
@[simp] theorem location_root (v : V ≃ W) (e : E ≃ F) (a : V) :
    location v e (.rootPopulation a) = .rootPopulation (v a) := rfl

def event (v : V ≃ W) (e : E ≃ F) : SourceEvent V E Copy → SourceEvent W F Copy
  | .merger a b p => .merger a b (location v e p)
  | .parentPulse h coin => .parentPulse (v h) coin
  | .edgeExit f => .edgeExit (e f)
  | .ordinaryEntry f => .ordinaryEntry (e f)
  | .rootEntry a => .rootEntry (v a)

/-- Live roots, original-copy ancestry and entire old genealogy are retained;
only original population names/register indices change by the graph bijection. -/
def state (v : V ≃ W) (e : E ≃ F) (s : State V E Copy) : State W F Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy := s.genealogy
  location l := location v e (s.location l)
  register a := s.register (v.symm a)
  history := s.history.map (event v e)

theorem valid (v : V ≃ W) (e : E ≃ F) (s : State V E Copy) (hs : Valid s) :
    Valid (state v e s) := ⟨hs.ancestor_live,hs.representative,hs.leaf_fiber,hs.wellLabelled⟩

@[simp] theorem copyLocation_map (v : V ≃ W) (e : E ≃ F) (s : State V E Copy) (x : Copy) :
    copyLocation (state v e s) x = location v e (copyLocation s x) := rfl

@[simp] theorem descends_iff (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (p : Location V E) (x : X) :
    DescendsTo (network N v e) (location v e p) x ↔ DescendsTo N p x := by
  cases p with
  | node a => simpa [DescendsTo,network] using
      dreach_iff N.graph v e (v a) (v (N.leaf x))
  | edge f => simpa [DescendsTo,network] using
      dreach_iff N.graph v e (v (N.graph.target f)) (v (N.leaf x))
  | rootPopulation a => simp [DescendsTo,network]

theorem sourceValid (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (sample : Copy → X) (s : State V E Copy) (hs : SourceValid N sample s) :
    SourceValid (network N v e) sample (state v e s) := by
  refine ⟨valid v e s hs.forest,?_⟩
  intro x
  rw [copyLocation_map,descends_iff]
  exact hs.original_descendant x

theorem initial_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (sample : Copy → X) (reg : V → Bool) :
    state v e (initial N sample reg) = initial (network N v e) sample (fun a => reg (v.symm a)) := rfl

theorem merge_commutes (v : V ≃ W) (e : E ≃ F) (s : State V E Copy) (a b : Copy) :
    state v e (merge s a b) = merge (state v e s) a b := by
  simp [state,merge,event,List.map_append]
  funext x
  by_cases h : s.ancestor x = b <;> simp [h]

theorem legalMerge_iff (v : V ≃ W) (e : E ≃ F) (s : State V E Copy) (a b : Copy) :
    LegalMerge (state v e s) a b ↔ LegalMerge s a b := by
  constructor
  · intro h
    refine ⟨h.first_live,h.second_live,h.different,(location v e).injective h.same_population,?_⟩
    intro z hz
    apply h.population_not_node (v z)
    exact congrArg (location v e) hz
  · intro h
    refine ⟨h.first_live,h.second_live,h.different,congrArg (location v e) h.same_population,?_⟩
    intro z hz
    apply h.population_not_node (v.symm z)
    apply (location v e).injective
    simpa only [state,location_node,Equiv.apply_symm_apply] using hz

theorem transport_commutes (v : V ≃ W) (e : E ≃ F) (s : State V E Copy)
    (p : Copy → Location V E) (a : SourceEvent V E Copy) :
    state v e (transport s p a) = transport (state v e s) (fun l => location v e (p l)) (event v e a) := by
  simp [state,transport,List.map_append]

@[simp] theorem location_eq_node (v : V ≃ W) (e : E ≃ F) (p : Location V E) (a : V) :
    location v e p = .node (v a) ↔ p = .node a :=
by
  change location v e p = location v e (.node a) ↔ p = .node a
  exact (location v e).apply_eq_iff_eq
@[simp] theorem location_eq_edge (v : V ≃ W) (e : E ≃ F) (p : Location V E) (f : E) :
    location v e p = .edge (e f) ↔ p = .edge f :=
by
  change location v e p = location v e (.edge f) ↔ p = .edge f
  exact (location v e).apply_eq_iff_eq

theorem exitEdge_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (s : State V E Copy) (f : E) :
    state v e (exitEdge N s f) = exitEdge (network N v e) (state v e s) (e f) := by
  rw [exitEdge,transport_commutes]
  congr 1
  funext l
  simp only [state,location_eq_edge]
  split_ifs <;> simp [network,graph]

theorem enterEdge_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (s : State V E Copy) (f : E) :
    state v e (enterEdge N s f) = enterEdge (network N v e) (state v e s) (e f) := by
  rw [enterEdge,transport_commutes]
  congr 1
  funext l
  simp only [state]
  simp only [network,graph_target,location_eq_node]
  split_ifs <;> simp

theorem enterRoot_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (s : State V E Copy) :
    state v e (enterRoot N s) = enterRoot (network N v e) (state v e s) := by
  rw [enterRoot,transport_commutes]
  congr 1
  funext l
  simp only [state,network,location_eq_node]
  split_ifs <;> simp

/-- Current live-ancestor coin indices correspond by the SAME copy label. -/
def atNodeEquiv (v : V ≃ W) (e : E ≃ F) (s : State V E Copy) (a : V) :
    AtNode s a ≃ AtNode (state v e s) (v a) where
  toFun l := ⟨l.val,l.property.1,congrArg (location v e) l.property.2⟩
  invFun l := ⟨l.val,l.property.1,(location_eq_node v e (s.location l.val) a).mp l.property.2⟩
  left_inv l := rfl
  right_inv l := rfl

/-- Original independent routing has one coin per current ancestor, never
one independently resampled coin per observed descendant copy. -/
theorem pulse_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy)
    (coin : AtNode s H.hybrid → Bool) :
    state v e (pulse H s coin) =
      pulse (parents N v e H) (state v e s)
        (fun l => coin ((atNodeEquiv v e s H.hybrid).symm l)) := by
  classical
  rw [pulse,transport_commutes]
  unfold pulse
  congr 1
  · funext l
    by_cases h : l ∈ s.live ∧ s.location l = .node H.hybrid
    · simp only [state, parents, location_eq_node, h, dite_true]
      change location v e (.edge (H.parent (coin ⟨l,h⟩))) =
        .edge ((parents N v e H).parent (coin ⟨l,h⟩))
      cases hc : coin ⟨l,h⟩ <;> rfl
    · simp [state,parents,location_eq_node,h]
  · change SourceEvent.parentPulse (v H.hybrid) _ = SourceEvent.parentPulse (v H.hybrid) _
    congr 1
    funext l
    change (if h : l ∈ s.live ∧ s.location l = .node H.hybrid then some (coin ⟨l,h⟩) else none) =
      (if h : l ∈ s.live ∧ location v e (s.location l) = .node (v H.hybrid) then
        some (coin ((atNodeEquiv v e s H.hybrid).symm ⟨l,h⟩)) else none)
    refine dite_congr (propext (and_congr Iff.rfl
      (location_eq_node v e (s.location l) H.hybrid).symm)) ?_ ?_
    · intro h
      rfl
    · intro h
      rfl

theorem commonPulse_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) :
    state v e (commonPulse H s) = commonPulse (parents N v e H) (state v e s) := by
  unfold commonPulse
  rw [pulse_commutes]
  simp [state,parents]

#print axioms sourceValid
#print axioms merge_commutes
#print axioms exitEdge_commutes
#print axioms enterEdge_commutes
#print axioms enterRoot_commutes
end GProgram.G7.SourceStateRelabelling
