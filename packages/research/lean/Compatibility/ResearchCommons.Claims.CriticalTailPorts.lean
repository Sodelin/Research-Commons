import SamuelAlexanderResearch.GeneralRigidity
import PortEncoding

/-! Frozen CB-POPULATION-002 full-card owner/type correspondence, NOT adopted.
Original actual critical simple population, finite-root/chronology/labelled
parent/child premises remain. Persistent minimum cuts yield adjacency alone;
encoding requires neither minimum width nor periodicity. Full NAMED-slot and
replacement-label schedule periodicity is a separate positive-period premise
for arbitrary-word strict paths. Finite slots do not imply periodicity.
No pre-base reconstruction, canonical-sorted/converse written companion,
effective infinite-graph encoder, new method or historical novelty claim. -/
set_option autoImplicit false
noncomputable section
namespace ResearchCommons.Claims.CriticalTailPorts
universe u
open PopulationCounting InfiniteConservation PortEncoding PortDynamics

theorem persistent_minimum_tail {k : Nat} (p : InfiniteLabeledPopulation k k)
    (start : Nat) (hr : p.rootSupport ≤ start)
    (hc : ∀ n, start ≤ n → crossingCount p n = triangular k) :
    ∀ u, start ≤ u → ∀ v,
      (p.edge u v).isSome = true ↔ u < v ∧ v ≤ u+k := by
  exact GeneralRigidity.minimum_tail_edges p start hr hc

theorem eventual_minimum_rigidity {k : Nat} (p : InfiniteLabeledPopulation k k)
    (hc : ∃ start, ∀ n, start ≤ n → crossingCount p n = k*(k+1)/2) :
    ∃ start, ∀ u, start ≤ u → ∀ v,
      (p.edge u v).isSome = true ↔ u < v ∧ v ≤ u+k := by
  exact GeneralRigidity.eventually_minimum_tail_edges p hc

theorem actual_eventual_fair_encoding {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ base C, ∃ S : PortDynamics.Schedule C (Fin k),
      ∃ init : Fin C → PortDynamics.Token (Fin k),
      p.rootSupport ≤ base ∧ C = Fintype.card (Cut p base) ∧
      Nonempty (PortDynamics.Legal S base init) ∧ PortDynamics.Fair S ∧
      (∀ u v (a : Fin k), base ≤ v →
        (p.edge u v = some a.val ↔ PortDynamics.DecodedEdge S base init u v a)) ∧
      (∀ u v label, base ≤ v → p.edge u v = some label → label < k) := by
  exact PortEncoding.eventual_encoding p

theorem actual_tail_labelled_edge_iff {k : Nat} (p : InfiniteLabeledPopulation k k) (base : Nat) (hr : Regular p base) (u v : Nat) (a : Fin k)
    (hv : base ≤ v) :
    p.edge u v = some a.val ↔
      PortDynamics.DecodedEdge (schedule p base hr) base (initial p base hr) u v a := by
  exact PortEncoding.encoding_exact p base hr u v a hv

theorem actual_schedule_fair {k : Nat} (p : InfiniteLabeledPopulation k k) (base : Nat) (hr : Regular p base) :
    PortDynamics.Fair (schedule p base hr) := by
  exact PortEncoding.encoding_fair p base hr

theorem actual_encoded_periodic_realization {k : Nat} (p : InfiniteLabeledPopulation k k) (base : Nat) (hr : Regular p base)
    {M period : Nat} (hp : 0 < period)
    (hperiod : PortDynamics.PeriodicAfter (schedule p base hr) M period)
    (s : Nat → Fin k) :
    ∃ path : Nat → Nat, base+M ≤ path 0 ∧ path 0 < base+M+period ∧
      ∀ n, path n < path (n+1) ∧ p.edge (path n) (path (n+1)) = some (s n).val := by
  exact PortEncoding.encoded_periodic_realizes p base hr hp hperiod s

theorem full_labelled_periodic_schedule_realizes_strict {C : Nat} {A : Type} {S : Schedule C A}
    (base : Nat) (initial : Fin C → Token A) {M p : Nat}
    (hp : 0 < p) (period : PeriodicAfter S M p)
    (coverage : IncomingCoverage S base initial) (s : Nat → A) :
    ∃ path : Nat → Nat, base+M ≤ path 0 ∧ path 0 < base+M+p ∧
      ∀ n, path n < path (n+1) ∧
        DecodedEdge S base initial (path n) (path (n+1)) (s n) := by
  exact PortDynamics.periodic_schedule_realizes_strict base initial hp period coverage s

/-- One actual constructed schedule supplies the fair exact encoding AND
conditional periodic realization. Regularity is output from the original
critical graph theorem, not an extra original-population hypothesis. -/
theorem same_constructed_actual_schedule {k : Nat} (p : InfiniteLabeledPopulation k k) :
    ∃ base, ∃ hr : PortEncoding.Regular p base,
      p.rootSupport ≤ base ∧
      Nonempty (PortDynamics.Legal (PortEncoding.schedule p base hr) base (PortEncoding.initial p base hr)) ∧
      PortDynamics.Fair (PortEncoding.schedule p base hr) ∧
      (∀ u v (a : Fin k), base ≤ v →
        (p.edge u v = some a.val ↔ PortDynamics.DecodedEdge (PortEncoding.schedule p base hr)
          base (PortEncoding.initial p base hr) u v a)) ∧
      (∀ u v label, base ≤ v → p.edge u v = some label → label < k) ∧
      (∀ M period : Nat, 0 < period →
        PortDynamics.PeriodicAfter (PortEncoding.schedule p base hr) M period →
        ∀ s : Nat → Fin k, ∃ path : Nat → Nat,
          base+M ≤ path 0 ∧ path 0 < base+M+period ∧
          ∀ n, path n < path (n+1) ∧ p.edge (path n) (path (n+1)) = some (s n).val) := by
  obtain ⟨base,hroot,hr,_⟩ := InfiniteConservation.eventual_structure p
  refine ⟨base,hr,hroot,⟨PortEncoding.encoding_legal p base hr⟩,
    PortEncoding.encoding_fair p base hr,PortEncoding.encoding_exact p base hr,
    PortEncoding.tail_label_lt p base hr,?_⟩
  intro M period hp hperiod s
  exact PortEncoding.encoded_periodic_realizes p base hr hp hperiod s

end ResearchCommons.Claims.CriticalTailPorts
