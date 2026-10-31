import LabelWitness
import FiniteEdgeBridge
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction Nanuq.Source Nanuq.AdjacentCertificate
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Exact same-source occurrence serialization into the unchanged finite Tree
and edgeWitness APIs. No adjacent-mask or geometric-order premise is smuggled in.
The resulting tip list is the actual chosen syntax frontier under the label map. -/
theorem actual_receiver_representation {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    {t : BinarySyntax V} (ht : Represents G t root) (label : V → Nat)
    (hsize : 2 ≤ t.frontier.length) :
    ∃ T : Tree, T.size = (t.frontier.map label).length - 1 ∧
      ∀ (q : Quartet) (r a b c d : Nat), q.parts r = (a,b,c,d) → a≠b → c≠d →
        (LabelledQuartet G label a b c d ↔
          ∃ e∈T.internalIntervals 1,
            edgeWitness (t.frontier.map label) e.1 e.2 q r = true) := by
  have hs : 2 ≤ ((encode label t).leaves.filter (fun _ => true)).length := by
    simpa only [List.filter_true,encode_leaves,List.length_map] using hsize
  obtain ⟨x,rest,hfull,hlist,hqueries⟩ := restriction_representation
    (fun _ => true) (encode label t) hs
  have hl : t.frontier.map label = x :: rest.leaves := by
    simpa only [List.filter_true,encode_leaves] using hlist
  refine ⟨rest.erase,?_,?_⟩
  · rw [erase_size rest hfull,hl,List.length_cons]
    omega
  · intro q r a b c d hparts hab hcd
    have hp := hqueries a b c d rfl rfl rfl rfl
    have hw := (actual_labelled_witness_iff ha hui root hr ht label a b c d).trans hp.symm
    rw [hl]
    exact hw.trans (whole_first_edgeWitness x rest hfull q r a b c d hparts hab hcd)

#print axioms actual_receiver_representation
end Nanuq.GraphReceiver
