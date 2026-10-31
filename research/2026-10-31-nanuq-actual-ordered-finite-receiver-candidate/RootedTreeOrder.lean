import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import OccurrenceOrderReceiver
import LabelWitness
import GraphLeaves

/-! UNCOMPILED original rooted-tree join. The actual opened graph supplies
unique incoming IDs; no ordered-tree certificate is assumed. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction Nanuq.Source
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- RootedBinary plus original unique target IDs derives binary tree outdegrees. -/
theorem tree_binary_outdegree (N : RootedBinary V E X)
    (hui : Function.Injective N.graph.target) :
    ∀ v, N.graph.outDegree v=0 ∨ N.graph.outDegree v=2 := by
  intro v
  by_cases hr : v=N.root
  · subst v; exact Or.inr N.root_degrees.2
  by_cases hl : ∃ x, N.leaf x=v
  · obtain ⟨x,rfl⟩ := hl; exact Or.inl (N.leaf_degrees x).2
  rcases N.internal_degrees v hr (fun x hx => hl ⟨x,hx⟩) with ht | hh
  · exact Or.inr ht.2
  · have hi : N.graph.inDegree v≤1 := by
      apply Finset.card_le_one.mpr
      intro e he f hf
      exact hui ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
    have htwo := hh.1
    omega

/-- The actual leaf order determines an exact quartet-equivalent syntax.
No directed Represents claim is made for the reshaped output. -/
theorem rooted_tree_order_receiver (N : RootedBinary V E X)
    (hui : Function.Injective N.graph.target)
    (xs : List X) (θ : X → ℝ) (hnd : xs.Nodup) (hall : ∀ x, x∈xs)
    (hθ : Function.Injective θ) (horder : xs.Pairwise (fun a b => θ a≤θ b))
    (hcuts : ∀ (e : E) (a c d f : X),
      N.graph.OrientedQuartet e (N.leaf a) (N.leaf c) (N.leaf d) (N.leaf f) →
      ¬((θ a<θ d ∧ θ d<θ c ∧ θ c<θ f) ∨
        (θ d<θ a ∧ θ a<θ f ∧ θ f<θ c))) :
    ∃ s : BinarySyntax V, s.frontier=xs.map N.leaf ∧
      ∀ (label : V → Nat) a b c d,
        LabelledQuartet N.graph label a b c d ↔ (encode label s).Witness [] a b c d := by
  classical
  obtain ⟨t,ht⟩ := exists_represents N.graph N.acyclic (tree_binary_outdegree N hui) N.root
  have htn := frontier_nodup N.acyclic hui ht
  have hysn : (xs.map N.leaf).Nodup := hnd.map N.leaf.injective
  have hp : t.frontier.Perm (xs.map N.leaf) := by
    apply (List.perm_ext_iff_of_nodup htn hysn).mpr
    intro v
    rw [ht.mem_frontier_iff]
    constructor
    · rintro ⟨_,hz⟩
      obtain ⟨x,hx⟩ := (N.leaf_iff_outDegree_zero v).mpr hz
      exact List.mem_map.mpr ⟨x,hall x,hx⟩
    · rintro hv
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
      exact ⟨(ht.mem_nodes_iff _).mpr (N.rooted _),(N.leaf_degrees x).2⟩
  let rank : V → ℝ := fun v => if h : ∃ x, N.leaf x=v then θ (Classical.choose h) else 0
  have hrank (x : X) : rank (N.leaf x)=θ x := by
    have hx : ∃ y, N.leaf y=N.leaf x := ⟨x,rfl⟩
    dsimp [rank]
    rw [dif_pos hx]
    exact congrArg θ (N.leaf.injective (Classical.choose_spec hx))
  let code : V ↪ Nat :=
    { toFun := fun v => (Fintype.equivFin V v).val
      inj' := fun _ _ h => (Fintype.equivFin V).injective (Fin.val_injective h) }
  have hstrict : xs.Pairwise (fun a b => θ a<θ b) := by
    apply List.Pairwise.imp₂ (fun a b hab hne =>
      lt_of_le_of_ne hab (fun he => hne (hθ he))) horder hnd
  have hsort : (xs.map N.leaf).Pairwise (fun a b => rank a<rank b) := by
    simpa only [List.pairwise_map,hrank] using hstrict
  have hi : ∀ a∈xs.map N.leaf, ∀ b∈xs.map N.leaf, rank a=rank b → a=b := by
    intro a ha b hb he
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
    rw [hrank,hrank] at he
    exact congrArg N.leaf (hθ he)
  have hfin : xs.toFinset=Finset.univ := by ext x; simp [hall x]
  have hcard : Fintype.card X=xs.length := by
    simpa only [hfin,Finset.card_univ] using List.toFinset_card_of_nodup hnd
  have hsize : 2≤(xs.map N.leaf).length := by
    simpa only [List.length_map,← hcard] using N.at_least_two_taxa
  have hno : ∀ a c d e,
      a∈xs.map N.leaf → c∈xs.map N.leaf → d∈xs.map N.leaf → e∈xs.map N.leaf →
      (encode code t).Witness [] (code a) (code c) (code d) (code e) →
      ¬((rank a<rank d ∧ rank d<rank c ∧ rank c<rank e) ∨
        (rank d<rank a ∧ rank a<rank e ∧ rank e<rank c)) := by
    intro a c d e ha hc hd he hw
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hc
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hd
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp he
    have hq := (actual_labelled_witness_iff N.acyclic hui N.root N.rooted ht code _ _ _ _).mpr hw
    obtain ⟨w,x,y,z,_,⟨hw,hx,hy,hz⟩,f,hbridge,hq⟩ := hq
    have hw' := code.injective hw
    have hx' := code.injective hx
    have hy' := code.injective hy
    have hz' := code.injective hz
    subst w; subst x; subst y; subst z
    simp only [hrank]
    rcases hq with hq | hq
    · exact hcuts f a c d e hq
    · intro hbad
      apply hcuts f d e a c hq
      rcases hbad with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
      · exact Or.inr ⟨h1,h2,h3⟩
      · exact Or.inl ⟨h1,h2,h3⟩
  obtain ⟨s,hfront,hw⟩ := occurrence_order_receiver t (xs.map N.leaf) rank code
    hp hysn hsize hsort hi hno
  refine ⟨s,hfront,?_⟩
  intro label a b c d
  exact (actual_labelled_witness_iff N.acyclic hui N.root N.rooted ht label a b c d).trans
    (hw label a b c d).symm

#print axioms rooted_tree_order_receiver
end Nanuq.GraphReceiver
