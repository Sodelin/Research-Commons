import G7OriginalFiniteEncoding
import G7FiniteReachability
import Mathlib.Data.Fintype.Inv

/-!
Executable directed/bridge admission tests on the finite original code.
Contributor: dot, 2026-10-09. The planar/cofacial-taxa admission test is not
implemented here and remains a separate obligation of full G7 admission.
-/
namespace GProgram.G7.OriginalAdmission
open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding
open GProgram.G7.FiniteReachability
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

instance decidableDStep (G : EdgeGraph V E) : DecidableRel G.DStep :=
  fun a b => inferInstanceAs (Decidable (∃ e, G.source e = a ∧ G.target e = b))
instance decidableDReach (G : EdgeGraph V E) : DecidableRel G.DReach :=
  decideReach G.DStep
instance decidableTransGen (R : V → V → Prop) [DecidableRel R] (a b : V) :
    Decidable (Relation.TransGen R a b) := by
  letI : DecidableRel (Relation.ReflTransGen R) := decideReach R
  exact decidable_of_iff (∃ c, R a c ∧ Relation.ReflTransGen R c b)
    Relation.TransGen.head'_iff.symm
instance decidableAcyclic (G : EdgeGraph V E) : Decidable G.Acyclic :=
  inferInstanceAs (Decidable (∀ a, ¬ Relation.TransGen G.DStep a a))
instance decidableAvoidReach (G : EdgeGraph V E) (z a b : V) :
    Decidable (G.AvoidReach z a b) := by
  letI : DecidableRel (Relation.ReflTransGen (fun x y => G.DStep x y ∧ x ≠ z ∧ y ≠ z)) :=
    decideReach _
  exact inferInstanceAs (Decidable (a ≠ z ∧ b ≠ z ∧
    Relation.ReflTransGen (fun x y => G.DStep x y ∧ x ≠ z ∧ y ≠ z) a b))
instance decidableDominates (G : EdgeGraph V E) (r z a : V) : Decidable (G.Dominates r z a) :=
  inferInstanceAs (Decidable (¬G.AvoidReach z r a))
instance decidableInc (G : EdgeGraph V E) (e : E) (a b : V) : Decidable (G.Inc e a b) :=
  inferInstanceAs (Decidable ((G.source e = a ∧ G.target e = b) ∨ (G.source e = b ∧ G.target e = a)))
instance decidableUStep (G : EdgeGraph V E) (keep : E → Prop) [DecidablePred keep] :
    DecidableRel (G.UStep keep) :=
  fun a b => inferInstanceAs (Decidable (∃ e, keep e ∧ G.Inc e a b))
instance decidableUReach (G : EdgeGraph V E) (keep : E → Prop) [DecidablePred keep] :
    DecidableRel (G.UReach keep) := decideReach (G.UStep keep)
instance decidableBridge (G : EdgeGraph V E) (e : E) : Decidable (G.IsBridge e) :=
  inferInstanceAs (Decidable (¬ G.UReach (fun f => f ≠ e) (G.source e) (G.target e)))
instance decidableHybrid (G : EdgeGraph V E) (v : V) : Decidable (G.IsHybrid v) :=
  inferInstanceAs (Decidable (G.inDegree v = 2 ∧ G.outDegree v = 1))

variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
abbrev NV := Fin (vertexCount (Fintype.card X) (Fintype.card ID))
abbrev NE := Fin (edgeCount (Fintype.card X) (Fintype.card ID))
def codeGraph (c : Code X ID) : EdgeGraph (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)) :=
  ⟨c.1,c.2.1⟩
def codeRoot (c : Code X ID) : NV (X:=X) (ID:=ID) := c.2.2.1
def codeLeaf (c : Code X ID) : X → NV (X:=X) (ID:=ID) := c.2.2.2.1

def BinaryValid (c : Code X ID) : Prop :=
  Function.Injective (codeLeaf c) ∧ 2 ≤ Fintype.card X ∧
  ((codeGraph c).inDegree (codeRoot c) = 0 ∧ (codeGraph c).outDegree (codeRoot c) = 2) ∧
  (∀ x, (codeGraph c).inDegree (codeLeaf c x) = 1 ∧ (codeGraph c).outDegree (codeLeaf c x) = 0) ∧
  (∀ a, a ≠ codeRoot c → (∀ x, codeLeaf c x ≠ a) →
    ((codeGraph c).inDegree a = 1 ∧ (codeGraph c).outDegree a = 2) ∨ (codeGraph c).IsHybrid a) ∧
  (codeGraph c).Acyclic ∧
  (∀ a, (codeGraph c).DReach (codeRoot c) a) ∧
  (∀ a, (∀ x, (codeGraph c).Dominates (codeRoot c) a (codeLeaf c x)) → a = codeRoot c)

instance decidableBinaryValid (c : Code X ID) : Decidable (BinaryValid c) := by
  unfold BinaryValid Function.Injective
  infer_instance

def CutChild (c : Code X ID) : Prop :=
  ∀ f, (codeGraph c).IsHybrid ((codeGraph c).source f) → (codeGraph c).IsBridge f
instance decidableCutChild (c : Code X ID) : Decidable (CutChild c) := by
  unfold CutChild
  infer_instance

/-- Every accepted code is constructed into the inherited original source
carrier. No desired observation law or arbitrary admission oracle is supplied. -/
def sourceOfValid (c : Code X ID) (h : BinaryValid c) :
    RootedBinary (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)) X where
  graph := codeGraph c
  root := codeRoot c
  leaf := ⟨codeLeaf c,h.1⟩
  at_least_two_taxa := h.2.1
  root_degrees := h.2.2.1
  leaf_degrees := h.2.2.2.1
  internal_degrees := h.2.2.2.2.1
  acyclic := h.2.2.2.2.2.1
  rooted := h.2.2.2.2.2.2.1
  least_stable := h.2.2.2.2.2.2.2

def binaryCutChildCodes : Finset (Code X ID) :=
  allCodes.filter (fun c => BinaryValid c ∧ CutChild c)

theorem encoded_binary_valid {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N) :
    BinaryValid (encode N ids H) := by
  let M := numberedSource N ids
  exact ⟨M.leaf.injective, M.at_least_two_taxa, M.root_degrees, M.leaf_degrees,
    M.internal_degrees, M.acyclic, M.rooted, M.least_stable⟩

theorem encoded_cut_child {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N)
    (hc : ∀ f, N.graph.IsHybrid (N.graph.source f) → N.graph.IsBridge f) :
    CutChild (encode N ids H) :=
  GProgram.G7.OriginalRelabelling.cut_child_preserved N _ _ hc

def codeSite (c : Code X ID) : ID → NV (X:=X) (ID:=ID) := c.2.2.2.2.1
def codeParent (c : Code X ID) : ID → Bool → NE (X:=X) (ID:=ID) := c.2.2.2.2.2

def RegistryValid (c : Code X ID) : Prop :=
  Function.Injective (codeSite c) ∧
  (∀ i, (codeGraph c).IsHybrid (codeSite c i)) ∧
  (∀ a, (codeGraph c).IsHybrid a → ∃ i, codeSite c i = a) ∧
  (∀ i b, (codeGraph c).target (codeParent c i b) = codeSite c i) ∧
  (∀ i, codeParent c i false ≠ codeParent c i true)
instance decidableRegistryValid (c : Code X ID) : Decidable (RegistryValid c) := by
  unfold RegistryValid Function.Injective
  infer_instance

/-- This still awaits the separate outer-labelled planarity test. It is an
exact executable census of the binary LSA cut-child and named-registry part. -/
def registeredBinaryCutChildCodes : Finset (Code X ID) :=
  allCodes.filter (fun c => BinaryValid c ∧ CutChild c ∧ RegistryValid c)

theorem encoded_registry_valid {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N) :
    RegistryValid (encode N ids H) := by
  refine ⟨?_, ?_, ?_, encoded_parent_target N ids H, encoded_parent_bits_distinct N ids H⟩
  · intro i j he
    apply ids.injective
    apply Subtype.ext
    exact (vertexNumbering N ids).injective he
  · intro i
    change (GProgram.G7.OriginalRelabelling.graph N.graph (vertexNumbering N ids)
      (edgeNumbering N ids)).IsHybrid ((vertexNumbering N ids) (ids i).val)
    simpa using (ids i).property
  · intro a ha
    have ho : N.graph.IsHybrid ((vertexNumbering N ids).symm a) := by
      exact (GProgram.G7.OriginalRelabelling.hybrid_iff N.graph _ _ a).mp ha
    refine ⟨ids.symm ⟨(vertexNumbering N ids).symm a,ho⟩, ?_⟩
    simp [codeSite,encode]

theorem every_registered_source_survives_filter {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N)
    (hc : ∀ f, N.graph.IsHybrid (N.graph.source f) → N.graph.IsBridge f) :
    encode N ids H ∈ (registeredBinaryCutChildCodes : Finset (Code X ID)) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,encoded_binary_valid N ids H,
    encoded_cut_child N ids H hc,encoded_registry_valid N ids H⟩

open UnifiedLean.Source.NativeParentRouting

/-- Every accepted registry is an exact bijection onto the reconstructed
source's actual hybrid vertices, rather than a subset of available IDs. -/
def decodedHybridMap (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    ID → Hybrid (sourceOfValid c hb) := fun i => ⟨codeSite c i,hr.2.1 i⟩

theorem decodedHybridMap_bijective (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    Function.Bijective (decodedHybridMap c hb hr) := by
  constructor
  · intro i j he
    exact hr.1 (congrArg Subtype.val he)
  · intro h
    obtain ⟨i,hi⟩ := hr.2.2.1 h.val h.property
    exact ⟨i,Subtype.ext hi⟩

def decodedIDs (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    ID ≃ Hybrid (sourceOfValid c hb) where
  toFun := decodedHybridMap c hb hr
  invFun := Fintype.bijInv (decodedHybridMap_bijective c hb hr)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

def decodedRegistry (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    OriginalParentRegistry (sourceOfValid c hb) where
  parents h := {
    hybrid := h.val
    isHybrid := h.property
    parent0 := codeParent c ((decodedIDs c hb hr).symm h) false
    parent1 := codeParent c ((decodedIDs c hb hr).symm h) true
    target0 := by
      have he := hr.2.2.2.1 ((decodedIDs c hb hr).symm h) false
      have hs := congrArg Subtype.val ((decodedIDs c hb hr).apply_symm_apply h)
      exact he.trans hs
    target1 := by
      have he := hr.2.2.2.1 ((decodedIDs c hb hr).symm h) true
      have hs := congrArg Subtype.val ((decodedIDs c hb hr).apply_symm_apply h)
      exact he.trans hs
    different := hr.2.2.2.2 _ }
  original_site _ := rfl

theorem decoded_parent_exact (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (i : ID) (b : Bool) :
    ((decodedRegistry c hb hr).parents ((decodedIDs c hb hr) i)).parent b = codeParent c i b := by
  cases b <;> simp [decodedRegistry,GProgram.G2.OriginalHybridParents.parent]

#print axioms decidableBinaryValid
#print axioms sourceOfValid
end GProgram.G7.OriginalAdmission
