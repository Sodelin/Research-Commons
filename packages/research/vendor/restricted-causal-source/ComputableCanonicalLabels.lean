import ExplicitProfileDecoding
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Remove the canonical-label choice bottleneck: explicit lexicographic orders,
subtype enumerations for actual active selector/root tokens, and decidable
decoded edges. No Fintype.equivFin or Fintype.ofInjective is used by these
definitions. This is the same bounded common-source construction, not a new
causal class or weakened graph target.
-/

namespace RestrictedCausal.ComputableCanonical

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection ProfileRegistry
open ExplicitProfile FiniteGraphDecision FiniteTargetImage HPLTarget

universe u v

def markKey : Mark → Fin 2
  | .tail => 0
  | .head => 1

theorem markKey_injective : Function.Injective markKey := by
  intro a b h
  cases a <;> cases b
  · rfl
  · have hn : (0 : Nat) = 1 := congrArg Fin.val h
    cases hn
  · have hn : (1 : Nat) = 0 := congrArg Fin.val h
    cases hn
  · rfl

abbrev BridgeKey (X : Type u) := X ×ₗ (X ×ₗ (Fin 2 ×ₗ Fin 2))

def bridgeKey {X : Type u} [LinearOrder X] {Q : Profile X} (b : BridgeToken Q) : BridgeKey X :=
  toLex (b.left, toLex (b.right, toLex (markKey b.leftMark, markKey b.rightMark)))

theorem bridgeKey_injective {X : Type u} [LinearOrder X] (Q : Profile X) :
    Function.Injective (bridgeKey (Q := Q)) := by
  intro a b h
  have hl := congrArg (fun p : BridgeKey X => (ofLex p).1) h
  have hr := congrArg (fun p : BridgeKey X => (ofLex (ofLex p).2).1) h
  have hml := markKey_injective (congrArg
    (fun p : BridgeKey X => (ofLex (ofLex (ofLex p).2).2).1) h)
  have hmr := markKey_injective (congrArg
    (fun p : BridgeKey X => (ofLex (ofLex (ofLex p).2).2).2) h)
  cases a
  cases b
  cases hl
  cases hr
  cases hml
  cases hmr
  rfl

def bridgeOrder {X : Type u} [LinearOrder X] (Q : Profile X) : LinearOrder (BridgeToken Q) :=
  LinearOrder.lift' bridgeKey (bridgeKey_injective Q)

def selectorOrder {X : Type u} [LinearOrder X] (Q : Profile X) : LinearOrder (Selector Q) := by
  letI : LinearOrder (BridgeToken Q) := bridgeOrder Q
  exact LinearOrder.lift' (toLex : Selector Q → {x : X // Q.parent x} ⊕ₗ BridgeToken Q) toLex.injective

def retainedOrder {X : Type u} [LinearOrder X] (Q : Profile X) :
    LinearOrder (CanonicalSelection.Vertex Q) := by
  letI : LinearOrder (Selector Q) := selectorOrder Q
  exact LinearOrder.lift' (toLex : CanonicalSelection.Vertex Q → X ⊕ₗ Selector Q) toLex.injective

abbrev BridgeTuple {X : Type u} [LinearOrder X] (Q : Profile X) :=
  {p : OrderedPair X × Mark × Mark // Q.bridge p.1.val.1 p.2.1 p.1.val.2 p.2.2}

def bridgeTupleEquiv {X : Type u} [LinearOrder X] (Q : Profile X) : BridgeToken Q ≃ BridgeTuple Q where
  toFun b := ⟨(⟨(b.left, b.right), b.ordered⟩, b.leftMark, b.rightMark), b.allowed⟩
  invFun p := ⟨p.val.1.val.1, p.val.1.val.2, p.val.2.1, p.val.2.2, p.val.1.property, p.property⟩
  left_inv b := by cases b; rfl
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨⟨⟨x, y⟩, hxy⟩, mx, my⟩, hp⟩
    rfl

def activeBridgeFintype {X : Type u} [LinearOrder X] [Fintype X] (Q : Profile X)
    (hb : ∀ x mx y my, Decidable (Q.bridge x mx y my)) : Fintype (BridgeToken Q) := by
  letI : DecidablePred (fun p : OrderedPair X × Mark × Mark =>
      Q.bridge p.1.val.1 p.2.1 p.1.val.2 p.2.2) :=
    fun p => hb p.1.val.1 p.2.1 p.1.val.2 p.2.2
  letI : Fintype (BridgeTuple Q) := Fintype.subtype
    (Finset.univ.filter (fun p : OrderedPair X × Mark × Mark =>
      Q.bridge p.1.val.1 p.2.1 p.1.val.2 p.2.2)) (by intro p; simp)
  exact Fintype.ofEquiv (BridgeTuple Q) (bridgeTupleEquiv Q).symm

/-- The usual finite disjoint-sum construction, written explicitly so an
older noncomputable selector instance cannot be selected by elaboration. -/
def sumFintype (A : Type u) (B : Type v) [Fintype A] [Fintype B] : Fintype (Sum A B) where
  elems := Finset.univ.disjSum Finset.univ
  complete := by rintro (a | b) <;> simp

def activeSelectorFintype {X : Type u} [LinearOrder X] [Fintype X] (Q : Profile X)
    (hf : DecidablePred Q.parent) (hb : ∀ x mx y my, Decidable (Q.bridge x mx y my)) :
    Fintype (Selector Q) := by
  letI : DecidablePred Q.parent := hf
  letI : Fintype {x : X // Q.parent x} :=
    Fintype.subtype (Finset.univ.filter Q.parent) (by intro x; simp)
  letI : Fintype (BridgeToken Q) := activeBridgeFintype Q hb
  exact sumFintype {x : X // Q.parent x} (BridgeToken Q)

abbrev RootTuple {V : Type u} [LinearOrder V] (G : MarkedGraph V) :=
  {p : OrderedPair V // G.edge p.val.1 p.val.2 .head .head}

def rootTupleEquiv {V : Type u} [LinearOrder V] (G : MarkedGraph V) : Root G ≃ RootTuple G where
  toFun r := ⟨⟨(r.left, r.right), r.ordered⟩, r.edge⟩
  invFun p := ⟨p.val.val.1, p.val.val.2, p.val.property, p.property⟩
  left_inv r := by cases r; rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rcases p with ⟨⟨⟨x, y⟩, hxy⟩, hp⟩
    rfl

def activeRootFintype {V : Type u} [LinearOrder V] [Fintype V] (G : MarkedGraph V)
    (he : ∀ a b ma mb, Decidable (G.edge a b ma mb)) : Fintype (Root G) := by
  letI : DecidablePred (fun p : OrderedPair V => G.edge p.val.1 p.val.2 .head .head) :=
    fun p => he p.val.1 p.val.2 .head .head
  letI : Fintype (RootTuple G) := Fintype.subtype
    (Finset.univ.filter (fun p : OrderedPair V => G.edge p.val.1 p.val.2 .head .head))
    (by intro p; simp)
  exact Fintype.ofEquiv (RootTuple G) (rootTupleEquiv G).symm

def decidableEqOfInjection {A : Type u} {B : Type v} [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) : DecidableEq A := fun a b =>
  if h : f a = f b then isTrue (hf h) else isFalse (fun heq => h (congrArg f heq))

def rootDecidableEq {V : Type u} [LinearOrder V] (G : MarkedGraph V) : DecidableEq (Root G) :=
  decidableEqOfInjection (rootTupleEquiv G) (rootTupleEquiv G).injective

def decodedEdgeDecision {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X)
    (x y : X) (mx my : Mark) : Decidable ((decodedObserved c).edge x y mx my) := by
  letI : Decidable (EdgeCycleFree (rawObserved c)) := cycleFreeDecision c
  by_cases h : EdgeCycleFree (rawObserved c)
  · simpa only [decodedObserved, if_pos h, dif_pos h] using rawEdgeDecision c x y mx my
  · simpa only [decodedObserved, if_neg h, dif_neg h, emptyObserved] using (isFalse id : Decidable False)

def decodedParentDecision {X : Type u} [LinearOrder X] [Fintype X]
    (c : RegistryCode X) (x : X) : Decidable ((decodedProfile c).parent x) :=
  inferInstanceAs (Decidable (c.1 x = true))

def decodedBridgeDecision {X : Type u} [LinearOrder X] [Fintype X]
    (c : RegistryCode X) (x : X) (mx : Mark) (y : X) (my : Mark) :
    Decidable ((decodedProfile c).bridge x mx y my) := by
  letI : Decidable (rawBridge c x mx y my) := pairReadDecision
    (fun p m n => (c.2 p).2 (m, n) = true) (fun _ _ _ => inferInstance) x mx y my
  change Decidable (rawBridge c x mx y my ∧ (mx = .tail → c.1 x = true) ∧ (my = .tail → c.1 y = true))
  infer_instance

def canonicalGraphEdgeDecision {X : Type u} [LinearOrder X] [Fintype X]
    (c : RegistryCode X) (a b : CanonicalSelection.Vertex (decodedProfile c)) (ma mb : Mark) :
    Decidable ((SourceSelection.graph (SourceSelection.canonical (decodedProfile c))).edge a b ma mb) := by
  rcases a with (x | s) <;> rcases b with (y | t)
  · exact decodedEdgeDecision c x y ma mb
  · cases t <;> dsimp [SourceSelection.graph, SourceSelection.canonical, CanonicalSelection.Incident] <;> infer_instance
  · cases s <;> dsimp [SourceSelection.graph, SourceSelection.canonical, CanonicalSelection.Incident] <;> infer_instance
  · exact isFalse (fun h => h.1)

def profileDAG {X : Type u} [LinearOrder X] (Q : AdmissibleProfile X) :
    letI : LinearOrder (CanonicalSelection.Vertex Q.val) := retainedOrder Q.val
    SourceDAG X (Selector Q.val) (Root (SourceSelection.graph (SourceSelection.canonical Q.val))) := by
  letI : LinearOrder (CanonicalSelection.Vertex Q.val) := retainedOrder Q.val
  exact {
    arrow := Arrow (SourceSelection.graph (SourceSelection.canonical Q.val))
    acyclic := root_expansion_acyclic (SourceSelection.graph (SourceSelection.canonical Q.val))
      (SourceSelection.selected_directed_acyclic (SourceSelection.canonical Q.val) Q.property.2)
    selection_sink := SourceSelection.canonical_dag_selection_sinks Q.val }

/-- A concrete, computably enumerated canonical finite source for every code.
No runtime has been used to check elaboration or evaluate this definition. -/
def codeSource {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) : FiniteSource X := by
  let Q := decode c
  letI : LinearOrder (CanonicalSelection.Vertex Q.val) := retainedOrder Q.val
  letI : Fintype (Selector Q.val) := activeSelectorFintype Q.val
    (decodedParentDecision c) (decodedBridgeDecision c)
  letI : Fintype (CanonicalSelection.Vertex Q.val) := sumFintype X (Selector Q.val)
  let G := SourceSelection.graph (SourceSelection.canonical Q.val)
  letI : Fintype (Root G) := activeRootFintype G (canonicalGraphEdgeDecision c)
  exact {
    selections := Selector Q.val
    latents := Root G
    selectionFintype := inferInstance
    latentFintype := inferInstance
    dag := profileDAG Q }

theorem profileDAG_original_preserves {X : Type u} {S : Type u} {L : Type u}
    [LinearOrder X] (D : SourceDAG X S L) :
    SourcePreserves D (profileDAG (originalProfile D)) ∧
      ∀ t : X, SourcePreserves (augmentSource D t) (augmentSource (profileDAG (originalProfile D)) t) := by
  letI : LinearOrder (CanonicalSelection.Vertex (sourceProfile D)) := retainedOrder (sourceProfile D)
  exact ⟨canonical_baseline_preserves D, canonical_indicator_preserves D⟩

/-- The new computable label/order choice is plugged into the same original
DAG preservation theorem, not inferred from a different canonical registry. -/
theorem codeSource_original_preserves {X : Type u} [LinearOrder X] [Fintype X]
    (D : FiniteSource X) :
    SourcePreserves D.dag (codeSource (encode (originalProfile D.dag))).dag ∧
      ∀ t : X, SourcePreserves (augmentSource D.dag t)
        (augmentSource (codeSource (encode (originalProfile D.dag))).dag t) := by
  change SourcePreserves D.dag (profileDAG (decode (encode (originalProfile D.dag)))) ∧
    ∀ t : X, SourcePreserves (augmentSource D.dag t)
      (augmentSource (profileDAG (decode (encode (originalProfile D.dag)))) t)
  rw [decode_encode]
  exact profileDAG_original_preserves D.dag

theorem codeSource_original_signature {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) :
    SameElementarySignature T D (codeSource (encode (originalProfile D.dag))) :=
  same_signature_of_preserves T D _ (codeSource_original_preserves D).1
    (fun t => (codeSource_original_preserves D).2 t.val)

theorem codeSource_original_target {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) :
    tcm D.dag T = tcm (codeSource (encode (originalProfile D.dag))).dag T :=
  tcm_eq_of_all_mags D.dag _ T (fun t => ((codeSource_original_preserves D).2 t.val).mag_eq)

theorem card_enumeration_independent (V : Type u) («first» second : Fintype V) :
    @Fintype.card V «first» = @Fintype.card V second :=
  @Fintype.card_congr V V «first» second (Equiv.refl V)

/-- The exact original bounds survive the changed finite enumerations and
the explicit lexicographic root order. No cardinality is inferred from an
unrelated typeclass instance. -/
theorem codeSource_size_bounds {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) :
    @Fintype.card (codeSource c).selections (codeSource c).selectionFintype ≤
        Fintype.card X + 4 * (Fintype.card X).choose 2 ∧
      @Fintype.card (codeSource c).latents (codeSource c).latentFintype ≤
        9 * (Fintype.card X).choose 2 := by
  let Q := decode c
  letI : LinearOrder (CanonicalSelection.Vertex Q.val) := retainedOrder Q.val
  constructor
  · have heq : @Fintype.card (Selector Q.val) (codeSource c).selectionFintype =
        Fintype.card (Selector Q.val) := card_enumeration_independent _ _ _
    exact heq.trans_le (selector_card_bound Q.val)
  · have heq : @Fintype.card (Root (SourceSelection.graph (SourceSelection.canonical Q.val)))
        (codeSource c).latentFintype =
        Fintype.card (Root (SourceSelection.graph (SourceSelection.canonical Q.val))) :=
      card_enumeration_independent _ _ _
    exact heq.trans_le (canonical_hidden_root_bound Q.val)

end RestrictedCausal.ComputableCanonical
