import ComputableCanonicalLabels

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

A concrete finite decoder for EVERY elementary-query history. Output is a
Boolean encoding of the full labeled marked HPL TCM, with an exact decoding
theorem. The accepted source must fit the entire history. The theorem below
identifies the original structural-source version-space image, not independent
indicator classes. The B-query policy, statistical faithfulness realization and
G7 integration remain separate full-theorem dependencies.
-/

namespace RestrictedCausal.TranscriptDecoder

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget ProfileRegistry FiniteTargetImage FiniteGraphDecision ComputableCanonical

universe u

inductive ElementaryAction (X : Type u) (T : X → Prop)
  | ci (x y : X) (conditioning : X → Bool)
  | invariance (target : {x : X // T x}) (x : X) (conditioning : X → Bool)

def actionEquiv {X : Type u} {T : X → Prop} :
    ElementaryAction X T ≃ (X × X × (X → Bool)) ⊕ ({x : X // T x} × X × (X → Bool)) where
  toFun a := match a with
    | .ci x y b => .inl (x, y, b)
    | .invariance t x b => .inr (t, x, b)
  invFun a := match a with
    | .inl (x, y, b) => .ci x y b
    | .inr (t, x, b) => .invariance t x b
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with (⟨x, y, b⟩ | ⟨t, x, b⟩) <;> rfl

instance actionFintype {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] : Fintype (ElementaryAction X T) :=
  Fintype.ofEquiv ((X × X × (X → Bool)) ⊕ ({x : X // T x} × X × (X → Bool))) actionEquiv.symm

instance actionDecidableEq {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) : DecidableEq (ElementaryAction X T) :=
  decidableEqOfInjection actionEquiv actionEquiv.injective

def LegalAction {X : Type u} (T : X → Prop) : ElementaryAction X T → Prop
  | .ci x y b => x ≠ y ∧ ¬ BoolCondition b x ∧ ¬ BoolCondition b y
  | .invariance _ x b => ¬ BoolCondition b x

/-- True means the stated selected separation. Invalid coordinates have a
fixed false response only to totalize the finite action encoding. The eventual
query policy must separately prove it asks LegalAction coordinates. -/
def PositiveAnswer {X : Type u} [DecidableEq X] {T : X → Prop}
    (D : FiniteSource X) : ElementaryAction X T → Prop
  | .ci x y b =>
      if x ≠ y ∧ ¬ BoolCondition b x ∧ ¬ BoolCondition b y then
        ¬ ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition (BoolCondition b)) (Observed x) (Observed y)
      else False
  | .invariance t x b =>
      if ¬ BoolCondition b x then
        ¬ ActiveConnection (arrowGraph (augmentSource D.dag t.val).arrow)
          (SelectedCondition (InvarianceCondition (BoolCondition b))) (Observed none) (Observed (some x))
      else False

theorem answer_preserved {X : Type u} [DecidableEq X] {T : X → Prop}
    {D E : FiniteSource X} (h : SameElementarySignature T D E) (a : ElementaryAction X T) :
    PositiveAnswer D a ↔ PositiveAnswer E a := by
  cases a with
  | ci x y b =>
      by_cases hg : x ≠ y ∧ ¬ BoolCondition b x ∧ ¬ BoolCondition b y
      · simpa only [PositiveAnswer, if_pos hg] using
          not_congr (h.baseline (BoolCondition b) x y hg.1 hg.2.1 hg.2.2)
      · simp only [PositiveAnswer, if_neg hg]
  | invariance t x b =>
      by_cases hg : ¬ BoolCondition b x
      · simpa only [PositiveAnswer, if_pos hg] using not_congr (h.invariance t (BoolCondition b) x hg)
      · simp only [PositiveAnswer, if_neg hg]

abbrev History (X : Type u) (T : X → Prop) := List (ElementaryAction X T × Bool)

def SourceConsistent {X : Type u} [DecidableEq X] {T : X → Prop}
    (D : FiniteSource X) (h : History X T) : Prop :=
  ∀ ay ∈ h, PositiveAnswer D ay.1 ↔ ay.2 = true

theorem consistent_preserved {X : Type u} [DecidableEq X] {T : X → Prop}
    {D E : FiniteSource X} (hsig : SameElementarySignature T D E) (h : History X T) :
    SourceConsistent D h ↔ SourceConsistent E h :=
  ⟨fun hd ay hay => (answer_preserved hsig ay.1).symm.trans (hd ay hay),
    fun he ay hay => (answer_preserved hsig ay.1).trans (he ay hay)⟩

def sourceSelectionEq {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) :
    DecidableEq (codeSource c).selections := by
  letI : LinearOrder (Selector (ExplicitProfile.decode c).val) := selectorOrder (ExplicitProfile.decode c).val
  change DecidableEq (Selector (ExplicitProfile.decode c).val)
  infer_instance

def sourceLatentEq {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) :
    DecidableEq (codeSource c).latents := by
  let Q := ExplicitProfile.decode c
  letI : LinearOrder (CanonicalSelection.Vertex Q.val) := retainedOrder Q.val
  exact rootDecidableEq (SourceSelection.graph (SourceSelection.canonical Q.val))

def sourceArrowDecision {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X)
    (a b : SourceVertex X (codeSource c).selections (codeSource c).latents) :
    Decidable ((codeSource c).dag.arrow a b) := by
  let Q := ExplicitProfile.decode c
  letI : LinearOrder (CanonicalSelection.Vertex Q.val) := retainedOrder Q.val
  change Decidable (Arrow (SourceSelection.graph (SourceSelection.canonical Q.val)) a b)
  rcases a with (x | r) <;> rcases b with (y | s)
  · exact canonicalGraphEdgeDecision c x y .tail .head
  · exact isFalse id
  · change Decidable (@Eq (CanonicalSelection.Vertex Q.val) y r.left ∨
      @Eq (CanonicalSelection.Vertex Q.val) y r.right)
    infer_instance
  · exact isFalse id

def invarianceConditionDecision {X : Type u} (b : X → Bool) :
    DecidablePred (InvarianceCondition (BoolCondition b)) := fun x => by
  cases x with
  | none => exact isFalse id
  | some x => exact boolConditionDecision b x

def answerDecision {X : Type u} [LinearOrder X] [Fintype X] {T : X → Prop}
    (c : RegistryCode X) (a : ElementaryAction X T) : Decidable (PositiveAnswer (codeSource c) a) := by
  letI : Fintype (codeSource c).selections := (codeSource c).selectionFintype
  letI : Fintype (codeSource c).latents := (codeSource c).latentFintype
  letI : DecidableEq (codeSource c).selections := sourceSelectionEq c
  letI : DecidableEq (codeSource c).latents := sourceLatentEq c
  letI : DecidableRel (codeSource c).dag.arrow := sourceArrowDecision c
  cases a with
  | ci x y b =>
      letI : Decidable (ActiveConnection (arrowGraph (codeSource c).dag.arrow)
          (SelectedCondition (BoolCondition b)) (Observed x) (Observed y)) :=
        selectedConnectionDecision (codeSource c).dag (BoolCondition b) x y
      unfold PositiveAnswer
      infer_instance
  | invariance t x b =>
      letI : DecidableRel (augmentSource (codeSource c).dag t.val).arrow :=
        augmentedArrowDecision (codeSource c).dag t.val
      letI : DecidablePred (InvarianceCondition (BoolCondition b)) := invarianceConditionDecision b
      letI : Decidable (ActiveConnection (arrowGraph (augmentSource (codeSource c).dag t.val).arrow)
          (SelectedCondition (InvarianceCondition (BoolCondition b))) (Observed none) (Observed (some x))) :=
        selectedConnectionDecision (augmentSource (codeSource c).dag t.val)
          (InvarianceCondition (BoolCondition b)) none (some x)
      unfold PositiveAnswer
      infer_instance

def codeAnswer {X : Type u} [LinearOrder X] [Fintype X] {T : X → Prop}
    (c : RegistryCode X) (a : ElementaryAction X T) : Bool :=
  @decide (PositiveAnswer (codeSource c) a) (answerDecision c a)

theorem codeAnswer_correct {X : Type u} [LinearOrder X] [Fintype X] {T : X → Prop}
    (c : RegistryCode X) (a : ElementaryAction X T) :
    codeAnswer c a = true ↔ PositiveAnswer (codeSource c) a := by
  simp only [codeAnswer, decide_eq_true_eq]

theorem bool_eq_iff_truth_iff (p q : Bool) : p = q ↔ (p = true ↔ q = true) := by
  cases p <;> cases q <;> simp

def CodeConsistent {X : Type u} [LinearOrder X] [Fintype X] {T : X → Prop}
    (c : RegistryCode X) (h : History X T) : Prop := ∀ ay ∈ h, codeAnswer c ay.1 = ay.2

instance codeConsistentDecision {X : Type u} [LinearOrder X] [Fintype X]
    {T : X → Prop} [DecidablePred T] (c : RegistryCode X) (h : History X T) :
    Decidable (CodeConsistent c h) := by
  unfold CodeConsistent
  infer_instance

theorem code_consistent_iff {X : Type u} [LinearOrder X] [Fintype X] {T : X → Prop}
    (c : RegistryCode X) (h : History X T) : CodeConsistent c h ↔ SourceConsistent (codeSource c) h := by
  have one (ay : ElementaryAction X T × Bool) :
      codeAnswer c ay.1 = ay.2 ↔ (PositiveAnswer (codeSource c) ay.1 ↔ ay.2 = true) := by
    rw [bool_eq_iff_truth_iff, codeAnswer_correct]
  exact ⟨fun hc ay hay => (one ay).mp (hc ay hay), fun hs ay hay => (one ay).mpr (hs ay hay)⟩

abbrev TargetCode (X : Type u) (T : X → Prop) :=
  CombinedVertex X T → CombinedVertex X T → Mark → Mark → Bool

def decodeTarget {X : Type u} {T : X → Prop} (b : TargetCode X T) : MarkedGraph (CombinedVertex X T) where
  edge x y mx my := b x y mx my = true

theorem decodeTarget_injective {X : Type u} {T : X → Prop} :
    Function.Injective (decodeTarget (X := X) (T := T)) := by
  intro a b h
  apply funext; intro x
  apply funext; intro y
  apply funext; intro mx
  apply funext; intro my
  apply (bool_eq_iff_truth_iff _ _).mpr
  change (decodeTarget a).edge x y mx my ↔ (decodeTarget b).edge x y mx my
  rw [h]

def codeTarget {X : Type u} [LinearOrder X] [Fintype X] (T : X → Prop) [DecidablePred T]
    (c : RegistryCode X) : TargetCode X T := by
  letI : Fintype (codeSource c).selections := (codeSource c).selectionFintype
  letI : Fintype (codeSource c).latents := (codeSource c).latentFintype
  letI : DecidableEq (codeSource c).selections := sourceSelectionEq c
  letI : DecidableEq (codeSource c).latents := sourceLatentEq c
  letI : DecidableRel (codeSource c).dag.arrow := sourceArrowDecision c
  exact fun x y mx my => @decide ((tcm (codeSource c).dag T).edge x y mx my)
    (tcmEdgeDecision (codeSource c).dag T x y mx my)

theorem codeTarget_correct {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (c : RegistryCode X) :
    decodeTarget (codeTarget T c) = tcm (codeSource c).dag T := by
  apply markedGraph_eq
  intro x y mx my
  simp only [decodeTarget, codeTarget, decide_eq_true_eq]

/-- Fully finite postprocessing for any history. These are source definitions
only, not a claim that a compiler has accepted or run the procedure. -/
def decodeHistory {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (h : History X T) : Finset (TargetCode X T) :=
  (Finset.univ.filter (fun c : RegistryCode X => CodeConsistent c h)).image (codeTarget T)

/-- Exact whole-history decoder for the full marked target and ORIGINAL
unbounded finite structural-source carrier. Inconsistent branches are covered
too: their right-hand source set is empty. No shared-source or target adapter
is assumed here; both have proof bodies in the imported development. -/
theorem decodeHistory_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (h : History X T) (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ decodeHistory T h, decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SourceConsistent E h ∧ tcm E.dag T = G := by
  constructor
  · rintro ⟨b, hb, hG⟩
    obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hb
    refine ⟨codeSource c, (code_consistent_iff c h).mp (Finset.mem_filter.mp hc).2, ?_⟩
    exact (codeTarget_correct T c).symm.trans ((congrArg decodeTarget hcb).trans hG)
  · rintro ⟨E, hE, hG⟩
    let c := encode (originalProfile E.dag)
    have hsig := codeSource_original_signature T E
    have hc : CodeConsistent c h := (code_consistent_iff c h).mpr
      ((consistent_preserved hsig h).mp hE)
    refine ⟨codeTarget T c, Finset.mem_image.mpr
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩, ?_⟩
    exact (codeTarget_correct T c).trans ((codeSource_original_target T E).symm.trans hG)

theorem decodeHistory_card_bound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (h : History X T) :
    (decodeHistory T h).card ≤ 2 ^ Fintype.card X * 96 ^ ((Fintype.card X).choose 2) := by
  have hi := Finset.card_image_le (s := Finset.univ.filter (fun c : RegistryCode X => CodeConsistent c h))
    (f := codeTarget T)
  have hf := Finset.card_filter_le (Finset.univ : Finset (RegistryCode X)) (fun c => CodeConsistent c h)
  have hle : (decodeHistory T h).card ≤ Fintype.card (RegistryCode X) := hi.trans hf
  exact hle.trans_eq (registry_code_card X)

/-- The outstanding efficient-certificate theorem has exactly this interface.
It is a predicate, NOT an axiom or assumed property of all histories. -/
def CompleteHistory {X : Type u} [DecidableEq X] {T : X → Prop}
    (D : FiniteSource X) (h : History X T) : Prop :=
  ∀ E : FiniteSource X, SourceConsistent E h ↔ SameSetwiseSignature T D E

theorem decode_complete_history {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X) (h : History X T)
    (complete : CompleteHistory D h) (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ decodeHistory T h, decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G := by
  rw [decodeHistory_exact]
  exact ⟨fun ⟨E, hc, ht⟩ => ⟨E, (complete E).mp hc, ht⟩,
    fun ⟨E, hs, ht⟩ => ⟨E, (complete E).mpr hs, ht⟩⟩

end RestrictedCausal.TranscriptDecoder
