import FiniteSelectedMAGDecision

/- Pinned proof compatibility: expose the ORIGINAL total decode constructor
when checking its parent field. No code/profile/decoder definition changes. -/

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Explicit total decoding of the full Boolean profile code. Forbidden virtual
tails are filtered against the singleton F flags. A cyclic directed part is
replaced by the empty observed graph, yielding a valid common-source profile
for EVERY code. Valid encoded profiles are recovered exactly, so this repair
does not omit any original source or change its target. Duplicate entries are
allowed. Computable canonical source labels/order and the optimized query
certificate remain separate obligations.
-/

namespace RestrictedCausal.ExplicitProfile

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection ProfileRegistry
open FiniteGraphDecision

universe u

def pairRead {X : Type u} [LinearOrder X] (f : OrderedPair X → Mark → Mark → Prop)
    (x : X) (mx : Mark) (y : X) (my : Mark) : Prop :=
  if hxy : x < y then f ⟨(x, y), hxy⟩ mx my
  else if hyx : y < x then f ⟨(y, x), hyx⟩ my mx else False

def pairReadDecision {X : Type u} [LinearOrder X]
    (f : OrderedPair X → Mark → Mark → Prop)
    (hf : ∀ p mx my, Decidable (f p mx my)) (x : X) (mx : Mark) (y : X) (my : Mark) :
    Decidable (pairRead f x mx y my) := by
  by_cases hxy : x < y
  · simpa only [pairRead, dif_pos hxy] using hf ⟨(x, y), hxy⟩ mx my
  · by_cases hyx : y < x
    · simpa only [pairRead, dif_neg hxy, dif_pos hyx] using hf ⟨(y, x), hyx⟩ my mx
    · simpa only [pairRead, dif_neg hxy, dif_neg hyx] using (isFalse id : Decidable False)

theorem pairRead_self {X : Type u} [LinearOrder X]
    (f : OrderedPair X → Mark → Mark → Prop) (x : X) (mx my : Mark) :
    ¬ pairRead f x mx x my := by
  simp [pairRead]

theorem pairRead_reverse {X : Type u} [LinearOrder X]
    (f : OrderedPair X → Mark → Mark → Prop) (x : X) (mx : Mark) (y : X) (my : Mark) :
    pairRead f x mx y my ↔ pairRead f y my x mx := by
  by_cases heq : x = y
  · subst y
    simp [pairRead]
  · rcases lt_or_gt_of_ne heq with hxy | hyx
    · have hn : ¬ y < x := fun h => lt_asymm hxy h
      simp only [pairRead, dif_pos hxy, dif_neg hn]
    · have hn : ¬ x < y := fun h => lt_asymm hyx h
      simp only [pairRead, dif_neg hn, dif_pos hyx]

/-- Recover an arbitrary symmetric, irreflexive marked relation from its
ordered-pair restriction. All tail/head combinations remain explicit. -/
theorem pairRead_recovers {X : Type u} [LinearOrder X]
    (f : OrderedPair X → Mark → Mark → Prop) (R : X → Mark → X → Mark → Prop)
    (hsymm : ∀ x mx y my, R x mx y my → R y my x mx)
    (hdiag : ∀ x mx my, ¬ R x mx x my)
    (hpair : ∀ p mx my, f p mx my ↔ R p.val.1 mx p.val.2 my)
    (x : X) (mx : Mark) (y : X) (my : Mark) : pairRead f x mx y my ↔ R x mx y my := by
  by_cases heq : x = y
  · subst y
    exact ⟨fun h => (pairRead_self f x mx my h).elim, fun h => (hdiag x mx my h).elim⟩
  · rcases lt_or_gt_of_ne heq with hxy | hyx
    · simpa only [pairRead, dif_pos hxy] using hpair ⟨(x, y), hxy⟩ mx my
    · have hn : ¬ x < y := fun h => lt_asymm hyx h
      have hp := hpair ⟨(y, x), hyx⟩ my mx
      have hr : R y my x mx ↔ R x mx y my :=
        ⟨hsymm y my x mx, hsymm x mx y my⟩
      simpa only [pairRead, dif_neg hn, dif_pos hyx] using hp.trans hr

def orderedEdge {X : Type u} [LinearOrder X] (c : RegistryCode X)
    (p : OrderedPair X) : Mark → Mark → Prop
  | .tail, .tail => False
  | .tail, .head => (c.2 p).1.1 = .forward
  | .head, .tail => (c.2 p).1.1 = .backward
  | .head, .head => (c.2 p).1.2 = true

def orderedEdgeDecision {X : Type u} [LinearOrder X] (c : RegistryCode X)
    (p : OrderedPair X) (mx my : Mark) : Decidable (orderedEdge c p mx my) := by
  cases mx <;> cases my <;> unfold orderedEdge <;> infer_instance

def rawObserved {X : Type u} [LinearOrder X] (c : RegistryCode X) : MarkedGraph X where
  edge x y mx my := pairRead (orderedEdge c) x mx y my

def rawEdgeDecision {X : Type u} [LinearOrder X] (c : RegistryCode X)
    (x y : X) (mx my : Mark) : Decidable ((rawObserved c).edge x y mx my) :=
  pairReadDecision (orderedEdge c) (orderedEdgeDecision c) x mx y my

theorem raw_mixed_laws {X : Type u} [LinearOrder X] (c : RegistryCode X) : MixedLaws (rawObserved c) where
  symmetric := fun x y mx my h => (pairRead_reverse (orderedEdge c) x mx y my).mp h
  irreflexive := pairRead_self (orderedEdge c)
  no_tail_tail := by
    intro x y h
    have hn : ¬ (rawObserved c).edge x y .tail .tail := by
      simp [rawObserved, pairRead, orderedEdge]
    exact hn h

theorem orderedEdge_encode {X : Type u} [LinearOrder X] (Q : AdmissibleProfile X)
    (p : OrderedPair X) (mx my : Mark) :
    orderedEdge (encode Q) p mx my ↔ Q.val.observed.edge p.val.1 p.val.2 mx my := by
  classical
  cases mx with
  | tail =>
      cases my with
      | tail => exact ⟨False.elim, fun h => (Q.property.1.no_tail_tail _ _ h).elim⟩
      | head => exact direction_forward Q.val.observed p.val.1 p.val.2
  | head =>
      cases my with
      | head => simp [orderedEdge, encode]
      | tail =>
          have h := direction_backward Q.val.observed Q.property.2 p.val.1 p.val.2
          exact h.trans ⟨Q.property.1.symmetric _ _ .tail .head,
            Q.property.1.symmetric _ _ .head .tail⟩

theorem rawObserved_encode {X : Type u} [LinearOrder X] (Q : AdmissibleProfile X) :
    rawObserved (encode Q) = Q.val.observed := by
  apply markedGraph_eq
  intro x y mx my
  exact pairRead_recovers (orderedEdge (encode Q))
    (fun x mx y my => Q.val.observed.edge x y mx my)
    (fun x mx y my => Q.property.1.symmetric x y mx my)
    Q.property.1.irreflexive (orderedEdge_encode Q) x mx y my

def EdgeCycleFree {V : Type u} (G : MarkedGraph V) : Prop :=
  ∀ x y, Directed G x y → ¬ Reach G y x

theorem edgeCycleFree_iff {V : Type u} (G : MarkedGraph V) : EdgeCycleFree G ↔ DirectedAcyclic G := by
  constructor
  · intro h x xs hp
    cases hp with
    | nil => rfl
    | cons hedge htail => exact (h _ _ hedge ⟨_, htail⟩).elim
  · intro h x y hedge
    rintro ⟨xs, hp⟩
    have hnil := h x (y :: xs) (.cons hedge hp)
    cases hnil

def cycleFreeDecision {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) :
    Decidable (EdgeCycleFree (rawObserved c)) := by
  letI : DecidableRel (Directed (rawObserved c)) := fun x y => rawEdgeDecision c x y .tail .head
  letI : DecidableRel (Reach (rawObserved c)) := reachDecision (rawObserved c) (rawEdgeDecision c)
  unfold EdgeCycleFree
  infer_instance

def emptyObserved (X : Type u) : MarkedGraph X := ⟨fun _ _ _ _ => False⟩

theorem empty_mixed_laws (X : Type u) : MixedLaws (emptyObserved X) :=
  ⟨fun _ _ _ _ h => h.elim, fun _ _ _ => id, fun _ _ => id⟩

theorem empty_acyclic (X : Type u) : DirectedAcyclic (emptyObserved X) := by
  intro x xs hp
  cases hp with
  | nil => rfl
  | cons hedge _ => exact hedge.elim

def decodedObserved {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) : MarkedGraph X :=
  letI : Decidable (EdgeCycleFree (rawObserved c)) := cycleFreeDecision c
  if EdgeCycleFree (rawObserved c) then rawObserved c else emptyObserved X

theorem decoded_observed_valid {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) :
    MixedLaws (decodedObserved c) ∧ DirectedAcyclic (decodedObserved c) := by
  by_cases h : EdgeCycleFree (rawObserved c)
  · simpa only [decodedObserved, if_pos h, dif_pos h] using
      And.intro (raw_mixed_laws c) ((edgeCycleFree_iff _).mp h)
  · simpa only [decodedObserved, if_neg h, dif_neg h] using And.intro (empty_mixed_laws X) (empty_acyclic X)

theorem decodedObserved_encode {X : Type u} [LinearOrder X] [Fintype X] (Q : AdmissibleProfile X) :
    decodedObserved (encode Q) = Q.val.observed := by
  have hraw := rawObserved_encode Q
  have hcycle : EdgeCycleFree (rawObserved (encode Q)) :=
    (edgeCycleFree_iff _).mpr (by simpa only [hraw] using Q.property.2)
  simp only [decodedObserved, if_pos hcycle, dif_pos hcycle, hraw]

def rawBridge {X : Type u} [LinearOrder X] (c : RegistryCode X) : X → Mark → X → Mark → Prop :=
  pairRead (fun p mx my => (c.2 p).2 (mx, my) = true)

def decodedBridge {X : Type u} [LinearOrder X] (c : RegistryCode X)
    (x : X) (mx : Mark) (y : X) (my : Mark) : Prop :=
  rawBridge c x mx y my ∧ (mx = .tail → c.1 x = true) ∧ (my = .tail → c.1 y = true)

def decodedProfile {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) : Profile X where
  observed := decodedObserved c
  parent x := c.1 x = true
  bridge := decodedBridge c
  bridge_ne := by
    rintro x mx y my ⟨hr, _⟩ heq
    subst y
    exact pairRead_self _ x mx my hr
  bridge_symm := by
    rintro x mx y my ⟨hr, hx, hy⟩
    exact ⟨(pairRead_reverse _ x mx y my).mp hr, hy, hx⟩
  bridge_tails := fun h => h.2

def decode {X : Type u} [LinearOrder X] [Fintype X] (c : RegistryCode X) : AdmissibleProfile X :=
  ⟨decodedProfile c, (decoded_observed_valid c).1, (decoded_observed_valid c).2⟩

theorem rawBridge_encode {X : Type u} [LinearOrder X] (Q : AdmissibleProfile X)
    (x : X) (mx : Mark) (y : X) (my : Mark) : rawBridge (encode Q) x mx y my ↔ Q.val.bridge x mx y my := by
  classical
  apply pairRead_recovers _ Q.val.bridge
  · exact fun _ _ _ _ h => Q.val.bridge_symm h
  · exact fun _ _ _ h => Q.val.bridge_ne h rfl
  · intro p m n
    simp [encode]

/-- Exact recovery includes singleton flags, all marked bridge choices,
bow-preserving observed edges, and the actual acyclicity restriction. -/
theorem decode_encode {X : Type u} [LinearOrder X] [Fintype X] (Q : AdmissibleProfile X) :
    decode (encode Q) = Q := by
  classical
  apply Subtype.ext
  apply profile_eq (decodedObserved_encode Q)
  · exact funext fun x => propext (by simp [decode, decodedProfile, encode])
  · apply funext; intro x
    apply funext; intro mx
    apply funext; intro y
    apply funext; intro my
    apply propext
    constructor
    · intro h
      exact (rawBridge_encode Q x mx y my).mp h.1
    · intro h
      refine ⟨(rawBridge_encode Q x mx y my).mpr h, ?_, ?_⟩
      · intro htail
        simpa [encode] using (Q.val.bridge_tails h).1 htail
      · intro htail
        simpa [encode] using (Q.val.bridge_tails h).2 htail

theorem decode_surjective {X : Type u} [LinearOrder X] [Fintype X] :
    Function.Surjective (decode (X := X)) := fun Q => ⟨encode Q, decode_encode Q⟩

end RestrictedCausal.ExplicitProfile

namespace RestrictedCausal.FiniteTargetImage

open SelectedWalk CanonicalSelection OriginalProjection ProfileRegistry HPLTarget ExplicitProfile

universe u

/-- Code enumeration no longer enumerates arbitrary Prop-valued profiles via
`Fintype.ofInjective`. This definition is still marked noncomputable because
the present canonical source labels/order and full-signature filter have not
yet been replaced by their explicit finite Boolean implementations. -/
noncomputable def codedRegistryList {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) : Finset (MarkedGraph (CombinedVertex X T)) := by
  classical
  exact (Finset.univ.filter (fun c : RegistryCode X => SameElementarySignature T D (registrySource (decode c)))).image
    (fun c => tcm (registrySource (decode c)).dag T)

theorem codedRegistryList_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) (G : MarkedGraph (CombinedVertex X T)) :
    G ∈ codedRegistryList T D ↔ ∃ E : FiniteSource X,
      SameSetwiseSignature T D E ∧ tcm E.dag T = G := by
  classical
  constructor
  · intro h
    obtain ⟨c, hc, htarget⟩ := Finset.mem_image.mp h
    exact ⟨registrySource (decode c), (Finset.mem_filter.mp hc).2.setwise, htarget⟩
  · rintro ⟨E, hsig, htarget⟩
    apply Finset.mem_image.mpr
    refine ⟨encode (originalProfile E.dag), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [decode_encode]
      exact hsig.elementary.trans (original_registry_signature T E)
    · rw [decode_encode]
      exact (original_registry_target T E).symm.trans htarget

theorem codedRegistryList_card_bound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) :
    (codedRegistryList T D).card ≤ 2 ^ Fintype.card X * 96 ^ ((Fintype.card X).choose 2) := by
  classical
  have himage := Finset.card_image_le (s := Finset.univ.filter
    (fun c : RegistryCode X => SameElementarySignature T D (registrySource (decode c))))
    (f := fun c => tcm (registrySource (decode c)).dag T)
  have hfilter := Finset.card_filter_le (Finset.univ : Finset (RegistryCode X))
    (fun c => SameElementarySignature T D (registrySource (decode c)))
  have hle : (codedRegistryList T D).card ≤ Fintype.card (RegistryCode X) := himage.trans hfilter
  exact hle.trans_eq (registry_code_card X)

end RestrictedCausal.FiniteTargetImage
