import CanonicalFiniteBounds
import Mathlib.Data.Fintype.BigOperators

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
An injective finite code for full H_X/F/V profiles with acyclic bow-aware H_X.
This is a registry-cardinality component, not the original-source decoder or
an assertion that an arbitrary family of indicator MAGs is jointly realizable.
-/

namespace RestrictedCausal.ProfileRegistry

open SelectedWalk CanonicalSelection LatentRoots

universe u

inductive DirectionChoice
  | absent
  | forward
  | backward
  deriving DecidableEq

instance : Fintype DirectionChoice where
  elems := {.absent, .forward, .backward}
  complete := by intro d; cases d <;> simp

theorem card_directionChoice : Fintype.card DirectionChoice = 3 := rfl

noncomputable def direction {X : Type u} (G : MarkedGraph X) (x y : X) :
    DirectionChoice := by
  classical
  exact if Directed G x y then .forward else if Directed G y x then .backward else .absent

theorem no_directed_pair {X : Type u} {G : MarkedGraph X} (hG : DirectedAcyclic G)
    (x y : X) (hxy : Directed G x y) : ¬ Directed G y x := by
  intro hyx
  have hbad := hG x [y, x] (.cons hxy (.cons hyx (.nil x)))
  cases hbad

theorem direction_forward {X : Type u} (G : MarkedGraph X) (x y : X) :
    direction G x y = .forward ↔ Directed G x y := by
  classical
  by_cases hxy : Directed G x y
  · simp [direction, hxy]
  · by_cases hyx : Directed G y x <;> simp [direction, hxy, hyx]

theorem direction_backward {X : Type u} (G : MarkedGraph X)
    (hG : DirectedAcyclic G) (x y : X) :
    direction G x y = .backward ↔ Directed G y x := by
  classical
  by_cases hxy : Directed G x y
  · have hyx := no_directed_pair hG x y hxy
    simp [direction, hxy, hyx]
  · by_cases hyx : Directed G y x <;> simp [direction, hxy, hyx]

theorem recover_pair {X : Type u} (G K : MarkedGraph X)
    (lawsG : MixedLaws G) (lawsK : MixedLaws K)
    (acycG : DirectedAcyclic G) (acycK : DirectedAcyclic K)
    (x y : X) (hd : direction G x y = direction K x y)
    (hb : G.edge x y .head .head ↔ K.edge x y .head .head)
    (mx my : Mark) : G.edge x y mx my ↔ K.edge x y mx my := by
  cases mx with
  | tail =>
      cases my with
      | tail => exact ⟨fun h => (lawsG.no_tail_tail x y h).elim,
          fun h => (lawsK.no_tail_tail x y h).elim⟩
      | head =>
          change Directed G x y ↔ Directed K x y
          rw [← direction_forward G x y, ← direction_forward K x y, hd]
  | head =>
      cases my with
      | head => exact hb
      | tail =>
          have hg : G.edge x y .head .tail ↔ Directed G y x :=
            ⟨lawsG.symmetric x y .head .tail, lawsG.symmetric y x .tail .head⟩
          have hk : K.edge x y .head .tail ↔ Directed K y x :=
            ⟨lawsK.symmetric x y .head .tail, lawsK.symmetric y x .tail .head⟩
          rw [hg, hk, ← direction_backward G acycG x y,
            ← direction_backward K acycK x y, hd]

abbrev AdmissibleProfile (X : Type u) :=
  {Q : Profile X // MixedLaws Q.observed ∧ DirectedAcyclic Q.observed}

/-- Two bits of data are not confused: F has one bit per variable, while V has
four independent incidence-mark bits per ordered distinct pair. The observed
graph has three directional statuses and one independent confounding bit. -/
abbrev RegistryCode (X : Type u) [LinearOrder X] :=
  (X → Bool) × (OrderedPair X → (DirectionChoice × Bool) × (Mark × Mark → Bool))

noncomputable def encode {X : Type u} [LinearOrder X] (Q : AdmissibleProfile X) :
    RegistryCode X := by
  classical
  exact (fun x => decide (Q.val.parent x), fun p =>
    ((direction Q.val.observed p.val.1 p.val.2,
      decide (Q.val.observed.edge p.val.1 p.val.2 .head .head)),
      fun m => decide (Q.val.bridge p.val.1 m.1 p.val.2 m.2)))

theorem encode_parent {X : Type u} [LinearOrder X]
    {Q R : AdmissibleProfile X} (h : encode Q = encode R) (x : X) :
    Q.val.parent x ↔ R.val.parent x := by
  classical
  exact decide_eq_decide.mp (congrArg (fun c : RegistryCode X => c.1 x) h)

theorem encode_ordered_bridge {X : Type u} [LinearOrder X]
    {Q R : AdmissibleProfile X} (h : encode Q = encode R)
    (x y : X) (hxy : x < y) (mx my : Mark) :
    Q.val.bridge x mx y my ↔ R.val.bridge x mx y my := by
  classical
  exact decide_eq_decide.mp
    (congrArg (fun c : RegistryCode X => (c.2 ⟨(x, y), hxy⟩).2 (mx, my)) h)

theorem encode_bridge {X : Type u} [LinearOrder X]
    {Q R : AdmissibleProfile X} (h : encode Q = encode R)
    (x y : X) (mx my : Mark) : Q.val.bridge x mx y my ↔ R.val.bridge x mx y my := by
  by_cases heq : x = y
  · subst y
    exact ⟨fun hb => (Q.val.bridge_ne hb rfl).elim,
      fun hb => (R.val.bridge_ne hb rfl).elim⟩
  · rcases lt_or_gt_of_ne heq with hxy | hyx
    · exact encode_ordered_bridge h x y hxy mx my
    · have hrev := encode_ordered_bridge h y x hyx my mx
      exact ⟨fun hb => R.val.bridge_symm (hrev.mp (Q.val.bridge_symm hb)),
        fun hb => Q.val.bridge_symm (hrev.mpr (R.val.bridge_symm hb))⟩

theorem encode_ordered_edge {X : Type u} [LinearOrder X]
    {Q R : AdmissibleProfile X} (h : encode Q = encode R)
    (x y : X) (hxy : x < y) (mx my : Mark) :
    Q.val.observed.edge x y mx my ↔ R.val.observed.edge x y mx my := by
  classical
  have hd := congrArg (fun c : RegistryCode X => (c.2 ⟨(x, y), hxy⟩).1.1) h
  have hb := congrArg (fun c : RegistryCode X => (c.2 ⟨(x, y), hxy⟩).1.2) h
  exact recover_pair Q.val.observed R.val.observed Q.property.1 R.property.1
    Q.property.2 R.property.2 x y hd (decide_eq_decide.mp hb) mx my

theorem encode_edge {X : Type u} [LinearOrder X]
    {Q R : AdmissibleProfile X} (h : encode Q = encode R)
    (x y : X) (mx my : Mark) :
    Q.val.observed.edge x y mx my ↔ R.val.observed.edge x y mx my := by
  by_cases heq : x = y
  · subst y
    exact ⟨fun he => (Q.property.1.irreflexive x mx my he).elim,
      fun he => (R.property.1.irreflexive x mx my he).elim⟩
  · rcases lt_or_gt_of_ne heq with hxy | hyx
    · exact encode_ordered_edge h x y hxy mx my
    · have hrev := encode_ordered_edge h y x hyx my mx
      exact ⟨fun he => R.property.1.symmetric y x my mx
          (hrev.mp (Q.property.1.symmetric x y mx my he)),
        fun he => Q.property.1.symmetric y x my mx
          (hrev.mpr (R.property.1.symmetric x y mx my he))⟩

theorem markedGraph_eq {X : Type u} {G K : MarkedGraph X}
    (h : ∀ x y mx my, G.edge x y mx my ↔ K.edge x y mx my) : G = K := by
  have he : G.edge = K.edge := funext fun x => funext fun y =>
    funext fun mx => funext fun my => propext (h x y mx my)
  cases G
  cases K
  cases he
  rfl

theorem profile_eq {X : Type u} {Q R : Profile X}
    (ho : Q.observed = R.observed) (hf : Q.parent = R.parent)
    (hv : Q.bridge = R.bridge) : Q = R := by
  cases Q
  cases R
  cases ho
  cases hf
  cases hv
  rfl

theorem encode_injective {X : Type u} [LinearOrder X] :
    Function.Injective (encode (X := X)) := by
  intro Q R h
  apply Subtype.ext
  apply profile_eq (markedGraph_eq (encode_edge h))
  · exact funext fun x => propext (encode_parent h x)
  · exact funext fun x => funext fun mx => funext fun y => funext fun my =>
      propext (encode_bridge h x y mx my)

noncomputable instance admissibleProfileFintype (X : Type u)
    [LinearOrder X] [Fintype X] : Fintype (AdmissibleProfile X) := by
  classical
  exact Fintype.ofInjective encode encode_injective

theorem registry_code_card (X : Type u) [LinearOrder X] [Fintype X] :
    Fintype.card (RegistryCode X) =
      2 ^ Fintype.card X * 96 ^ ((Fintype.card X).choose 2) := by
  classical
  simp only [RegistryCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, card_directionChoice, card_mark, card_orderedPair]

/-- Exact finite registry bound for the complete marked profile. No raw SG,
RG, skeleton or collection of independently realizable indicator classes is
substituted. Acyclicity only filters codes and cannot increase this count. -/
theorem admissible_profile_card_bound (X : Type u) [LinearOrder X] [Fintype X] :
    Fintype.card (AdmissibleProfile X) ≤
      2 ^ Fintype.card X * 96 ^ ((Fintype.card X).choose 2) := by
  have h := Fintype.card_le_of_injective (encode (X := X)) encode_injective
  exact h.trans_eq (registry_code_card X)

end RestrictedCausal.ProfileRegistry
