import Std

namespace SocialScience.Identifiability

/-- A design is the set of probes whose outputs can be observed. -/
def Equivalent {Θ X Y : Type} (predict : Θ → X → Y) (design : X → Prop)
    (θ φ : Θ) : Prop := ∀ x, design x → predict θ x = predict φ x

/-- Structural identifiability, with exact outputs rather than noisy samples. -/
def Identified {Θ X Y : Type} (predict : Θ → X → Y) (design : X → Prop) : Prop :=
  ∀ θ φ, Equivalent predict design θ φ → θ = φ

theorem equivalent_refl {Θ X Y : Type} (predict : Θ → X → Y)
    (design : X → Prop) (θ : Θ) : Equivalent predict design θ θ :=
  fun _ _ => rfl

theorem equivalent_symm {Θ X Y : Type} {predict : Θ → X → Y}
    {design : X → Prop} {θ φ : Θ} (h : Equivalent predict design θ φ) :
    Equivalent predict design φ θ := fun x hx => (h x hx).symm

theorem equivalent_trans {Θ X Y : Type} {predict : Θ → X → Y}
    {design : X → Prop} {θ φ ψ : Θ}
    (h : Equivalent predict design θ φ) (g : Equivalent predict design φ ψ) :
    Equivalent predict design θ ψ := fun x hx => (h x hx).trans (g x hx)

theorem restrict_design {Θ X Y : Type} {predict : Θ → X → Y}
    {small large : X → Prop} {θ φ : Θ}
    (included : ∀ x, small x → large x) (h : Equivalent predict large θ φ) :
    Equivalent predict small θ φ := fun x hx => h x (included x hx)

theorem more_probes_preserve_identification {Θ X Y : Type} {predict : Θ → X → Y}
    {small large : X → Prop} (included : ∀ x, small x → large x)
    (h : Identified predict small) : Identified predict large :=
  fun θ φ g => h θ φ (restrict_design included g)

/-- Transforming indistinguishable outputs cannot make them distinguishable. -/
theorem postprocess_preserves_equivalence {Θ X Y Z : Type}
    {predict : Θ → X → Y} {design : X → Prop} {θ φ : Θ}
    (transform : Y → Z) (h : Equivalent predict design θ φ) :
    Equivalent (fun p x => transform (predict p x)) design θ φ :=
  fun x hx => congrArg transform (h x hx)

/-- The baseline probe observes a sum; the second probe isolates one component. -/
def twoComponent (θ : Int × Int) (probe : Bool) : Int :=
  if probe then θ.1 else θ.1 + θ.2

theorem baseline_ambiguous :
    Equivalent twoComponent (fun probe => probe = false) (1, 0) (0, 1) := by
  intro probe h
  subst probe
  decide

theorem baseline_not_identified :
    ¬ Identified twoComponent (fun probe => probe = false) := by
  intro h
  have bad := congrArg Prod.fst (h (1, 0) (0, 1) baseline_ambiguous)
  have : (1 : Int) = 0 := bad
  omega

theorem both_probes_identify : Identified twoComponent (fun _ => True) := by
  intro θ φ h
  have first := h true trivial
  have total := h false trivial
  simp [twoComponent] at first total
  apply Prod.ext
  · exact first
  · omega

end SocialScience.Identifiability
