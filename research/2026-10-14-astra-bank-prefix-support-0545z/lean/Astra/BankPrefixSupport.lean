import Mathlib.Logic.Function.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Source-only finite bank-prefix argument. This is a finite algebra lemma,
not a supplied source law or physical cardinal bound. An actual-source caller
must derive its single-coordinate difference premise from source providers.
Neither independence of an external configuration PMF nor a fitted mixture is
assumed. Every prefix is a literal bank on the same original site carrier. -/
namespace Astra.BankPrefixSupport

open scoped Classical

variable {Site : Type*} {m : Nat}

/-- All listed sites initially use their smaller arm; unlisted bits stay in
the same supplied background bank. Prefix k switches precisely indices < k. -/
noncomputable def prefixBank (J : Fin m → Site) (low high : Fin m → Bool)
    (background : Site → Bool) (k : Nat) : Site → Bool :=
  Function.extend J (fun i => if i.val < k then high i else low i) background

lemma prefixBank_at (J : Fin m → Site) (hinj : Function.Injective J)
    (low high : Fin m → Bool) (background : Site → Bool) (k : Nat) (i : Fin m) :
    prefixBank J low high background k (J i) =
      if i.val < k then high i else low i :=
  hinj.extend_apply _ _ i

lemma prefixBank_off (J : Fin m → Site) (low high : Fin m → Bool)
    (background : Site → Bool) (k : Nat) (s : Site) (hs : ¬ ∃ i, J i = s) :
    prefixBank J low high background k s = background s :=
  Function.extend_apply' _ _ s hs

/-- Consecutive banks agree at every actual site except J i. -/
lemma successive_agree_off (J : Fin m → Site) (hinj : Function.Injective J)
    (low high : Fin m → Bool) (background : Site → Bool) (i : Fin m) :
    ∀ s, s ≠ J i →
      prefixBank J low high background i.val s =
        prefixBank J low high background (i.val + 1) s := by
  intro s hs
  by_cases hex : ∃ j, J j = s
  · obtain ⟨j, rfl⟩ := hex
    have hji : j ≠ i := fun h => hs (congrArg J h)
    have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
    rw [prefixBank_at J hinj, prefixBank_at J hinj]
    have hlt : (j.val < i.val) ↔ (j.val < i.val + 1) := by omega
    rw [hlt]
  · rw [prefixBank_off J low high background _ s hex,
      prefixBank_off J low high background _ s hex]

noncomputable def lowerBit (arm : Bool → ℝ) : Bool :=
  if arm false ≤ arm true then false else true

noncomputable def upperBit (arm : Bool → ℝ) : Bool := !(lowerBit arm)

lemma lower_lt_upper (arm : Bool → ℝ) (hne : arm false ≠ arm true) :
    arm (lowerBit arm) < arm (upperBit arm) := by
  by_cases hle : arm false ≤ arm true
  · simpa only [lowerBit, upperBit, if_pos hle, Bool.not_false] using
      lt_of_le_of_ne hle hne
  · simpa only [lowerBit, upperBit, if_neg hle, Bool.not_true] using lt_of_not_ge hle

/-- Derive a strict exposure chain from exact one-coordinate differences.
The premise is generic algebra; source applications must instantiate it with
an actual proved bank-flip identity, rather than assume a desired law. -/
theorem actual_prefix_strictMono
    (J : Fin m → Site) (hinj : Function.Injective J)
    (arm : Fin m → Bool → ℝ) (hne : ∀ i, arm i false ≠ arm i true)
    (background : Site → Bool) (f : (Site → Bool) → ℝ)
    (difference : ∀ (i : Fin m) (coin coin' : Site → Bool),
      (∀ s, s ≠ J i → coin s = coin' s) →
      f coin' - f coin = arm i (coin' (J i)) - arm i (coin (J i))) :
    StrictMono (fun k : Fin (m+1) =>
      f (prefixBank J (fun i => lowerBit (arm i))
        (fun i => upperBit (arm i)) background k.val)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hdiff := difference i
    (prefixBank J (fun i => lowerBit (arm i)) (fun i => upperBit (arm i))
      background i.val)
    (prefixBank J (fun i => lowerBit (arm i)) (fun i => upperBit (arm i))
      background (i.val + 1))
    (successive_agree_off J hinj _ _ background i)
  rw [prefixBank_at J hinj, prefixBank_at J hinj] at hdiff
  simp only [Nat.lt_succ_self, if_true, lt_self_iff_false, if_false] at hdiff
  have hp := lower_lt_upper (arm i) (hne i)
  change f (prefixBank J _ _ background i.val) <
    f (prefixBank J _ _ background (i.val+1))
  linarith

/-- m unequal independent bank coordinates yield at least m+1 survival
values in any finite set covering every actual bank's survival. No mass or
support assertion is built into the generic lemma. -/
theorem prefix_survival_card
    (J : Fin m → Site) (hinj : Function.Injective J)
    (arm : Fin m → Bool → ℝ) (hne : ∀ i, arm i false ≠ arm i true)
    (background : Site → Bool) (f : (Site → Bool) → ℝ)
    (difference : ∀ (i : Fin m) (coin coin' : Site → Bool),
      (∀ s, s ≠ J i → coin s = coin' s) →
      f coin' - f coin = arm i (coin' (J i)) - arm i (coin (J i)))
    (A : Finset ℝ) (hA : ∀ coin, Real.exp (-f coin) ∈ A) :
    m + 1 ≤ A.card := by
  have hmono := actual_prefix_strictMono J hinj arm hne background f difference
  let g : Fin (m+1) → A := fun k =>
    ⟨Real.exp (-f (prefixBank J (fun i => lowerBit (arm i))
      (fun i => upperBit (arm i)) background k.val)), hA _⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hval := congrArg Subtype.val hab
    have hexp := Real.exp_injective hval
    apply hmono.injective
    exact neg_injective hexp
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_fin, Fintype.card_coe] using hc

-- Requests for future execution, not actual audit receipts.
#print axioms successive_agree_off
#print axioms lower_lt_upper
#print axioms actual_prefix_strictMono
#print axioms prefix_survival_card

end Astra.BankPrefixSupport
