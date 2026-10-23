import RestrictedBudgetAndHonesty
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Effective coordinate enumeration from the declared finite observed-label
order. Boolean subset functions are encoded by their complete bit word on
that sorted label list; injectivity is proved. Explicit lexicographic keys
then order all three query index types, and actual merge-sort enumeration
replaces the earlier mathematical Finset.toList choice.

No Classical.choose, Fintype.equivFin, ofInjective, noncomputable definition
or graph-oracle evaluation is used in these enumeration definitions. This
does not by itself construct or certify the interactive G7 strategy.
-/

namespace RestrictedCausal.PartialQueries

universe u v

def sortedEnumeration (I : Type u) [LinearOrder I] [Fintype I] : Enumeration I where
  items := (Finset.univ : Finset I).sort (· ≤ ·)
  complete i := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_univ i)
  nodup := Finset.sort_nodup _ _
  length := by rw [Finset.length_sort]; rfl

theorem map_eq_on_members {I : Type u} {J : Type v} (items : List I) (f g : I → J)
    (same : items.map f = items.map g) : ∀ x ∈ items, f x = g x := by
  induction items with
  | nil => intro x member; cases member
  | cons «first» rest ih =>
      have heads := List.cons.inj same
      intro x member
      rcases List.mem_cons.mp member with label | later
      · simpa only [label] using heads.1
      · exact ih heads.2 x later

def bitNat : Bool → Nat
  | false => 0
  | true => 1

theorem bitNat_injective : Function.Injective bitNat := by
  intro a b same
  cases a <;> cases b <;> simp [bitNat] at same ⊢

def extendSubsetBits {X : Type u} (P : X → Prop) [DecidablePred P]
    (bits : {x : X // P x} → Bool) (x : X) : Bool :=
  if member : P x then bits ⟨x, member⟩ else false

def subsetWord {X : Type u} [LinearOrder X] [Fintype X]
    (P : X → Prop) [DecidablePred P] (bits : {x : X // P x} → Bool) : List Nat :=
  (sortedEnumeration X).items.map (fun x => bitNat (extendSubsetBits P bits x))

theorem subsetWord_injective {X : Type u} [LinearOrder X] [Fintype X]
    (P : X → Prop) [DecidablePred P] : Function.Injective (subsetWord P) := by
  intro bits other same
  funext z
  have atZ := map_eq_on_members (sortedEnumeration X).items
    (fun x => bitNat (extendSubsetBits P bits x))
    (fun x => bitNat (extendSubsetBits P other x)) same z.val
    ((sortedEnumeration X).complete z.val)
  have values := bitNat_injective atZ
  simpa only [extendSubsetBits, dif_pos z.property] using values

abbrev PairKey (X : Type u) := X ×ₗ X
abbrev QueryKey (X : Type u) := X ×ₗ (X ×ₗ List Nat)

def marginalKey {X : Type u} (T : X → Prop) (q : MarginalIndex T) : PairKey X :=
  toLex (q.val.1.val, q.val.2)

theorem marginalKey_injective {X : Type u} (T : X → Prop) :
    Function.Injective (marginalKey T) := by
  intro a b same
  have «first» := congrArg (fun p : PairKey X => (ofLex p).1) same
  have second := congrArg (fun p : PairKey X => (ofLex p).2) same
  rcases a with ⟨⟨⟨a, availableA⟩, x⟩, distinctA⟩
  rcases b with ⟨⟨⟨b, availableB⟩, y⟩, distinctB⟩
  change a = b at «first»
  change x = y at second
  subst b
  subst y
  rfl

def observedKey {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (q : ObservedIndex T) : QueryKey X :=
  toLex (q.1.val.1, toLex (q.1.val.2,
    subsetWord (fun z => ¬ T z ∧ z ≠ q.1.val.1 ∧ z ≠ q.1.val.2) q.2))

theorem observedKey_injective {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : Function.Injective (observedKey T) := by
  intro a b same
  have «first» := congrArg (fun p : QueryKey X => (ofLex p).1) same
  have second := congrArg (fun p : QueryKey X => (ofLex (ofLex p).2).1) same
  have word := congrArg (fun p : QueryKey X => (ofLex (ofLex p).2).2) same
  rcases a with ⟨⟨⟨a, x⟩, orderedA⟩, bits⟩
  rcases b with ⟨⟨⟨b, y⟩, orderedB⟩, other⟩
  change a = b at «first»
  change x = y at second
  subst b
  subst y
  have equalBits : bits = other :=
    subsetWord_injective (fun z => ¬ T z ∧ z ≠ a ∧ z ≠ x) word
  subst other
  rfl

def conditionalKey {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (q : ConditionalIndex T) : QueryKey X :=
  toLex (q.1.val.1.val, toLex (q.1.val.2,
    subsetWord (fun z => ¬ T z ∧ z ≠ q.1.val.2) q.2))

theorem conditionalKey_injective {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : Function.Injective (conditionalKey T) := by
  intro a b same
  have «first» := congrArg (fun p : QueryKey X => (ofLex p).1) same
  have second := congrArg (fun p : QueryKey X => (ofLex (ofLex p).2).1) same
  have word := congrArg (fun p : QueryKey X => (ofLex (ofLex p).2).2) same
  rcases a with ⟨⟨⟨⟨a, availableA⟩, x⟩, distinctA⟩, bits⟩
  rcases b with ⟨⟨⟨⟨b, availableB⟩, y⟩, distinctB⟩, other⟩
  change a = b at «first»
  change x = y at second
  subst b
  subst y
  have equalBits : bits = other := subsetWord_injective (fun z => ¬ T z ∧ z ≠ x) word
  subst other
  rfl

def marginalIndexOrder {X : Type u} [LinearOrder X] (T : X → Prop) : LinearOrder (MarginalIndex T) :=
  LinearOrder.lift' (marginalKey T) (marginalKey_injective T)

def observedIndexOrder {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : LinearOrder (ObservedIndex T) :=
  LinearOrder.lift' (observedKey T) (observedKey_injective T)

def conditionalIndexOrder {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : LinearOrder (ConditionalIndex T) :=
  LinearOrder.lift' (conditionalKey T) (conditionalKey_injective T)

def effectiveMarginalEnumeration {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : Enumeration (MarginalIndex T) := by
  letI : LinearOrder (MarginalIndex T) := marginalIndexOrder T
  exact sortedEnumeration _

def effectiveObservedEnumeration {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : Enumeration (ObservedIndex T) := by
  letI : LinearOrder (ObservedIndex T) := observedIndexOrder T
  exact sortedEnumeration _

def effectiveConditionalEnumeration {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : Enumeration (ConditionalIndex T) := by
  letI : LinearOrder (ConditionalIndex T) := conditionalIndexOrder T
  exact sortedEnumeration _

end RestrictedCausal.PartialQueries
