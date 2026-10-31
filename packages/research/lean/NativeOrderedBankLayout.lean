import Mathlib.Logic.Equiv.Fin.Basic

/-!
Explicit original bank ordering for the existing native row compiler.

The caller supplies occurrence-preserving vertex/edge/hybrid equivalences.
This constructs the shared index layout; it does not acquire or admit a source,
parse a request, interpret a coin or certify an observation law.
-/
namespace Astra.NativeOrderedBankLayout

variable {V E H : Type*} {nv ne nh : ℕ}

/-- All original edges, followed by ONE ancestral population. -/
def populationEquiv (edges : E ≃ Fin ne) : Option E ≃ Fin (ne + 1) :=
  (Equiv.optionCongr edges).trans finSuccEquivLast.symm

/-- Native AGE, edge inverse rates, ancestral inverse rate, then hybrid IDs. -/
def bankEquiv (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) : V ⊕ (Option E ⊕ H) ≃ Fin (nv + ne + 1 + nh) :=
  ((Equiv.sumCongr vertices
      ((Equiv.sumCongr (populationEquiv edges) hybrids).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by simp [Nat.add_assoc]))

@[simp] theorem population_some (edges : E ≃ Fin ne) (e : E) :
    populationEquiv edges (some e) = (edges e).castSucc := by
  simp [populationEquiv]

@[simp] theorem population_none (edges : E ≃ Fin ne) :
    populationEquiv edges none = Fin.last ne := by
  simp [populationEquiv]

@[simp] theorem age_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (v : V) :
    (bankEquiv vertices edges hybrids (.inl v)).val = (vertices v).val := by
  simp [bankEquiv]

@[simp] theorem edge_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (e : E) :
    (bankEquiv vertices edges hybrids (.inr (.inl (some e)))).val =
      nv + (edges e).val := by
  simp [bankEquiv, populationEquiv]

@[simp] theorem ancestral_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) :
    (bankEquiv vertices edges hybrids (.inr (.inl none))).val = nv + ne := by
  simp [bankEquiv, populationEquiv]

@[simp] theorem hybrid_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (h : H) :
    (bankEquiv vertices edges hybrids (.inr (.inr h))).val =
      nv + ne + 1 + (hybrids h).val := by
  simp [bankEquiv, Nat.add_assoc]

/-- No edge or hybrid coordinate can alias the one ancestral slot. -/
theorem ancestral_fiber (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (q : V ⊕ (Option E ⊕ H)) :
    (bankEquiv vertices edges hybrids q).val = nv + ne ↔ q = .inr (.inl none) := by
  constructor
  · intro h
    apply (bankEquiv vertices edges hybrids).injective
    apply Fin.ext
    simpa only [ancestral_index] using h
  · rintro rfl
    exact ancestral_index vertices edges hybrids

/-- Universal coordinate contract, including empty carriers when supplied. -/
theorem ordered_bank_positions (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) :
    (∀ v, (bankEquiv vertices edges hybrids (.inl v)).val = (vertices v).val) ∧
    (∀ e, (bankEquiv vertices edges hybrids (.inr (.inl (some e)))).val =
      nv + (edges e).val) ∧
    (bankEquiv vertices edges hybrids (.inr (.inl none))).val = nv + ne ∧
    (∀ h, (bankEquiv vertices edges hybrids (.inr (.inr h))).val =
      nv + ne + 1 + (hybrids h).val) ∧
    (∀ q, (bankEquiv vertices edges hybrids q).val = nv + ne ↔
      q = .inr (.inl none)) := by
  exact ⟨age_index vertices edges hybrids, edge_index vertices edges hybrids,
    ancestral_index vertices edges hybrids, hybrid_index vertices edges hybrids,
    ancestral_fiber vertices edges hybrids⟩

end Astra.NativeOrderedBankLayout
