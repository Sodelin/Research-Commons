import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
The first/last occurrence part of the OLD contiguous multicopy theorem.
These are actual finite physical-tip positions, with the cyclic cut chosen
at a block boundary. No graph/plane-contour/restriction equality is assumed
or proved here. Connecting those existing tree interfaces remains separate.
-/

namespace ResearchCommons.NANUQ.ContiguousCopies

universe u

variable {Taxon : Type u} {m : Nat}

def First (taxon : Fin m → Taxon) (i : Fin m) : Prop :=
  ∀ j, taxon j = taxon i → i ≤ j

def Last (taxon : Fin m → Taxon) (i : Fin m) : Prop :=
  ∀ j, taxon j = taxon i → j ≤ i

def Extreme (taxon : Fin m → Taxon) (i : Fin m) : Prop :=
  First taxon i ∨ Last taxon i

def Contiguous (taxon : Fin m → Taxon) : Prop :=
  ∀ i j k, i ≤ j → j ≤ k → taxon i = taxon k → taxon j = taxon i

def InInterval (l r i : Fin m) : Prop := l ≤ i ∧ i ≤ r

/-- Every actual occurrence has the first and last actual occurrence of its
same taxon, bracketing it. No nonempty assumption for unused labels. -/
theorem extreme_bounds (taxon : Fin m → Taxon) (i : Fin m) :
    ∃ f g, taxon f = taxon i ∧ taxon g = taxon i ∧
      First taxon f ∧ Last taxon g ∧ f ≤ i ∧ i ≤ g := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun j => taxon j = taxon i)
  have hi : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hs : s.Nonempty := ⟨i, hi⟩
  let f := s.min' hs
  let g := s.max' hs
  have hf : taxon f = taxon i :=
    (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hg : taxon g = taxon i :=
    (Finset.mem_filter.mp (s.max'_mem hs)).2
  refine ⟨f, g, hf, hg, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact s.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.trans hf⟩)
  · intro j hj
    exact s.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.trans hg⟩)
  · exact s.min'_le i hi
  · exact s.le_max' i hi

/-- For a contour interval containing two taxon labels, every physical tip
has a retained extreme of its SAME taxon on the SAME side of that interval.
The statement does not assume a desired split or quartet law. -/
theorem same_interval_side_extreme (taxon : Fin m → Taxon)
    (hcont : Contiguous taxon) (l r : Fin m)
    (hrich : ∃ a b, InInterval l r a ∧ InInterval l r b ∧ taxon a ≠ taxon b)
    (i : Fin m) :
    ∃ e, Extreme taxon e ∧ taxon e = taxon i ∧
      (InInterval l r e ↔ InInterval l r i) := by
  obtain ⟨f, g, hf, hg, hfirst, hlast, hfi, hig⟩ := extreme_bounds taxon i
  by_cases hli : l ≤ i
  · by_cases hir : i ≤ r
    · by_cases hlf : l ≤ f
      · refine ⟨f, Or.inl hfirst, hf, ?_⟩
        exact ⟨fun _ => ⟨hli, hir⟩, fun _ => ⟨hlf, hfi.trans hir⟩⟩
      · by_cases hgr : g ≤ r
        · refine ⟨g, Or.inr hlast, hg, ?_⟩
          exact ⟨fun _ => ⟨hli, hir⟩, fun _ => ⟨hli.trans hig, hgr⟩⟩
        · obtain ⟨a, b, ha, hb, hab⟩ := hrich
          have hfl : f ≤ l := le_of_lt (lt_of_not_ge hlf)
          have hrg : r ≤ g := le_of_lt (lt_of_not_ge hgr)
          have hfg : taxon f = taxon g := hf.trans hg.symm
          have hta := hcont f a g (hfl.trans ha.1) (ha.2.trans hrg) hfg
          have htb := hcont f b g (hfl.trans hb.1) (hb.2.trans hrg) hfg
          exact (hab (hta.trans htb.symm)).elim
    · refine ⟨g, Or.inr hlast, hg, ?_⟩
      constructor
      · intro he
        exact (hir (hig.trans he.2)).elim
      · intro hi
        exact (hir hi.2).elim
  · refine ⟨f, Or.inl hfirst, hf, ?_⟩
    constructor
    · intro he
      exact (hli (he.1.trans hfi)).elim
    · intro hi
      exact (hli hi.1).elim

/-- A singleton first/last occurrence is retained once. The Boolean is
internal proof bookkeeping, never a new observation or source variable. -/
theorem extreme_card_le_two [Fintype Taxon] (taxon : Fin m → Taxon) :
    Fintype.card {i : Fin m // Extreme taxon i} ≤ 2 * Fintype.card Taxon := by
  classical
  let encode : {i : Fin m // Extreme taxon i} → Taxon × Bool :=
    fun i => (taxon i.val, if First taxon i.val then true else false)
  have hinj : Function.Injective encode := by
    intro i j heq
    have ht : taxon i.val = taxon j.val := congrArg Prod.fst heq
    have hbit :
        (if First taxon i.val then true else false) =
          (if First taxon j.val then true else false) :=
      congrArg Prod.snd heq
    apply Subtype.ext
    by_cases hi : First taxon i.val
    · have hj : First taxon j.val := by
        by_contra hn
        simp only [if_pos hi, if_neg hn] at hbit
        cases hbit
      exact le_antisymm (hi j.val ht.symm) (hj i.val ht)
    · have hj : ¬ First taxon j.val := by
        intro hj
        simp only [if_neg hi, if_pos hj] at hbit
        cases hbit
      have ilast : Last taxon i.val := i.property.resolve_left hi
      have jlast : Last taxon j.val := j.property.resolve_left hj
      exact le_antisymm (jlast i.val ht) (ilast j.val ht.symm)
  calc
    Fintype.card {i : Fin m // Extreme taxon i} ≤ Fintype.card (Taxon × Bool) :=
      Fintype.card_le_of_injective encode hinj
    _ = 2 * Fintype.card Taxon := by simp [Fintype.card_prod, Nat.mul_comm]

end ResearchCommons.NANUQ.ContiguousCopies
