import TerminalCloneAvoiders

/-! Frozen CB-ALEXANDER-002 owner/type correspondence, not adopted.
Reuses the original actual-population parent selection and terminal cloning.
One Q escapes every listed host and every finite global stretch simultaneously.
No uniform child cap, terminal-free or unbounded-stretch assertion; no novelty claim. -/
namespace ResearchCommons.Claims.CountableHosts
open GenericUniversalAvoiders TerminalCloneAvoiders
universe u v w
variable {Label : Type w}

theorem selected_exact_parents {V : Type u} (p : Population V Label) :
    ExactlyOneParentPerLabel (selectParents p) := selectParents_exact p

theorem selection_language_inclusion {V : Type u} (p : Population V Label)
    (s : ℕ → Label) : Realizes (selectParents p) s → Realizes p s :=
  selectParents_realizes p s

theorem selected_clone_language {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x) (s : ℕ → Label) :
    Realizes (terminalClone (selectParents p) m hm) s ↔ Realizes (selectParents p) s :=
  terminalClone_language (selectParents p) m hm s

theorem selected_clone_actual_roots {V : Type u} (p : Population V Label)
    (m : V → ℕ) (hm : ∀ x, 0 < m x)
    (hroot : ∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) :
    Nonempty ({x : Fibre V m //
      ∀ y b, ¬ (terminalClone (selectParents p) m hm).edge y x b} ≃
      {x : V // ∀ y b, ¬ p.edge y x b}) :=
  ⟨selectedClone_rootsEquiv p m hm hroot⟩

theorem one_clone_escapes_countable_hosts {V : Type u}
    (p : Population V Label) (s : ℕ → Label) (avoids : ¬ Realizes p s)
    (W : ℕ → Type v) (hosts : ∀ j, Population (W j) Label) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (¬ Realizes (terminalClone (selectParents p) m hm) s) ∧
      (∀ t, Realizes (terminalClone (selectParents p) m hm) t → Realizes p t) ∧
      Nonempty ({x : Fibre V m //
        ∀ y b, ¬ (terminalClone (selectParents p) m hm).edge y x b} ≃
        {x : V // ∀ y b, ¬ p.edge y x b}) ∧
      ExactlyOneParentPerLabel (terminalClone (selectParents p) m hm) ∧
      ∀ j L (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (terminalClone (selectParents p) m hm)
          ((populationHost (hosts j)).power L) f := by
  obtain ⟨m,hm,ha,hl,hr,hp,hn⟩ :=
    avoiding_no_countable_exact_parent_family_from_any_population p s avoids W hosts
  exact ⟨m,hm,ha,hl,⟨selectedClone_rootsEquiv p m hm hr⟩,hp,hn⟩

theorem exact_parent_original_language_escape {V : Type u}
    (p : Population V Label) (exact_parents : ExactlyOneParentPerLabel p)
    (s : ℕ → Label) (avoids : ¬ Realizes p s)
    (W : ℕ → Type v) (hosts : ∀ j, Population (W j) Label) :
    ∃ (m : V → ℕ) (hm : ∀ x, 0 < m x),
      (¬ Realizes (terminalClone p m hm) s) ∧
      (∀ t, Realizes (terminalClone p m hm) t ↔ Realizes p t) ∧
      (∀ x, (∀ y b, ¬ p.edge y x b) → m x = 1) ∧
      ExactlyOneParentPerLabel (terminalClone p m hm) ∧
      ∀ j L (f : Fibre V m → W j), Function.Injective f →
        ¬ PreservesEdges (terminalClone p m hm)
          ((populationHost (hosts j)).power L) f :=
  avoiding_no_countable_exact_parent_bounded_stretch_population_family
    p exact_parents s avoids W hosts
end ResearchCommons.Claims.CountableHosts
