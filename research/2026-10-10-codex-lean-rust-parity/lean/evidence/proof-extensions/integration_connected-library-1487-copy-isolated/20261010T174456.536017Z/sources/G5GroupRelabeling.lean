import G5CoupledGroupSemantics

/-!
# Coupled quartet selectors are invariant under actual group relabeling

Contributor: dot, 2026-10-02. A small group's private selectors extend along
an injective original-group-ID map. No compatibility/output field supplies
the conclusion; the extension function is constructed in the proof.
-/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

theorem coupled_reindex_of_injective {k r : Nat}
    (pos : Fin r → Fin 2 → α) (e : Fin k → Fin r)
    (he : Function.Injective e) (owner : Fin 4 → Fin k) :
    coupledQuartetWitness pos (e ∘ owner) ↔
      coupledQuartetWitness (fun i => pos (e i)) owner := by
  constructor
  · rintro ⟨choice,hw⟩
    exact ⟨choice ∘ e,hw⟩
  · rintro ⟨choice,hw⟩
    refine ⟨Function.extend e choice (fun _ => 0),?_⟩
    simpa only [quartetAt,groupSelected,Function.comp_apply,he.extend_apply] using hw

theorem coupled_iff_selector_of_injective_owner {r : Nat}
    (pos : Fin r → Fin 2 → α) (owner : Fin 4 → Fin r)
    (howner : Function.Injective owner) :
    coupledQuartetWitness pos owner ↔ selectorWitness (fun i => pos (owner i)) := by
  have hh := coupled_reindex_of_injective pos owner howner (id : Fin 4 → Fin 4)
  simpa only [Function.comp_id, four_coupled_iff_selectorWitness] using hh

#print axioms coupled_reindex_of_injective
#print axioms coupled_iff_selector_of_injective_owner
end GProgram.G5.QuartetKernel
