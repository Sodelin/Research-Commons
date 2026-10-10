import ActualPopulationRate

/-! Original routed population occupancy, with original parent identities.
Contributor: dot (OpenAI), 9 October 2026. -/
namespace DotG34.ActualPulseOccupancy
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.FiniteSourceSnapshot
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma encoded_population_roots (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) (place : Location V E) :
    populationRoots (state (admittedCode N sample s hs)) place = populationRoots s place := by
  ext l
  simp only [populationRoots, Finset.mem_filter]
  change (l ∈ s.live ∧ (decodeSnapshot N.root (encodeSnapshot s hs.forest)).location l = place) ↔
    (l ∈ s.live ∧ s.location l = place)
  constructor
  · rintro ⟨hl, hp⟩
    exact ⟨hl, (decode_encode_live_population N.root s hs.forest hl) ▸ hp⟩
  · rintro ⟨hl, hp⟩
    refine ⟨hl, ?_⟩
    rw [decode_encode_live_population N.root s hs.forest hl]
    exact hp

theorem actual_pulse_population_roots (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) (place : Location V E) :
    populationRoots (state (pulseCode H s coin)) place =
      populationRoots (pulse H (state s) coin) place := by
  exact encoded_population_roots N sample _ _ place

/-- At a private entrance all current roots are at the named original hybrid;
the actual routed parent population is exactly the corresponding coin class. -/
theorem pulse_parent_population (N : RootedBinary V E X)
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy)
    (hall : ∀ l ∈ s.live, s.location l = .node H.hybrid)
    (coin : AtNode s H.hybrid → Bool) (b : Bool) :
    populationRoots (pulse H s coin) (.edge (H.parent b)) =
      (Finset.univ.filter (fun l : AtNode s H.hybrid => coin l = b)).image Subtype.val := by
  ext l
  simp only [populationRoots, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hl, hp⟩
    have hm : l ∈ s.live := hl
    let u : AtNode s H.hybrid := ⟨l, hm, hall l hm⟩
    refine ⟨u, ?_, rfl⟩
    have he : H.parent (coin u) = H.parent b := by
      simpa [pulse, transport, u, hm, hall l hm] using hp
    exact H.parent_injective he
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.property.1, ?_⟩
    simp [pulse, transport, u.property.1, u.property.2, hu]

#print axioms actual_pulse_population_roots
#print axioms pulse_parent_population
end DotG34.ActualPulseOccupancy
