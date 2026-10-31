import WongPedigreeRobust

/-! Frozen CB-WONG-004 full-card owner/type correspondence; NOT adopted.
Supplied rich-history/pedigree/owners and saturated candidates, nonempty
ancestry paths, finite but not uniformly bounded fibres and each separate
hypothesis hierarchy are preserved. Finite-error relaxation transfers IAP
alone, not reflection/specieslike/maximality. Existing deterministic finite
gARG coarsening obstruction is credited reuse, not a new discovery. No owner
inference, biological validation, empirical classification, likelihood law,
unrestricted reverse maximality, effective decision procedure or novelty claim. -/
set_option autoImplicit false
noncomputable section
namespace ResearchCommons.Claims.OwnerAncestry
universe u v w
open SpeciesBridge SpeciesGlobalIAP HistoryProjection FiniteHistoryCompletion
open WongPedigreeBridge

theorem sound_path_projects {Genome : Type u} {R : Genome -> Genome -> Prop}
    {E : SpeciesBridge.Graph} (owner : Genome -> Nat)
    (edgeSound : forall g h, R g h -> SameOrDescendant E (owner g) (owner h))
    {g h : Genome} (path : Reach R g h) :
    SameOrDescendant E (owner g) (owner h) := by
  exact HistoryProjection.path_projects owner edgeSound path

theorem fixed_locus_path_projects {Genome : Type u} {Locus : Type v}
    {R : Locus -> Genome -> Genome -> Prop} {E : SpeciesBridge.Graph}
    (owner : Genome -> Nat)
    (edgeSound : forall locus g h,
      R locus g h -> SameOrDescendant E (owner g) (owner h))
    {locus : Locus} {g h : Genome} (path : Reach (R locus) g h) :
    SameOrDescendant E (owner g) (owner h) := by
  exact HistoryProjection.locus_path_projects owner edgeSound path

theorem coordinate_erased_path_projects {Genome : Type u} {Locus : Type v}
    {R : Locus -> Genome -> Genome -> Prop} {E : SpeciesBridge.Graph}
    (owner : Genome -> Nat)
    (edgeSound : forall locus g h,
      R locus g h -> SameOrDescendant E (owner g) (owner h))
    {g h : Genome} (path : Reach (EraseIndex R) g h) :
    SameOrDescendant E (owner g) (owner h) := by
  exact HistoryProjection.erased_path_projects owner edgeSound path

theorem exact_owner_iap (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E) (S : NatSet) :
    IAP R (Pull owner S) ↔ IAP E S := by
  exact WongPedigreeBridge.iap_iff owner onto fibres faithful S

theorem exact_owner_reflection (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E) (S : NatSet) :
    Reflection R (Pull owner S) ↔ Reflection E S := by
  exact WongPedigreeBridge.reflection_iff owner onto fibres faithful S

theorem sound_common_ancestor_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (sound : PathSound owner R E)
    {S : NatSet} (ancestor : CommonAncestor R (Pull owner S)) :
    CommonAncestor E S := by
  exact WongPedigreeBridge.commonAncestor_descends owner onto sound ancestor

theorem sound_convex_pullback (owner : Nat → Nat) {R E : Graph}
    (sound : PathSound owner R E) {S : NatSet} (convex : Convex E S) :
    Convex R (Pull owner S) := by
  exact WongPedigreeBridge.convex_pullback owner sound convex

theorem exact_owner_convexity (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (S : NatSet) : Convex R (Pull owner S) ↔ Convex E S := by
  exact WongPedigreeBridge.convex_iff owner onto faithful acyclic S

theorem sound_connectedness_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (sound : PathSound owner R E)
    {S : NatSet} (convex : Convex E S)
    (connected : WeaklyConnected R (Pull owner S)) : WeaklyConnected E S := by
  exact WongPedigreeBridge.weaklyConnected_descends owner onto sound convex connected

theorem exact_owner_specieslike_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    {S : NatSet} (cluster : Specieslike R (Pull owner S)) : Specieslike E S := by
  exact WongPedigreeBridge.specieslike_descends owner onto fibres faithful acyclic cluster

theorem connected_fibre_specieslike_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) (S : NatSet) :
    Specieslike R (Pull owner S) ↔ Specieslike E S := by
  exact WongPedigreeBridge.specieslike_iff owner onto fibres faithful acyclic connectedFibres S

theorem saturated_maximality_iff (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) (S : NatSet) :
    MaximalAmongSaturated owner R S ↔ MaximalSpecieslike E S := by
  exact WongPedigreeBridge.maximal_saturated_iff owner onto fibres faithful acyclic connectedFibres S

theorem unrestricted_rich_maximality_descends (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner)
    (faithful : AncestryExactAwayFromFibres owner R E)
    (acyclic : ∀ v, ¬ Descendant E v v)
    (connectedFibres : ConnectedFibres owner R) {S : NatSet}
    (maximal : MaximalSpecieslike R (Pull owner S)) : MaximalSpecieslike E S := by
  exact WongPedigreeBridge.maximalSpecieslike_descends owner onto fibres faithful acyclic connectedFibres maximal

theorem same_carrier_finite_ancestry_errors_iap {R E : Graph} {S : NatSet}
    (errors : ∀ a, S a → FiniteSupport
      (fun b => S b ∧ ¬ (Descendant R a b ↔ Descendant E a b))) :
    IAP R S ↔ IAP E S := by
  exact WongPedigreeBridge.iap_iff_of_finite_ancestry_errors errors

theorem finite_projection_errors_iap (owner : Nat → Nat) {R E : Graph}
    (onto : Function.Surjective owner) (fibres : FiniteFibres owner) (S : NatSet)
    (errors : ∀ a, Pull owner S a → FiniteSupport
      (fun b => Pull owner S b ∧
        ¬ (Descendant R a b ↔ Descendant E (owner a) (owner b)))) :
    IAP R (Pull owner S) ↔ IAP E S := by
  exact WongPedigreeRobust.iap_iff_of_finite_projection_errors owner onto fibres S errors

theorem soundness_countercontrol :
    ∃ R A B : Graph,
      Function.Surjective (id : Nat → Nat) ∧ FiniteFibres id ∧
      NaturalDateBiosphere R ∧ NaturalDateBiosphere A ∧ NaturalDateBiosphere B ∧
      WongAlexander.RealDatedBiosphere R ∧ WongAlexander.RealDatedBiosphere A ∧
      WongAlexander.RealDatedBiosphere B ∧
      WeaklyConnected R Whole ∧
      PathSound id R A ∧ PathSound id R B ∧
      Specieslike A Whole ∧ ¬ IAP B Whole := by
  exact WongPedigreeBridge.sound_projection_does_not_determine_iap

theorem reused_finite_garg_coarsening_obstruction
    {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
    (G : WongGARG.GARG Node Coord) {Observation : Type w}
    (observe : WongGARG.GARG Node Coord → Observation) :
    ¬ ObservationPrediction.Recoverable
      (fun h : AbstractCompletionObservation Node Coord => observe h.observed)
      (fun h : AbstractCompletionObservation Node Coord => Specieslike h.completion Whole) := by
  exact WongPedigreeBridge.no_specieslike_recovery_from_garg_coarsening G observe

end ResearchCommons.Claims.OwnerAncestry
