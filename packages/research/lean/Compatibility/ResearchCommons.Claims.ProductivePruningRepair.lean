import SamuelAlexanderResearch.BoundaryRepair

/-! Frozen CB-POPULATION-003 correspondence for review, NOT adopted.
Existing original productive-core and canonical deletion-repair proofs only.
Pruning preserves the full infinite language. Repair preserves avoidance and
optimizes edges/roots only on the SAME retained S; no full language, connectivity,
species or empirical/novelty/native runtime conclusion is transferred to repair. -/
set_option autoImplicit false
noncomputable section
namespace ResearchCommons.Claims.ProductivePruningRepair
open SpeciesBridge SpeciesGlobalIAP BinaryPopulation ProductiveCore BoundaryRepair

theorem core_infinite (E : Graph) (horder : ∀ u v, E u v → u < v)
    (hroots : FiniteSupport (Root E)) (hchildren : ∀ v, FiniteSupport (E v)) :
    InfiniteSupport (Core E) := by
  exact ProductiveCore.core_infinite E horder hroots hchildren

theorem core_population {E : LabelledGraph} (p : BinaryNatPopulation E) :
    PopulationOn E (Core (ForgetLabels E)) := by
  exact ProductiveCore.core_population p

theorem reindexed_core_whole_inspecies {E : LabelledGraph} (p : BinaryNatPopulation E)
    (hiap : IAP (ForgetLabels E) Whole) :
    Inspecies (ForgetLabels (reindexed (core_population p))) Whole := by
  exact ProductiveCore.reindexed_core_whole_inspecies p hiap

theorem reindexed_core_whole_specieslike {E : LabelledGraph} (p : BinaryNatPopulation E)
    (hiap : IAP (ForgetLabels E) Whole) :
    Specieslike (ForgetLabels (reindexed (core_population p))) Whole := by
  exact ProductiveCore.reindexed_core_whole_specieslike p hiap

theorem reindexed_core_language_iff {E : LabelledGraph} (p : BinaryNatPopulation E)
    (s : Nat → Bool) : Realizes (reindexed (core_population p)) s ↔ Realizes E s := by
  exact ProductiveCore.reindexed_core_language_iff p s

theorem productive_core_theorem {E : LabelledGraph} (p : BinaryNatPopulation E)
    (hiap : IAP (ForgetLabels E) Whole) (d : Nat)
    (hcap : FixedGenderLift.ChildCap (ForgetLabels E) Whole d) :
    BinaryNatPopulation (reindexed (core_population p)) ∧
    Inspecies (Induced (ForgetLabels E) (Core (ForgetLabels E))) (Core (ForgetLabels E)) ∧
    FixedGenderLift.ChildCap (ForgetLabels (reindexed (core_population p))) Whole d ∧
    ∀ s, ¬ Realizes E s → ¬ Realizes (reindexed (core_population p)) s := by
  exact ProductiveCore.productive_core_theorem p hiap d hcap

theorem maximal_specieslike_descendantClosed (E : Graph) (S : NatSet)
    (horder : ∀ u v, E u v → u < v) (hmax : MaximalSpecieslike E S) :
    DescendantClosed E S := by
  exact ProductiveCore.maximal_specieslike_descendantClosed E S horder hmax

theorem maximal_cluster_pruning_commutes (E : Graph) (S : NatSet)
    (horder : ∀ u v, E u v → u < v) (hmax : MaximalSpecieslike E S) :
    RelativeCore E S = fun v => S v ∧ Core E v := by
  exact ProductiveCore.maximal_cluster_pruning_commutes E S horder hmax

theorem four_axioms_pruning_commutes (E : Graph) (S : NatSet)
    (h : SpeciesRootCriterion.FourAxioms E S) :
    RelativeCore E S = fun v => S v ∧ Core E v := by
  exact ProductiveCore.four_axioms_pruning_commutes E S h

theorem nonmaximal_cluster_productivity_counterexample :
    Specieslike PsEdge (fun v => v = 0) ∧ Core PsEdge 0 ∧
      ¬ RelativeCore PsEdge (fun v => v = 0) 0 := by
  exact ProductiveCore.nonmaximal_cluster_productivity_counterexample 

theorem constrained_maximum_not_descendantClosed :
    NaturalDateBiosphere ForkEdge ∧
    SpeciesRootCriterion.MaximalFourAxioms ForkEdge OddRay ∧
    Specieslike ForkEdge OddRay ∧ ¬ DescendantClosed ForkEdge OddRay := by
  exact ProductiveCore.constrained_maximum_not_descendantClosed 

theorem core_ancestrallyClosed (E : Graph) : AncestrallyClosed E (Core E) := by
  exact ProductiveCore.core_ancestrallyClosed E

theorem reindexed_population {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S) :
    BinaryNatPopulation (reindexed p) := by
  exact ProductiveCore.reindexed_population p

theorem reindexed_child_cap {E : LabelledGraph} {S : NatSet} (p : PopulationOn E S)
    (d : Nat) (hcap : FixedGenderLift.ChildCap (ForgetLabels E) S d) :
    FixedGenderLift.ChildCap (ForgetLabels (reindexed p)) Whole d := by
  exact ProductiveCore.reindexed_child_cap p d hcap

theorem deficient_finite_of_cofinite {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hremoved : FiniteSupport (fun v => ¬ S v)) : FiniteSupport (Deficient E S) := by
  exact BoundaryRepair.deficient_finite_of_cofinite p S hremoved

theorem cofinite_repair_population {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hremoved : FiniteSupport (fun v => ¬ S v)) : PopulationOn (Repair E S) S := by
  exact BoundaryRepair.cofinite_repair_population p S hremoved

theorem finite_deficiency_iff_repair_exists {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hinfinite : InfiniteSupport S) :
    FiniteSupport (Deficient E S) ↔
      ∃ F, AdmissibleRepair E S F ∧ PopulationOn F S := by
  exact BoundaryRepair.finite_deficiency_iff_repair_exists p S hinfinite

theorem repair_greatest (E : LabelledGraph) (S : NatSet) (F : LabelledGraph)
    (hF : AdmissibleRepair E S F) : ∀ u v b, F u v b → Repair E S u v b := by
  exact BoundaryRepair.repair_greatest E S F hF

theorem repair_minimal_roots (E : LabelledGraph) (S : NatSet) (F : LabelledGraph)
    (hF : AdmissibleRepair E S F) (v : Nat) (hv : S v)
    (hr : Root (ProductiveCore.Induced (ForgetLabels (Repair E S)) S) v) :
    Root (ProductiveCore.Induced (ForgetLabels F) S) v := by
  exact BoundaryRepair.repair_minimal_roots E S F hF v hv hr

theorem repair_deleted_edges_bounded {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hdeficient : FiniteSupport (Deficient E S)) :
    ∃ bound, ∀ u v b, Restrict E S u v b → ¬ Repair E S u v b →
      u < bound ∧ v < bound := by
  exact BoundaryRepair.repair_deleted_edges_bounded p S hdeficient

theorem finite_boundary_repair_theorem {E : LabelledGraph} (p : BinaryNatPopulation E)
    (S : NatSet) (hinfinite : InfiniteSupport S) (hdeficient : FiniteSupport (Deficient E S))
    (d : Nat) (hcap : FixedGenderLift.ChildCap (ForgetLabels E) Whole d) :
    let q := repair_population_of_finite_deficiency p S hinfinite hdeficient
    BinaryNatPopulation (reindexed q) ∧
    FixedGenderLift.ChildCap (ForgetLabels (reindexed q)) Whole d ∧
    (∀ s, ¬ Realizes E s → ¬ Realizes (reindexed q) s) ∧
    (∀ i, Root (ForgetLabels (reindexed q)) i ↔ Deficient E S (vertex q i)) := by
  exact BoundaryRepair.finite_boundary_repair_theorem p S hinfinite hdeficient d hcap

theorem ps_c0_repair_roots (s : Nat → Bool) (v : Nat) :
    (SpeciesCones.C0 v ∧ Root (ProductiveCore.Induced
      (ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C0)) SpeciesCones.C0) v) ↔
      v = 0 ∨ v = 2 ∨ v = 3 := by
  exact BoundaryRepair.ps_c0_repair_roots s v

theorem ps_c1_repair_roots (s : Nat → Bool) (v : Nat) :
    (SpeciesCones.C1 v ∧ Root (ProductiveCore.Induced
      (ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C1)) SpeciesCones.C1) v) ↔
      v = 1 ∨ v = 2 := by
  exact BoundaryRepair.ps_c1_repair_roots s v

theorem ps_c0_cut_edges (s : Nat → Bool) (u v : Nat) (b : Bool) :
    (Restrict (BinaryAvoidance.Edge s) SpeciesCones.C0 u v b ∧
      ¬ Repair (BinaryAvoidance.Edge s) SpeciesCones.C0 u v b) ↔
    ((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 3)) ∧ BinaryAvoidance.Edge s u v b := by
  exact BoundaryRepair.ps_c0_cut_edges s u v b

theorem ps_c1_cut_edges (s : Nat → Bool) (u v : Nat) (b : Bool) :
    (Restrict (BinaryAvoidance.Edge s) SpeciesCones.C1 u v b ∧
      ¬ Repair (BinaryAvoidance.Edge s) SpeciesCones.C1 u v b) ↔
    (u = 1 ∧ v = 2) ∧ BinaryAvoidance.Edge s u v b := by
  exact BoundaryRepair.ps_c1_cut_edges s u v b

theorem ps_c0_repair_not_connected (s : Nat → Bool) :
    ¬ WeaklyConnected (ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C0))
      SpeciesCones.C0 := by
  exact BoundaryRepair.ps_c0_repair_not_connected s

theorem ps_c1_repair_shifted_geometry (s : Nat → Bool) (u v : Nat) :
    ForgetLabels (Repair (BinaryAvoidance.Edge s) SpeciesCones.C1) (u + 1) (v + 1) ↔
      PsEdge u v := by
  exact BoundaryRepair.ps_c1_repair_shifted_geometry s u v

end ResearchCommons.Claims.ProductivePruningRepair
