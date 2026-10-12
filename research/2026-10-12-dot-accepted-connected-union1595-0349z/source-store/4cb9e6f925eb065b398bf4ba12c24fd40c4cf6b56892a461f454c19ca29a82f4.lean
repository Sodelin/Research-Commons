import G5BinaryRootSuppressedCutEncoding
import G5FairRawQuartetIdentificationFiniteLabels

/-!
# Fair M2 identifies the documented normalized edge-cut quartet target
Contributor: dot / OpenAI, 2026-10-03.
The target is built by actual original-switching taxon/dead-twig pruning and
unary suppression, followed by the explicit binary-root unordered-cut encoding.
Matches G5-NONPLANAR-CALENDAR-QUARTETS.md section 7 and the cluster-to-S root
suppression convention in sections 1 and G5-TRIPLE-CALENDAR-FULL-TARGET.md 5.
It is not an adjacency renderer or a semidirected/up-down network convention.
-/
namespace GProgram.G5.Normalization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest GProgram.G5.AttainedChronology
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativeFairCurrentPosition
open scoped Classical
variable {V E X V₂ E₂ : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

def rootSuppressedTreeResolves (T : Genealogy X) (q : Fin 4 ↪ X) (r : Nanuq.Quartet.Resolution) : Prop :=
  rootSuppressedTreeQuartet T ((resolutionPermutation r).trans q)

def allResolutions : Finset Nanuq.Quartet.Resolution :=
  {Nanuq.Quartet.Resolution.xy_zw,Nanuq.Quartet.Resolution.xz_yw,Nanuq.Quartet.Resolution.xw_yz}

lemma mem_allResolutions (r : Nanuq.Quartet.Resolution) : r ∈ allResolutions := by
  cases r <;> simp [allResolutions]

/-- Actual normalized original-switching displayed quartet union, with
nonempty/full/root exclusions and binary-root edge identification performed by
rootSuppressedCuts. Only local ORIGINAL edge/taxon evaluation rules are used. -/
noncomputable def normalizedDisplayedCutQuartets (N : RootedBinary V E X) (q : Fin 4 ↪ X) : Finset Nanuq.Quartet.Resolution :=
  allResolutions.filter (fun r => ∃ S : N.Switching, ∃ T : Genealogy X,
    PrunedAt N S Finset.univ N.root (some T) ∧ rootSuppressedTreeResolves T q r)

lemma selected_resolution_iff_permuted_first (N : RootedBinary V E X) (S : N.Switching)
    (q : Fin 4 ↪ X) (r : Nanuq.Quartet.Resolution) :
    S.graph.Resolves (fun i => N.leaf (q i)) r ↔
      S.graph.HasQuartet
        (N.leaf (((resolutionPermutation r).trans q) 0))
        (N.leaf (((resolutionPermutation r).trans q) 1))
        (N.leaf (((resolutionPermutation r).trans q) 2))
        (N.leaf (((resolutionPermutation r).trans q) 3)) := by
  cases r <;> simp [EdgeGraph.Resolves,resolutionPermutation,Function.Embedding.trans_apply]

lemma actual_raw_mem_iff_selected_resolves (N : RootedBinary V E X) (q : Fin 4 ↪ X)
    (r : Nanuq.Quartet.Resolution) :
    r ∈ N.rawDisplayedQuartets q ↔ ∃ S : N.Switching, S.graph.Resolves (fun i => N.leaf (q i)) r := by
  simp only [RootedBinary.rawDisplayedQuartets,Nanuq.Quartet.displayed,Finset.mem_image,Finset.mem_univ,true_and]
  apply exists_congr
  intro S
  exact eq_comm.trans (S.resolves_iff_eq_resolve q r).symm

/-- Exact compatibility of the canonical raw switching target with actual
pruning/unary reduction and the explicit binary-root suppressed edge cuts.
NO desired Q equality or normalization-preservation field is assumed. -/
theorem raw_displayed_equals_normalized_cut_quartets
    (N : RootedBinary V E X) (C : Calendar N.graph) (q : Fin 4 ↪ X) :
    N.rawDisplayedQuartets q = normalizedDisplayedCutQuartets N q := by
  ext r
  rw [actual_raw_mem_iff_selected_resolves]
  simp only [normalizedDisplayedCutQuartets,Finset.mem_filter,mem_allResolutions,true_and]
  constructor
  · rintro ⟨S,hS⟩
    have hA : (Finset.univ : Finset X).Nonempty := ⟨q 0,Finset.mem_univ _⟩
    obtain ⟨T,hT,hwell,hlabels⟩ := nonempty_root_pruning_tree_exists N C S Finset.univ hA
    refine ⟨S,T,hT,?_⟩
    unfold rootSuppressedTreeResolves
    apply (root_suppressed_cut_quartet_iff_cluster_quartet T _ (by intro i; rw [hlabels]; simp)).mpr
    apply (pruned_tree_quartet_iff_original_cut N S Finset.univ _ (fun _ => Finset.mem_univ _) hT).mpr
    exact (selected_resolution_iff_permuted_first N S q r).mp hS
  · rintro ⟨S,T,hT,hresolve⟩
    have hlabels : T.leaves = Finset.univ := by
      have h := prunedAt_exact_leaves N S Finset.univ hT
      rw [sampledDescendants_root] at h
      simpa only [Genealogy.optionLeaves] using h
    refine ⟨S,(selected_resolution_iff_permuted_first N S q r).mpr ?_⟩
    apply (pruned_tree_quartet_iff_original_cut N S Finset.univ _ (fun _ => Finset.mem_univ _) hT).mp
    apply (root_suppressed_cut_quartet_iff_cluster_quartet T _ (by intro i; rw [hlabels]; simp)).mp
    exact hresolve

/-- Every normalized displayed quartet is realized throughout a NONEMPTY
positive actual ORIGINAL switched-edge calendar interval. This explicitly
closes the positive-path coverage port for the reduced target as well. -/
theorem normalized_cut_quartet_has_positive_original_calendar_interval
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (q : Fin 4 ↪ X) (resolved : Nanuq.Quartet.Resolution)
    (hq : resolved ∈ normalizedDisplayedCutQuartets N q) :
    ∃ a : UnifiedLean.Source.NativeCommonPairGerm.CommonSeed N, ∃ l u : ℝ, l < u ∧
      ∀ t : ℝ, l ≤ t → t < u →
        OriginalQuartetSideWitness N C H a t ((resolutionPermutation resolved).trans q) := by
  rw [←raw_displayed_equals_normalized_cut_quartets N C q,actual_raw_mem_iff_selected_resolves] at hq
  obtain ⟨S,hS⟩ := hq
  obtain ⟨a,ha⟩ := commonSwitching_covers N H S
  have hcut := (selected_resolution_iff_permuted_first N S q resolved).mp hS
  rw [←ha] at hcut
  obtain ⟨l,u,hlu,hwindow⟩ := original_calendar_quartet_witness_complete_positive_interval N C H a
    ((resolutionPermutation resolved).trans q) hcut
  exact ⟨a,l,u,hlu,hwindow⟩

/-- Full fair-M2 upper bound for the DOCUMENTED normalized original edge-cut
quartet union, including pruning/dead-twig, unary and binary-root conventions.
The observations remain fresh DISTINCT ordinary original-tip pair laws.
This theorem does not assert sharpness or a semidirected target convention. -/
theorem fair_m2_identifies_documented_normalized_cut_quartets
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    {s : ℝ} (htips : ∀ x : X, C.age (N.leaf x) = s) (htips₂ : ∀ x : X, C₂.age (N₂.leaf x) = s)
    (heq : ∀ x y : X, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ∀ q : Fin 4 ↪ X, normalizedDisplayedCutQuartets N q = normalizedDisplayedCutQuartets N₂ q := by
  intro q
  rw [←raw_displayed_equals_normalized_cut_quartets N C q,←raw_displayed_equals_normalized_cut_quartets N₂ C₂ q]
  exact fair_m2_identifies_actual_raw_displayed_quartets N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂ htips htips₂ heq q

#print axioms normalized_cut_quartet_has_positive_original_calendar_interval
#print axioms raw_displayed_equals_normalized_cut_quartets
#print axioms fair_m2_identifies_documented_normalized_cut_quartets
end GProgram.G5.Normalization
