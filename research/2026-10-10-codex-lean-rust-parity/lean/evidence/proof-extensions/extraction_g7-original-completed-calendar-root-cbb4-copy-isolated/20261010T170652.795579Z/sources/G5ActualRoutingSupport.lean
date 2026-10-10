import G5ActualNoMergerReadout
import G5OriginalProgramSurvival
import G5OriginalSelectedPosterior

/-!
# Exact route-only support of an actual source word
Contributor: dot, 2026-10-09. Candidate pending compiler/source review.
Intervals are erased from the routing reader, while every original boundary
kernel, current-root owner and shared register is unchanged. The support
identity is derived from strict loss of roots at each merger and positive
actual holding mass. It is a whole-carrier statement, not a claim that an
unselected larger forest cannot merge invisibly.
-/
namespace GProgram.G5.ActualRoutingSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G5.ActualNoMergerReadout GProgram.G5.OriginalProgramSurvival
open GProgram.G5.OriginalSelectedPosterior
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.SourceCrossCarrierEpoch
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def routeProgram (N : RootedBinary V E X) {sample : Copy → X} :
    List (ProgramStep N) → Code N sample → PMF (Code N sample)
  | [], s => PMF.pure s
  | .interval _ :: ops, s => routeProgram N ops s
  | .boundary b :: ops, s => (boundaryKernel N b s).bind (routeProgram N ops)

lemma boundary_live_card (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s d : Code N sample)
    (hd : d ∈ (boundaryKernel N b s).support) : liveCard d = liveCard s := by
  cases b with
  | exit e =>
      have he : d = exitCode N s e := by simpa [boundaryKernel] using hd
      subst d
      rfl
  | ordinary e degree =>
      have he : d = ordinaryCode N s e := by simpa [boundaryKernel] using hd
      subst d
      rfl
  | root =>
      have he : d = rootCode N s := by simpa [boundaryKernel] using hd
      subst d
      rfl
  | common H =>
      have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa [boundaryKernel] using hd
      subst d
      rfl
  | independent H gamma =>
      change d ∈ ((currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
        (pulseCode H s)).support at hd
      obtain ⟨coin, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      subst d
      rfl

lemma epoch_card_le (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample)
    (hd : d ∈ (sourceTimeKernel N r t s).support) : liveCard d ≤ liveCard s := by
  obtain ⟨k, _, hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact iteration_support_card_le N r k s hk

lemma program_card_le (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hd : d ∈ (sourceProgram N r ops s).support) : liveCard d ≤ liveCard s := by
  induction ops generalizing s with
  | nil => have he : d = s := by simpa [sourceProgram] using hd
           subst d; exact le_refl _
  | cons op ops ih =>
      obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have htail := ih m hdm
      cases op with
      | interval t => exact htail.trans (epoch_card_le N r t s m hm)
      | boundary b => rw [← boundary_live_card N b s m hm]; exact htail

lemma route_live_card (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s d : Code N sample)
    (hd : d ∈ (routeProgram N ops s).support) : liveCard d = liveCard s := by
  induction ops generalizing s with
  | nil => have he : d = s := by simpa [routeProgram] using hd
           subst d; rfl
  | cons op ops ih =>
      cases op with
      | interval t => exact ih s hd
      | boundary b =>
          obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
          exact (ih m hdm).trans (boundary_live_card N b s m hm)

lemma route_in_source_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hd : d ∈ (routeProgram N ops s).support) :
    d ∈ (sourceProgram N r ops s).support := by
  induction ops generalizing s with
  | nil => exact hd
  | cons op ops ih =>
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      cases op with
      | interval t => exact ⟨s, actual_epoch_self_in_support N r t s, ih s hd⟩
      | boundary b =>
          obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
          exact ⟨m, hm, ih m hdm⟩

/-- Exact support, with all source chronology and boundary routing retained.
No stochastic-matrix membership or abstract route-cover hypothesis is used. -/
theorem actual_unchanged_count_iff_route (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s d : Code N sample) :
    (d ∈ (sourceProgram N r ops s).support ∧ liveCard d = liveCard s) ↔
      d ∈ (routeProgram N ops s).support := by
  constructor
  · rintro ⟨hd, hc⟩
    induction ops generalizing s with
    | nil => exact hd
    | cons op ops ih =>
        obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
        have htail := program_card_le N r ops m d hdm
        cases op with
        | interval t =>
            have hstep := epoch_card_le N r t s m hm
            have hms : liveCard m = liveCard s := by omega
            have he := actual_kernel_same_card_eq N r t s m hm hms
            subst m
            exact ih s hdm hc
        | boundary b =>
            apply (PMF.mem_support_bind_iff _ _ _).mpr
            refine ⟨m, hm, ih m hdm ?_⟩
            exact hc.trans (boundary_live_card N b s m hm).symm
  · intro hd
    exact ⟨route_in_source_support N r ops s d hd, route_live_card N ops s d hd⟩

lemma singleton_ancestor_injective (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ)) :
    Function.Injective (state s).ancestor := by
  have hg (x : Copy) : (state s).genealogy ((state s).ancestor x) = .leaf x := by
    have h := hs x (Finset.mem_univ x)
    simpa only [selectedView, selectedGenealogy, Finset.mem_univ, if_true,
      full_prune, Option.some.injEq] using h
  intro x y hxy
  have he : Genealogy.leaf x = Genealogy.leaf y := by
    rw [← hg x, ← hg y, hxy]
  exact Genealogy.leaf.inj he

lemma route_singleton_selected (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s d : Code N sample) (keep : Finset Copy)
    (hs : SingletonSelected keep (selectedView (state s) keep))
    (hd : d ∈ (routeProgram N ops s).support) :
    SingletonSelected keep (selectedView (state d) keep) := by
  induction ops generalizing s with
  | nil => have he : d = s := by simpa [routeProgram] using hd
           subst d; exact hs
  | cons op ops ih =>
      cases op with
      | interval t => exact ih s hs hd
      | boundary b =>
          obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
          exact ih m (actual_boundary_singleton_selected N keep b s m hm hs) hdm

noncomputable def originalRouteLaw (N : RootedBinary V E X) (sample : Copy → X)
    (p : HybridProbabilities N) (ops : List (ProgramStep N)) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    routeProgram N ops (initialCode N sample register))

/-- Natural once-drawn registers and all current-owner boundary coins are
kept. This is exact support of a WHOLE selected carrier, after G2 selection. -/
theorem actual_original_singleton_iff_route (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (d : Code N sample) :
    (d ∈ (originalProgramLaw N sample p r ops).support ∧
      SingletonSelected Finset.univ (selectedView (state d) Finset.univ)) ↔
      d ∈ (originalRouteLaw N sample p ops).support := by
  constructor
  · rintro ⟨hd, hs⟩
    obtain ⟨register, hr, hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨register, hr, (actual_unchanged_count_iff_route N r ops _ d).mp ⟨hdr, ?_⟩⟩
    have hdcard := (actual_maximal_live_card_iff N d).mpr
      (singleton_ancestor_injective N d hs)
    have hicard := (actual_maximal_live_card_iff N (initialCode N sample register)).mpr
      (singleton_ancestor_injective N _
        (actual_initial_singleton_selected N sample Finset.univ register))
    exact hdcard.trans hicard.symm
  · intro hd
    obtain ⟨register, hr, hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    refine ⟨(PMF.mem_support_bind_iff _ _ _).mpr
      ⟨register, hr, route_in_source_support N r ops _ d hdr⟩, ?_⟩
    exact route_singleton_selected N ops _ d Finset.univ
      (actual_initial_singleton_selected N sample Finset.univ register) hdr

/-- The actual posterior supports precisely images of actual boundary-route
histories. This removes the ordinary-merger PMF from the support criterion. -/
theorem actual_posterior_route_support (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (v : JoinedIndex N sample Finset.univ) :
    v ∈ (originalFullPosterior N sample p r Finset.univ ops).support ↔
      ∃ d, d ∈ (originalRouteLaw N sample p ops).support ∧
        joinedProjection N Finset.univ (.inl d) = v := by
  rw [actual_original_posterior_support_iff]
  constructor
  · rintro ⟨d, hd, hs, hv⟩
    exact ⟨d, (actual_original_singleton_iff_route N sample p r ops d).mp ⟨hd, hs⟩, hv⟩
  · rintro ⟨d, hd, hv⟩
    obtain ⟨hd', hs⟩ := (actual_original_singleton_iff_route N sample p r ops d).mpr hd
    exact ⟨d, hd', hs, hv⟩

#print axioms boundary_live_card
#print axioms program_card_le
#print axioms actual_unchanged_count_iff_route
#print axioms actual_original_singleton_iff_route
#print axioms actual_posterior_route_support
end GProgram.G5.ActualRoutingSupport
