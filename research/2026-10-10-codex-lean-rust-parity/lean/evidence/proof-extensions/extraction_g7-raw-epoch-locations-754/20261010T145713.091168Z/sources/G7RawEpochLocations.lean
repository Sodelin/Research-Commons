import G7FullEpochSupport
import UnifiedLean.Source.SourceInitializedCalendar

/-!
# Every raw original epoch row preserves each copied population

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Reuses the original legal-merge population identity, exact encoding identity,
and constructive whole-panel reassembly. Raw rows include zero coefficient
lists and cancellation branches. No positive-PMF-support inference, full-Code
enumeration, fitted population carrier or runtime refinement is asserted.
Draft pending sole-scheduler kernel checking and complete owned audit.
-/
universe uC
namespace GProgram.G7.RawEpochLocations
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCalendarCompatibility
open GProgram.G7.WholeAncestorPanelCode DotG6.ActualPopulationPanelSplit
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveCoefficientSupport GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.ConstructivePanelJoin GProgram.G7.EffectivePanelJoin
open GProgram.G7.SparseRowProducts GProgram.G7.FullEpochSupport

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [FinEnum V] [FinEnum E]
variable {Copy : Type uC} [DecidableEq Copy] [Fintype Copy] [FinEnum Copy]

lemma encodeActual_copyLocation (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) (x : Copy) :
    copyLocation (state (encodeActual N sample s hs)) x = copyLocation s x := by
  change copyLocation (decodeSnapshot N.root (encodeSnapshot s hs.forest)) x = _
  exact decode_encode_copyLocation N.root s hs.forest x

lemma merger_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (x : Copy) :
    copyLocation (state (merger N s p)) x = copyLocation (state s) x := by
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  let hv := merge_source_valid N sample (state s) s.property hm
  rw [merger_eq]
  change copyLocation (decodeSnapshot N.root
    (encodeSnapshot (merge (state s) p.2.val.1 p.2.val.2) hv.forest)) x = _
  exact (decode_encode_copyLocation N.root _ hv.forest x).trans
    (merge_population_preserved (state s) hm x)

theorem destinations_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s d : Code N sample) (hd : d ∈ destinations N fuel s) :
    ∀ x : Copy, copyLocation (state d) x = copyLocation (state s) x := by
  induction fuel generalizing s with
  | zero =>
      have he : d = s := List.mem_singleton.mp hd
      rw [he]
      intro x
      rfl
  | succ fuel ih =>
      by_cases hk : s.val.live.card ≤ 1
      · rw [destinations,if_pos hk] at hd
        have he : d = s := List.mem_singleton.mp hd
        rw [he]
        intro x
        rfl
      · rw [destinations,if_neg hk] at hd
        rcases List.mem_cons.mp hd with he | hd
        · rw [he]
          intro x
          rfl
        · rcases List.mem_flatMap.mp hd with ⟨p,_,hd⟩
          intro x
          exact (ih (merger N s p) hd x).trans (merger_copyLocation N s p x)

lemma populationRows_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (row : Code N sample × Sparse (Option E))
    (hrow : row ∈ populationRows N s i) (x : Copy) :
    copyLocation (state row.1) x = copyLocation (state s) x := by
  rcases List.mem_map.mp hrow with ⟨d,hd,he⟩
  rw [← he]
  exact destinations_copyLocation N (Fintype.card Copy) s d (List.mem_dedup.mp hd) x

lemma panel_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hc : AncestorClosed (state s) keep)
    (x : SelectedCopy keep) :
    copyLocation (state (panel N s keep hc)) x = copyLocation (state s) x.val := by
  unfold panel
  rw [encodeActual_copyLocation]
  rfl

lemma joinedCode_copyLocation_left (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) (x : SelectedCopy keep) :
    copyLocation (state (joinedCode N keep a b)) x.val = copyLocation (state a) x := by
  unfold joinedCode
  rw [encodeActual_copyLocation]
  exact joined_copyLocation_left keep (state a) (state b) x

lemma joinedCode_copyLocation_right (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep)))
    (x : SelectedCopy (Finset.univ \ keep)) :
    copyLocation (state (joinedCode N keep a b)) x.val = copyLocation (state b) x := by
  unfold joinedCode
  rw [encodeActual_copyLocation]
  exact joined_copyLocation_right keep (state a) (state b) x

/-- Every literal row in the full finite panel product has the original copied
population at every outer label, independently of its coefficient. -/
theorem fullRows_copyLocation (N : RootedBinary V E X) (todo : List (Option E)) :
    ∀ (C : Type uC) [DecidableEq C] [Fintype C] [FinEnum C] (sample : C → X)
      (s : Code N sample) (row : Code N sample × Sparse (Option E)),
      row ∈ fullRows N todo C sample s →
      ∀ x : C, copyLocation (state row.1) x = copyLocation (state s) x := by
  induction todo with
  | nil =>
      intro C _ _ _ sample s row hrow x
      have he : row = (s,single 1) := List.mem_singleton.mp hrow
      rw [he]
  | cons i todo ih =>
      intro C _ _ _ sample s row hrow x
      let keep := populationPanel (state s) (originalPlace N i)
      let hc : AncestorClosed (state s) keep :=
        locationPanel_closed (state s) s.property.forest (originalPlace N i)
      let left := panel N s keep hc
      let right := panel N s (Finset.univ \ keep) (closed_complement (state s) keep hc)
      have hrows : fullRows N (i::todo) C sample s =
          multiplyRows (joinedCode N keep) (populationRows N left i)
            (fullRows N todo (SelectedCopy (Finset.univ \ keep))
              (selectedSample sample (Finset.univ \ keep)) right) := rfl
      rw [hrows] at hrow
      rcases List.mem_flatMap.mp hrow with ⟨a,ha,hrow⟩
      rcases List.mem_map.mp hrow with ⟨b,hb,he⟩
      rw [← he]
      change copyLocation (state (joinedCode N keep a.1 b.1)) x =
        copyLocation (state s) x
      by_cases hx : x ∈ keep
      · exact (joinedCode_copyLocation_left N keep a.1 b.1 ⟨x,hx⟩).trans
          ((populationRows_copyLocation N left i a ha ⟨x,hx⟩).trans
            (panel_copyLocation N s keep hc ⟨x,hx⟩))
      · let xr : SelectedCopy (Finset.univ \ keep) := ⟨x,complement_mem keep x hx⟩
        exact (joinedCode_copyLocation_right N keep a.1 b.1 xr).trans
          ((ih (SelectedCopy (Finset.univ \ keep))
            (selectedSample sample (Finset.univ \ keep)) right b hb xr).trans
              (panel_copyLocation N s (Finset.univ \ keep)
                (closed_complement (state s) keep hc) xr))

theorem epochRows_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (row : Code N sample × Sparse (Option E))
    (hrow : row ∈ epochRows N s) (x : Copy) :
    copyLocation (state row.1) x = copyLocation (state s) x :=
  fullRows_copyLocation N (FinEnum.toList (Option E)) Copy sample s row hrow x

theorem epochRows_epochCompatible (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X} {a b : ℝ}
    (s : Code N sample) (hs : EpochCompatible N C a b (state s))
    (row : Code N sample × Sparse (Option E)) (hrow : row ∈ epochRows N s) :
    EpochCompatible N C a b (state row.1) := by
  intro x
  rw [epochRows_copyLocation N s row hrow x]
  exact hs x

#print axioms merger_copyLocation
#print axioms destinations_copyLocation
#print axioms fullRows_copyLocation
#print axioms epochRows_epochCompatible
end GProgram.G7.RawEpochLocations
