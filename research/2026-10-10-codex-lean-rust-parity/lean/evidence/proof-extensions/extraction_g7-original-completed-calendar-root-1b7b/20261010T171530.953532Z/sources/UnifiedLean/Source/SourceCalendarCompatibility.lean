import UnifiedLean.Source.SourcePoissonKernel
import G5CalendarRoutes

/-!
# Calendar-compatible ORIGINAL source epoch locations

Contributor: dot, 2026-10-02. The inherited SourceValid invariant is spatial;
this module adds the actual temporal invariant needed for physical epoch
assembly, and derives its preservation under actual merger/finite-code steps.
Future sampled tip nodes may be dormant until their original node age. Original
edge IDs and the actual ancestral root are retained. The initialized full
vertex agenda and clock/path identification are subsequent source obligations.
-/
namespace UnifiedLean.Source.SourceCalendarCompatibility
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Compatibility on a whole half-open epoch [a,b). Node locations are
unactivated future samples; no merger occurs at a node. -/
def LocationInEpoch (N : RootedBinary V E X) (C : Calendar N.graph)
    (a b : ℝ) : Location V E → Prop
  | .node v => b ≤ C.age v
  | .edge e => C.age (N.graph.target e) ≤ a ∧ b ≤ C.age (N.graph.source e)
  | .rootPopulation v => v = N.root ∧ C.age N.root ≤ a

def EpochCompatible (N : RootedBinary V E X) (C : Calendar N.graph)
    (a b : ℝ) (s : State V E Copy) : Prop :=
  ∀ x : Copy, LocationInEpoch N C a b (copyLocation s x)

/-- An admitted original edge occupied during this epoch is physically active
at every strictly interior time, using the original older-side convention. -/
theorem epoch_edge_active (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b t : ℝ} {s : State V E Copy} (hs : EpochCompatible N C a b s)
    {x : Copy} {e : E} (hx : copyLocation s x = .edge e)
    (ha : a ≤ t) (hb : t < b) : C.Active t e := by
  have hh := hs x
  rw [hx] at hh
  exact ⟨hh.1.trans ha,hb.trans_le hh.2⟩

/-- SourceValid's root identity is inherited, not an extra guard invented here.
The temporal part is supplied by the actual epoch locations. -/
theorem epoch_merge_compatible (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {s : State V E Copy} (hs : EpochCompatible N C a b s)
    {l m : Copy} (hm : LegalMerge s l m) :
    EpochCompatible N C a b (merge s l m) := by
  intro x
  rw [merge_population_preserved s hm]
  exact hs x

lemma encode_epoch_compatible (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} (s : State V E Copy) (hs : SourceValid N sample s)
    (hc : EpochCompatible N C a b s) :
    EpochCompatible N C a b (state (admittedCode N sample s hs)) := by
  intro x
  rw [show copyLocation (state (admittedCode N sample s hs)) x = copyLocation s x from
    decode_encode_copyLocation N.root s hs.forest x]
  exact hc x

/-- Every ACTUAL holding or merger destination stays in the same physical
calendar epoch. Snapshot encoding cannot insert a temporally invalid location. -/
theorem actual_step_destination_epoch (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) (p : Option (Choice N s)) :
    EpochCompatible N C a b (state (stepDestination N s p)) := by
  cases p with
  | none => exact hs
  | some p =>
      let hm := GProgram.SourceForestKingmanPopulationProjection.population_pair_is_source_legal
        (state s) (originalPlace N p.1) (originalPlace_not_node N p.1) p.2.property
      let hv := merge_source_valid N sample (state s) s.property hm
      exact encode_epoch_compatible N C _ hv (epoch_merge_compatible N C hs hm)

/-- Temporal compatibility is a support theorem for the genuine normalized
source step, derived from its actual destinations. -/
theorem actual_source_step_epoch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (r : PositivePairRates E) (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) {d : Code N sample}
    (hd : d ∈ (sourceStep N r s).support) : EpochCompatible N C a b (state d) := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hp]
  exact actual_step_destination_epoch N C s hs p

/-- Every finite actual-source iteration retains the physical epoch. -/
theorem actual_source_iteration_epoch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (r : PositivePairRates E) (k : Nat) (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) {d : Code N sample}
    (hd : d ∈ (sourceIteration N r k s).support) : EpochCompatible N C a b (state d) := by
  induction k generalizing s with
  | zero =>
      have he : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      simpa only [he] using hs
  | succ k ih =>
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (actual_source_step_epoch_support N C r s hs hm) hdm

/-- The entire continuous-time Poisson PMF has physical epoch support when
initialized in that epoch. No desired active-location law is assumed. -/
theorem actual_source_time_epoch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : EpochCompatible N C a b (state d) := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_source_iteration_epoch_support N C r k s hs hk

/-- Real initial samples at their original leaves, including serial samples
that are dormant until their own supplied age. -/
theorem initial_calendar_compatible (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) {a b : ℝ}
    (h : ∀ x : Copy, b ≤ C.age (N.leaf (sample x))) :
    EpochCompatible N C a b (initial N sample register) := h

/-- Actual original vertex ages, with coincident unrelated nodes deduplicated.
The finite chronology is generated from these ages, not supplied as a desired law. -/
noncomputable def originalDates (N : RootedBinary V E X) (C : Calendar N.graph) : Finset ℝ :=
  Finset.univ.image C.age

lemma originalDates_nonempty (N : RootedBinary V E X) (C : Calendar N.graph) :
    (originalDates N C).Nonempty := by
  exact ⟨C.age N.root,Finset.mem_image.mpr ⟨N.root,Finset.mem_univ _,rfl⟩⟩

noncomputable def firstOriginalDate (N : RootedBinary V E X) (C : Calendar N.graph) : ℝ :=
  (originalDates N C).min' (originalDates_nonempty N C)

lemma firstOriginalDate_le (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) :
    firstOriginalDate N C ≤ C.age v :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)

/-- Temporal initialization is derived from the finite original graph/calendar.
The first node boundary itself is processed by the later actual vertex agenda. -/
theorem actual_initial_calendar_boundary (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) :
    EpochCompatible N C (firstOriginalDate N C) (firstOriginalDate N C)
      (state (admittedCode N sample (initial N sample register)
        (initial_source_valid N sample register))) := by
  exact encode_epoch_compatible N C _ (initial_source_valid N sample register)
    (initial_calendar_compatible N C sample register (fun x => firstOriginalDate_le N C _))

#print axioms epoch_edge_active
#print axioms actual_step_destination_epoch
#print axioms actual_source_time_epoch_support
#print axioms initial_calendar_compatible
#print axioms actual_initial_calendar_boundary
end UnifiedLean.Source.SourceCalendarCompatibility
