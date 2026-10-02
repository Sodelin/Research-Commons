import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import G4PathResolvedMeasurement
import Mathlib.Data.List.OfFn

/-!
# Source-image and stopping goal audit

These are proved logical integration links and explicit countermodels, not
biological source-image/finite-stopping theorems. The observation map and
strict source admission must be supplied by the source integration modules.
No open G3/G4 conclusion, coefficient conjecture or hand receipt is an axiom.
-/
namespace UnifiedLean.Audits.ResearchGoalAudit

section EvidenceBoundary
/-- Status metadata never transports an unproved proposition. Only the
kernelChecked constructor carries a term of the actual statement. -/
inductive ClaimEvidence (statement : Prop) : Type
  | kernelChecked (proof : statement)
  | acceptedHand (sourceReceipt : String)
  | sourceEvidence (sourceReceipt : String)
  | externalPrior (citation : String)
  | failedOrUnchecked (attemptReceipt : String)
  | openGoal

def ClaimEvidence.isKernelChecked {statement : Prop}
    (e : ClaimEvidence statement) : Prop :=
  match e with
  | .kernelChecked _ => True
  | _ => False

theorem checked_evidence_has_actual_proof {statement : Prop}
    (e : ClaimEvidence statement) (h : e.isKernelChecked) : statement := by
  cases e with
  | kernelChecked hp => exact hp
  | acceptedHand _ => exact False.elim h
  | sourceEvidence _ => exact False.elim h
  | externalPrior _ => exact False.elim h
  | failedOrUnchecked _ => exact False.elim h
  | openGoal => exact False.elim h

/-- A hand-acceptance label alone supplies no kernel proof; this explicit
metadata object is well formed even with False as its declared statement. -/
theorem hand_receipt_is_metadata :
    ∃ e : ClaimEvidence False, ¬ e.isKernelChecked := by
  exact ⟨.acceptedHand "receipt identifier only", id⟩

end EvidenceBoundary

section JointSource
variable {Input Source Coordinate Value : Type*}

/-- Every row/copy coordinate is fitted by the SAME source. The source type
must retain its original graph, IDs and one parameter assignment. -/
def JointRealizes (law : Source → Coordinate → Value)
    (profile : Coordinate → Value) (source : Source) : Prop :=
  ∀ i, law source i = profile i

/-- This is rowwise compatibility, not the requested joint image. -/
def RowwiseRealizes (law : Source → Coordinate → Value)
    (profile : Coordinate → Value) : Prop :=
  ∀ i, ∃ source, law source i = profile i

theorem joint_implies_rowwise (law : Source → Coordinate → Value)
    (profile : Coordinate → Value)
    (h : ∃ source, JointRealizes law profile source) :
    RowwiseRealizes law profile := by
  rcases h with ⟨source, hs⟩
  exact fun i => ⟨source, hs i⟩

/-- A finite explicit countermodel. Each of two rows is separately realizable,
but one constant source cannot give their differing values. This audits the
invalid quantifier interchange; it is not a biological impossibility pair. -/
theorem rowwise_does_not_imply_joint :
    RowwiseRealizes (fun source : Bool => fun _ : Bool => source) id ∧
      ¬ ∃ source : Bool,
        JointRealizes (fun source : Bool => fun _ : Bool => source) id source := by
  constructor
  · intro i
    exact ⟨i, rfl⟩
  · rintro ⟨source, hs⟩
    have hf : source = false := hs false
    have ht : source = true := hs true
    cases hf.symm.trans ht

/-- Image membership for one admitted-source relation. -/
def SourceRealizable (realizes : Input → Source → Prop) (p : Input) : Prop :=
  ∃ source, realizes p source

/-- One bounded witness suffices; ALL equivalent sources need not be bounded. -/
def RealizableWithin (realizes : Input → Source → Prop) (size : Source → Nat)
    (p : Input) (B : Nat) : Prop :=
  ∃ source, size source ≤ B ∧ realizes p source

/-- The missing input-derived bound is explicit as a premise, never asserted
for an arbitrary biological profile by this module. -/
def OneWitnessBudget (realizes : Input → Source → Prop) (size : Source → Nat)
    (budget : Input → Nat) : Prop :=
  ∀ p, SourceRealizable realizes p → RealizableWithin realizes size p (budget p)

theorem within_implies_realizable (realizes : Input → Source → Prop)
    (size : Source → Nat) (p : Input) (B : Nat) :
    RealizableWithin realizes size p B → SourceRealizable realizes p := by
  rintro ⟨source, _, h⟩
  exact ⟨source, h⟩

theorem one_witness_budget_iff (realizes : Input → Source → Prop)
    (size : Source → Nat) (budget : Input → Nat)
    (hBudget : OneWitnessBudget realizes size budget) (p : Input) :
    SourceRealizable realizes p ↔ RealizableWithin realizes size p (budget p) :=
  ⟨hBudget p, within_implies_realizable realizes size p (budget p)⟩

/-- Conditional terminating decision component: the finite-budget feasibility
procedure and an input-bound FUNCTION are given as data. The proof obligation
hBudget is exactly the missing implication; this does not construct it. -/
def imageDecisionFromOneWitnessBudget (realizes : Input → Source → Prop)
    (size : Source → Nat) (budget : Input → Nat)
    (finiteTest : ∀ p B, Decidable (RealizableWithin realizes size p B))
    (hBudget : OneWitnessBudget realizes size budget) (p : Input) :
    Decidable (SourceRealizable realizes p) := by
  letI := finiteTest p (budget p)
  exact decidable_of_iff (RealizableWithin realizes size p (budget p))
    (one_witness_budget_iff realizes size budget hBudget p).symm

end JointSource

section NonEscapeQuantifiers
/-- Abstract shape/positivity budget tests for increasingly large joint
prefixes. The actual source compiler and enclosure predicates are not supplied
by this logical audit. -/
def NonEscapeBudget (test : Nat → Nat → Prop) : Prop :=
  ∃ B, ∀ m, test B m

/-- Allowing a NEW budget at each prefix is a strictly weaker condition. -/
def EveryPrefixHasBudget (test : Nat → Nat → Prop) : Prop :=
  ∀ m, ∃ B, test B m

theorem non_escape_implies_every_prefix (test : Nat → Nat → Prop)
    (h : NonEscapeBudget test) : EveryPrefixHasBudget test := by
  rcases h with ⟨B, hB⟩
  exact fun m => ⟨B, hB m⟩

/-- Checked quantifier countermodel. This is not a biological nonattainment
construction and contains no theorem about computable-profile recognition. -/
theorem every_prefix_budget_does_not_imply_non_escape :
    EveryPrefixHasBudget (fun B m => m ≤ B) ∧
      ¬ NonEscapeBudget (fun B m => m ≤ B) := by
  constructor
  · intro m
    exact ⟨m, Nat.le_refl m⟩
  · rintro ⟨B, hB⟩
    have h := hB (B + 1)
    omega

end NonEscapeQuantifiers

section StoppingQuantifiers
variable {Source Observation : Type*}

/-- All coordinates in a finite cap, not just one selected statistic. -/
def PrefixEquivalent (observe : Source → Nat → Observation)
    (x y : Source) (M : Nat) : Prop :=
  ∀ m, m ≤ M → observe x m = observe y m

def AllEquivalent (observe : Source → Nat → Observation) (x y : Source) : Prop :=
  ∀ m, observe x m = observe y m

/-- The old accepted ALL-CAP collision quantifier: both targets may vary byM. -/
def EveryCapCollision (observe : Source → Nat → Observation) : Prop :=
  ∀ M, ∃ x y, PrefixEquivalent observe x y M ∧ ¬ AllEquivalent observe x y

/-- The stronger fixed-target camouflage quantifier needed for the stopping
negative. x is chosen ONCE, before every cap. -/
def FixedTargetCamouflage (observe : Source → Nat → Observation) : Prop :=
  ∃ x, ∀ M, ∃ y, PrefixEquivalent observe x y M ∧ ¬ AllEquivalent observe x y

/-- Mathematical individual finite determinacy. An effective source/data
procedure for finding M is a further explicit requirement. -/
def EachTargetFinitelyDetermined (observe : Source → Nat → Observation) : Prop :=
  ∀ x, ∃ M, ∀ y, PrefixEquivalent observe x y M → AllEquivalent observe x y

theorem fixed_target_implies_every_cap (observe : Source → Nat → Observation)
    (h : FixedTargetCamouflage observe) : EveryCapCollision observe := by
  rcases h with ⟨x, hx⟩
  intro M
  rcases hx M with ⟨y, heq, hne⟩
  exact ⟨x, y, heq, hne⟩

theorem finite_determination_excludes_fixed_camouflage
    (observe : Source → Nat → Observation)
    (h : EachTargetFinitelyDetermined observe) : ¬ FixedTargetCamouflage observe := by
  rintro ⟨x, hx⟩
  rcases h x with ⟨M, hm⟩
  rcases hx M with ⟨y, heq, hne⟩
  exact hne (hm y heq)

/-- Threshold readout: every individual threshold has a finite certificate,
although no global cap works for all thresholds. This is only a quantifier
countermodel and has no biological source interpretation. -/
def thresholdObservation (x m : Nat) : Bool := if x ≤ m then true else false

theorem threshold_every_cap_collision : EveryCapCollision thresholdObservation := by
  intro M
  refine ⟨M + 1, M + 2, ?_, ?_⟩
  · intro m hm
    simp [thresholdObservation, show ¬M + 1 ≤ m by omega,
      show ¬M + 2 ≤ m by omega]
  · intro h
    have he := h (M + 1)
    simp [thresholdObservation] at he

theorem threshold_each_target_finitely_determined :
    EachTargetFinitelyDetermined thresholdObservation := by
  intro x
  refine ⟨x, ?_⟩
  intro y h
  have hyx : y ≤ x := by
    have he := h x (Nat.le_refl x)
    by_contra hn
    simp [thresholdObservation, hn] at he
  have hxy : x ≤ y := by
    by_contra hn
    have hylt : y < x := by omega
    have he := h y (Nat.le_of_lt hylt)
    simp [thresholdObservation, show ¬x ≤ y by omega] at he
  have hsame : x = y := Nat.le_antisymm hxy hyx
  subst y
  exact fun _ => rfl

/-- Checked failure of the implication that would incorrectly close G4. -/
theorem every_cap_does_not_imply_fixed_target :
    EveryCapCollision thresholdObservation ∧
      ¬ FixedTargetCamouflage thresholdObservation :=
  ⟨threshold_every_cap_collision,
    finite_determination_excludes_fixed_camouflage thresholdObservation
      threshold_each_target_finitely_determined⟩

end StoppingQuantifiers

section RequiredSharpness
/-- Mathematical sharpness only when a MINIMUM threshold is requested.
The predicate must describe the actual admissible readout/model class. -/
def SharpMinimum (worksAt : Nat → Prop) (n : Nat) : Prop :=
  worksAt n ∧ ∀ m, m < n → ¬ worksAt m

/-- A strongest sufficient bound alone is not a minimality theorem. -/
theorem sufficient_does_not_imply_sharp :
    (fun _ : Nat => True) 3 ∧ ¬ SharpMinimum (fun _ : Nat => True) 3 := by
  constructor
  · trivial
  · rintro ⟨_, h⟩
    exact h 0 (by omega) trivial

end RequiredSharpness

section NativeItineraryAudit
open GProgram.G4.PathResolved
open G4TwoRootSourceStopping
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable {N : RootedBinary V E X} {n m : Nat}

/-- List-valued form of the EXISTING genuinely observed complete original
parent record. This changes neither its edge IDs nor its route coins. -/
noncomputable def fullOriginalParentRecord
    (H : Fin n → GProgram.G2.OriginalHybridParents N)
    (c : Color (Fin n)) : List E :=
  List.ofFn (observedOriginalParents H c)

omit [DecidableEq E] in
/-- One complete original record already reveals the number of sites. This
is conditional on the richer readout contract, not recovered from forests. -/
theorem full_original_record_length
    (H : Fin n → GProgram.G2.OriginalHybridParents N)
    (c : Color (Fin n)) : (fullOriginalParentRecord H c).length = n := by
  exact List.length_ofFn

omit [DecidableEq E] in
theorem full_original_record_empty_iff_no_sites
    (H : Fin n → GProgram.G2.OriginalHybridParents N)
    (c : Color (Fin n)) : fullOriginalParentRecord H c = [] ↔ n = 0 := by
  exact List.ofFn_eq_nil_iff

omit [DecidableEq E] in
/-- Equality of actually measured complete records cannot camouflage a
change of site count, even with different records' site families. -/
theorem equal_complete_original_records_same_site_count
    (H : Fin n → GProgram.G2.OriginalHybridParents N)
    (J : Fin m → GProgram.G2.OriginalHybridParents N)
    (c : Color (Fin n)) (d : Color (Fin m))
    (h : fullOriginalParentRecord H c = fullOriginalParentRecord J d) : n = m := by
  simpa only [full_original_record_length] using congrArg List.length h

theorem full_original_record_injective
    (H : Fin n → GProgram.G2.OriginalHybridParents N) :
    Function.Injective (fullOriginalParentRecord H) := by
  intro c d h
  exact complete_original_parent_readout_injective H (List.ofFn_injective h)

/-- Positivity is imported from actual positive cell weights, not inferred
from an unrestricted fitted color distribution. -/
theorem original_itinerary_mass_positive
    (cells : Fin n → Cell) (c : Color (Fin n)) :
    0 < oneRootData cells c := by
  rw [oneRootData_eq]
  exact itineraryMass_pos cells c

/-- The complete natural one-root source PMF supports every itinerary. -/
theorem original_itinerary_PMF_full_support (cells : Fin n → Cell) :
    (sourceItineraryPMF cells).support = Set.univ := by
  ext c
  simp only [Set.mem_univ, iff_true, PMF.mem_support_iff]
  change ENNReal.ofReal (itineraryMass cells c) ≠ 0
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (itineraryMass_pos cells c))

/-- A finite enumeration of the supported measured ORIGINAL records.
All labels come from the same original parent map. -/
noncomputable def supportedOriginalRecords
    (H : Fin n → GProgram.G2.OriginalHybridParents N)
    (cells : Fin n → Cell) : Finset (List E) := by
  classical
  exact (Finset.univ.filter (fun c : Color (Fin n) => 0 < oneRootData cells c)).image
    (fullOriginalParentRecord H)

/-- Independently of C4, exact one-root support size is 2^n. This makes the
claimed added ordinary-detection power redundant in this changed menu. -/
theorem supported_original_records_card
    (H : Fin n → GProgram.G2.OriginalHybridParents N)
    (cells : Fin n → Cell) : (supportedOriginalRecords H cells).card = 2 ^ n := by
  classical
  have hf : (Finset.univ.filter
      (fun c : Color (Fin n) => 0 < oneRootData cells c)) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro c _
    exact original_itinerary_mass_positive cells c
  unfold supportedOriginalRecords
  rw [hf, Finset.card_image_of_injective _ (full_original_record_injective H)]
  simp [Color]

end NativeItineraryAudit

#print axioms checked_evidence_has_actual_proof
#print axioms hand_receipt_is_metadata
#print axioms joint_implies_rowwise
#print axioms rowwise_does_not_imply_joint
#print axioms one_witness_budget_iff
#print axioms imageDecisionFromOneWitnessBudget
#print axioms non_escape_implies_every_prefix
#print axioms every_prefix_budget_does_not_imply_non_escape
#print axioms fixed_target_implies_every_cap
#print axioms finite_determination_excludes_fixed_camouflage
#print axioms threshold_every_cap_collision
#print axioms threshold_each_target_finitely_determined
#print axioms every_cap_does_not_imply_fixed_target
#print axioms sufficient_does_not_imply_sharp
#print axioms full_original_record_length
#print axioms full_original_record_empty_iff_no_sites
#print axioms equal_complete_original_records_same_site_count
#print axioms full_original_record_injective
#print axioms original_itinerary_mass_positive
#print axioms original_itinerary_PMF_full_support
#print axioms supported_original_records_card

end UnifiedLean.Audits.ResearchGoalAudit
