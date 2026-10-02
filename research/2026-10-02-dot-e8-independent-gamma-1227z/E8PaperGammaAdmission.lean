import UnifiedLean.Source.E8PaperObservableBridge
import E8SCFG2RuntimeChildAdapter
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Independent CParty paper ensemble and root-emission admission

The paper carrier below is defined from bases, base-pair matching, the fixed
planar scaffold, independently planar extension, the paper's maximal-band
crossing-component density bound, and hard unpaired positions. It is NOT the
source trace type renamed as RNA. CParty sections2.1--2.3 and4 are the prior
specification/correctness theorem; their applicability to the re-expressed
C++ generator remains a source obligation.

Generated source emissions follow the pinned helper's four parent families
(V, VP, VP_CLOSED, VP_DIRECT), excluding fixed scaffold pairs. The source event
stream and 1-based-to-Fin conversion still require an actual execution decoder.
Endpoint ownership, planar extension, density, exhaustive/unambiguous support,
physical factors and the actual classifier remain separately visible premises.

An independent energy specification returns None for an excluded/infinite-
energy object. Its weight is zero. A positive-support correspondence plus a
proved PAPER zero complement transports the law to the entire raw paper
carrier, without silently identifying that carrier with source traces.
-/

noncomputable section
open scoped BigOperators
namespace UnifiedLean.Source.E8PaperGammaAdmission
open E8FiniteTracebackLaw E8SupportedTracebackLaw E8SCFG2RuntimeChildAdapter
open UnifiedLean.Source.E8PaperObservableBridge

inductive Base where
  | A | C | G | U
  deriving DecidableEq

open scoped Classical

abbrev Pair (n : ℕ) := Fin n × Fin n
abbrev Structure (n : ℕ) := Finset (Pair n)

def CanonicalPair (a b : Base) : Prop :=
  (a = .A ∧ b = .U) ∨ (a = .U ∧ b = .A) ∨
  (a = .C ∧ b = .G) ∨ (a = .G ∧ b = .C) ∨
  (a = .G ∧ b = .U) ∨ (a = .U ∧ b = .G)

def EndpointsDisjoint (p q : Pair n) : Prop :=
  p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

def Secondary (sequence : Fin n → Base) (P : Structure n) : Prop :=
  (∀ p ∈ P, p.1 < p.2 ∧ CanonicalPair (sequence p.1) (sequence p.2)) ∧
  (∀ p ∈ P, ∀ q ∈ P, p ≠ q → EndpointsDisjoint p q)

def Cross (p q : Pair n) : Prop :=
  (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨
  (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2)

def Nested (p q : Pair n) : Prop :=
  (p.1 < q.1 ∧ q.2 < p.2) ∨ (q.1 < p.1 ∧ p.2 < q.2)

def Planar (P : Structure n) : Prop := ∀ p ∈ P, ∀ q ∈ P, ¬ Cross p q

def FreshEndpoints (G A : Structure n) : Prop :=
  ∀ p ∈ G, ∀ q ∈ A, EndpointsDisjoint p q

/-- CParty's three band properties, before maximality. The common external
crossing neighbor ensures every member crosses a pair outside the band. -/
def BandCore (P B : Structure n) : Prop :=
  B.Nonempty ∧ B ⊆ P ∧ (∀ p ∈ B, ∀ q ∈ B, p ≠ q → Nested p q) ∧
  (∀ q ∈ P \ B, (∀ p ∈ B, Cross p q) ∨ (∀ p ∈ B, ¬ Cross p q)) ∧
  (∃ q ∈ P \ B, ∀ p ∈ B, Cross p q)

/-- Literal per-member crossing form of the main paper's band properties. -/
def MainBandCore (P B : Structure n) : Prop :=
  B.Nonempty ∧ B ⊆ P ∧ (∀ p ∈ B, ∀ q ∈ B, p ≠ q → Nested p q) ∧
  (∀ q ∈ P \ B, (∀ p ∈ B, Cross p q) ∨ (∀ p ∈ B, ¬ Cross p q)) ∧
  (∀ p ∈ B, ∃ q ∈ P, Cross p q)

def IsBand (P B : Structure n) : Prop :=
  BandCore P B ∧ ∀ C, BandCore P C → B ⊆ C → C = B

abbrev Band (P : Structure n) := {B : Structure n // IsBand P B}
instance bandFintype (P : Structure n) : Fintype (Band P) := Fintype.ofFinite _

def BandAdjacent (P : Structure n) (B C : Band P) : Prop :=
  B ≠ C ∧ ∃ p ∈ B.val, ∃ q ∈ C.val, Cross p q

def BandConnected (P : Structure n) (B C : Band P) : Prop :=
  Relation.ReflTransGen (BandAdjacent P) B C

/-- Band-density crossing includes the OUTER endpoints, as HFold section2.3,
printed p145 specifies. Ordinary base Cover has a different strict convention. -/
def BandCovers (B : Structure n) (k : Fin n) : Prop :=
  ∃ p ∈ B, p.1 ≤ k ∧ k ≤ p.2

/-- Density-2 is a component-local band coverage bound, not merely the
existence of two planar bracket lanes. -/
def DensityTwo (P : Structure n) : Prop :=
  ∀ B : Band P, ∀ k : Fin n,
    (Finset.univ.filter (fun C : Band P => BandConnected P B C ∧ BandCovers C.val k)).card ≤ 2

def HardAllowed (unpaired : Finset (Fin n)) (P : Structure n) : Prop :=
  ∀ p ∈ P, p.1 ∉ unpaired ∧ p.2 ∉ unpaired

structure PaperInput (n : ℕ) where
  sequence : Fin n → Base
  scaffold : Structure n
  scaffold_secondary : Secondary sequence scaffold
  scaffold_planar : Planar scaffold
  forcedUnpaired : Finset (Fin n)

/-- Independent raw paper output ensemble. No source derivation appears in
this definition. Hard constraints may make the ensemble empty. -/
def Gamma (input : PaperInput n) (P : Structure n) : Prop :=
  ∃ A : Structure n, Secondary input.sequence A ∧ Planar A ∧
    FreshEndpoints input.scaffold A ∧ DensityTwo P ∧
    HardAllowed input.forcedUnpaired P ∧ P = input.scaffold ∪ A

abbrev PaperStructure (input : PaperInput n) := {P : Structure n // Gamma input P}
instance paperStructureFintype (input : PaperInput n) : Fintype (PaperStructure input) :=
  Fintype.ofFinite _

theorem cross_symmetric (p q : Pair n) : Cross p q ↔ Cross q p := by
  simp only [Cross, or_comm]

theorem cross_irrefl (p : Pair n) : ¬ Cross p p := by simp [Cross]

theorem cross_not_nested (p q : Pair n) (h : Nested p q) : ¬ Cross p q := by
  intro hc
  simp only [Nested, Cross, Fin.lt_def] at h hc
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
    rcases hc with ⟨h₃,h₄,h₅⟩ | ⟨h₃,h₄,h₅⟩ <;> omega

theorem endpoints_disjoint_symmetric (p q : Pair n)
    (h : EndpointsDisjoint p q) : EndpointsDisjoint q p :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

theorem secondary_union_of_fresh (sequence : Fin n → Base) (G A : Structure n)
    (hg : Secondary sequence G) (ha : Secondary sequence A)
    (hf : FreshEndpoints G A) : Secondary sequence (G ∪ A) := by
  constructor
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hg.1 p hp
    · exact ha.1 p hp
  · intro p hp q hq hne
    rcases Finset.mem_union.mp hp with hp | hp <;>
      rcases Finset.mem_union.mp hq with hq | hq
    · exact hg.2 p hp q hq hne
    · exact hf p hp q hq
    · exact endpoints_disjoint_symmetric q p (hf q hq p hp)
    · exact ha.2 p hp q hq hne

/-- The main paper's per-member external crossing condition and the coded
common-neighbor condition agree under nonempty/all-or-no hypotheses. -/
theorem common_crossing_neighbor_iff (P B : Structure n) (hne : B.Nonempty)
    (huniform : ∀ q ∈ P \ B,
      (∀ p ∈ B, Cross p q) ∨ (∀ p ∈ B, ¬ Cross p q)) :
    (∃ q ∈ P \ B, ∀ p ∈ B, Cross p q) ↔
      (∀ p ∈ B, ∃ q ∈ P \ B, Cross p q) := by
  constructor
  · rintro ⟨q,hq,hall⟩ p hp
    exact ⟨q,hq,hall p hp⟩
  · intro h
    obtain ⟨p,hp⟩ := hne
    obtain ⟨q,hq,hcross⟩ := h p hp
    rcases huniform q hq with hall | hnone
    · exact ⟨q,hq,hall⟩
    · exact False.elim (hnone p hp hcross)

/-- The code's common external neighbor is equivalent to the paper's
per-member crossing condition; nesting proves that neighbor is external. -/
theorem bandCore_iff_mainBandCore (P B : Structure n) :
    BandCore P B ↔ MainBandCore P B := by
  constructor
  · rintro ⟨hne,hsub,hnested,huniform,⟨q,hq,hall⟩⟩
    refine ⟨hne,hsub,hnested,huniform,?_⟩
    intro p hp
    exact ⟨q,(Finset.mem_sdiff.mp hq).1,hall p hp⟩
  · rintro ⟨hne,hsub,hnested,huniform,hmember⟩
    refine ⟨hne,hsub,hnested,huniform,
      (common_crossing_neighbor_iff P B hne huniform).mpr ?_⟩
    intro p hp
    obtain ⟨q,hq,hcross⟩ := hmember p hp
    have hnot : q ∉ B := by
      intro hqb
      by_cases heq : p = q
      · subst q
        exact cross_irrefl p hcross
      · exact cross_not_nested p q (hnested p hp q hqb heq) hcross
    exact ⟨q,Finset.mem_sdiff.mpr ⟨hq,hnot⟩,hcross⟩

/-- Existing finite minimum selection identifies the outer pair of a
nonempty nested band; no arbitrary interval is fitted to its coverage. -/
theorem nested_set_has_outer_pair (B : Structure n) (hne : B.Nonempty)
    (hnested : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → Nested p q) :
    ∃ p ∈ B, ∀ q ∈ B, p.1 ≤ q.1 ∧ q.2 ≤ p.2 := by
  obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image B (fun p : Pair n => p.1) hne
  refine ⟨p,hp,?_⟩
  intro q hq
  refine ⟨hmin q hq,?_⟩
  by_cases heq : p = q
  · subst q
    exact le_refl _
  · rcases hnested p hp q hq heq with ⟨_,hright⟩ | ⟨hleft,_⟩
    · exact hright.le
    · exact False.elim ((not_lt_of_ge (hmin q hq)) hleft)

/-- The coded existential closed span is precisely the OUTER band's closed
span used in HFold's density definition. This is not ordinary base Cover. -/
theorem band_coverage_is_outer_closed_span (P : Structure n) (B : Band P) :
    ∃ p ∈ B.val, (∀ q ∈ B.val, p.1 ≤ q.1 ∧ q.2 ≤ p.2) ∧
      ∀ k : Fin n, BandCovers B.val k ↔ p.1 ≤ k ∧ k ≤ p.2 := by
  obtain ⟨p,hp,houter⟩ := nested_set_has_outer_pair B.val
    B.property.1.1 B.property.1.2.2.1
  refine ⟨p,hp,houter,?_⟩
  intro k
  constructor
  · rintro ⟨q,hq,hleft,hright⟩
    exact ⟨le_trans (houter q hq).1 hleft, le_trans hright (houter q hq).2⟩
  · intro h
    exact ⟨p,hp,h⟩

theorem fresh_implies_pair_disjoint (G A : Structure n) (h : FreshEndpoints G A) :
    Disjoint G A := by
  apply Finset.disjoint_left.mpr
  intro p hp ha
  exact (h p hp p ha).1 rfl

theorem extension_recovered (G A : Structure n) (h : FreshEndpoints G A) :
    (G ∪ A) \ G = A :=
  Finset.union_sdiff_cancel_left (fresh_implies_pair_disjoint G A h)

/-- The fixed scaffold determines its extension uniquely from the final
pair map, independently of a derivation's emission history. -/
theorem gamma_extension_unique (input : PaperInput n) (P A B : Structure n)
    (ha : FreshEndpoints input.scaffold A) (hb : FreshEndpoints input.scaffold B)
    (hpa : P = input.scaffold ∪ A) (hpb : P = input.scaffold ∪ B) : A = B := by
  have ea : P \ input.scaffold = A := by rw [hpa]; exact extension_recovered _ _ ha
  have eb : P \ input.scaffold = B := by rw [hpb]; exact extension_recovered _ _ hb
  exact ea.symm.trans eb

theorem gamma_secondary (input : PaperInput n) (P : Structure n) (h : Gamma input P) :
    Secondary input.sequence P := by
  obtain ⟨A,ha,_,hf,_,_,rfl⟩ := h
  exact secondary_union_of_fresh input.sequence input.scaffold A
    input.scaffold_secondary ha hf

theorem gamma_extension_planar (input : PaperInput n) (P : Structure n) (h : Gamma input P) :
    Planar (P \ input.scaffold) := by
  obtain ⟨A,_,hp,hf,_,_,rfl⟩ := h
  rw [extension_recovered input.scaffold A hf]
  exact hp

/-- Independent intended energy and temperature. None represents exclusion
or non-finite energy. DP09/Vienna correspondence is NOT proved by this record. -/
structure PhysicalEnergy (n : ℕ) where
  energy : Structure n → Option ℝ
  gasConstant : ℝ
  temperature : ℝ
  gasConstant_positive : 0 < gasConstant
  temperature_positive : 0 < temperature

def paperWeight (energy : PhysicalEnergy n) (P : Structure n) : ℝ :=
  match energy.energy P with
  | none => 0
  | some E => Real.exp (-E / (energy.gasConstant * energy.temperature))

theorem paperWeight_nonnegative (energy : PhysicalEnergy n) (P : Structure n) :
    0 ≤ paperWeight energy P := by
  unfold paperWeight
  split
  · exact le_refl 0
  · exact (Real.exp_pos _).le

theorem paperWeight_positive_iff (energy : PhysicalEnergy n) (P : Structure n) :
    0 < paperWeight energy P ↔ ∃ E, energy.energy P = some E := by
  cases h : energy.energy P with
  | none => simp [paperWeight, h]
  | some E => simp [paperWeight, h, Real.exp_pos]

abbrev PositivePaperStructure (input : PaperInput n) (energy : PhysicalEnergy n) :=
  {P : PaperStructure input // 0 < paperWeight energy P.val}
instance positivePaperFintype (input : PaperInput n) (energy : PhysicalEnergy n) :
    Fintype (PositivePaperStructure input energy) := Fintype.ofFinite _

/-- The omitted PAPER complement has zero mass, including independently
specified impossible/constrained/non-finite-energy objects. -/
theorem paper_weight_zero_outside_positive (energy : PhysicalEnergy n) (P : Structure n)
    (h : ¬0 < paperWeight energy P) : paperWeight energy P = 0 :=
  le_antisymm (le_of_not_gt h) (paperWeight_nonnegative energy P)

theorem sum_restrict_positive_paper (input : PaperInput n) (energy : PhysicalEnergy n)
    (f : PaperStructure input → ℝ)
    (hz : ∀ P, paperWeight energy P.val = 0 → f P = 0) :
    (∑ P : PaperStructure input, f P) =
      ∑ P : PositivePaperStructure input energy, f P.val := by
  have h := Finset.sum_congr_set {P : PaperStructure input | 0 < paperWeight energy P.val} f
    (fun P => f P.val) (fun _ _ => rfl)
    (fun P hout => hz P (paper_weight_zero_outside_positive energy P.val hout))
  refine h.trans ?_
  apply Finset.sum_congr
  · ext P
    simp
  · intro _ _
    rfl

/-- Normalized in-range source parent coordinates and actual parent family.
Constructing these from executed 1-based C++ items remains a decoder gate. -/
structure SourceEvent (n : ℕ) where
  family : NonTerminal
  pair : Pair n

def EmitsGenerated (G : Structure n) (e : SourceEvent n) : Prop :=
  (e.family = .V ∨ e.family = .VP ∨ e.family = .VP_CLOSED ∨ e.family = .VP_DIRECT) ∧
    e.pair ∉ G

/-- Pure set semantics of append_deduction_generated_pairs followed by unique
insertion. It does not prove that an arbitrary event list is an executed trace. -/
def generatedPairs (G : Structure n) : List (SourceEvent n) → Structure n
  | [] => ∅
  | e :: es => if EmitsGenerated G e then insert e.pair (generatedPairs G es)
      else generatedPairs G es

def rootOutput (G : Structure n) (events : List (SourceEvent n)) : Structure n :=
  G ∪ generatedPairs G events

theorem generated_pairs_exclude_scaffold (G : Structure n) (events : List (SourceEvent n)) :
    Disjoint G (generatedPairs G events) := by
  induction events with
  | nil => simp [generatedPairs]
  | cons e es ih =>
      rw [generatedPairs]
      split
      · apply Finset.disjoint_insert_right.mpr
        exact ⟨by simpa using (show e.pair ∉ G from (by assumption : EmitsGenerated G e).2), ih⟩
      · exact ih

/-- Distinct source obligations. No equivalence or desired probability-law
identity is a field. The output is fixed by events/family/scaffold, and the
paper carrier is independently fixed by Gamma and PhysicalEnergy. -/
structure RootAdmission {State : Type*} (b : ℕ)
    (factor : State → Fin b → ℝ) (next : State → Fin b → State) (terminal : State → ℝ)
    (d : ℕ) (s : State) (input : PaperInput n) (energy : PhysicalEnergy n) (Class : Type*) where
  events : Trace b d → List (SourceEvent n)
  renderedPairMap : Trace b d → Structure n
  render_lossless : ∀ t : PositiveTrace b factor next terminal d s,
    renderedPairMap t.val = rootOutput input.scaffold (events t.val)
  generated_secondary : ∀ t : PositiveTrace b factor next terminal d s,
    Secondary input.sequence (generatedPairs input.scaffold (events t.val))
  generated_planar : ∀ t : PositiveTrace b factor next terminal d s,
    Planar (generatedPairs input.scaffold (events t.val))
  endpoint_ownership : ∀ t : PositiveTrace b factor next terminal d s,
    FreshEndpoints input.scaffold (generatedPairs input.scaffold (events t.val))
  density_two : ∀ t : PositiveTrace b factor next terminal d s,
    DensityTwo (rootOutput input.scaffold (events t.val))
  hard_constraints : ∀ t : PositiveTrace b factor next terminal d s,
    HardAllowed input.forcedUnpaired (rootOutput input.scaffold (events t.val))
  rootGauge : ℝ
  rootGauge_positive : 0 < rootGauge
  physical_weight : ∀ t : PositiveTrace b factor next terminal d s,
    traceWeight b factor next terminal d s t.val =
      rootGauge * paperWeight energy (rootOutput input.scaffold (events t.val))
  exhaustive : ∀ P : PositivePaperStructure input energy,
    ∃ t : PositiveTrace b factor next terminal d s,
      rootOutput input.scaffold (events t.val) = P.val.val
  unambiguous : Function.Injective (fun t : PositiveTrace b factor next terminal d s =>
    rootOutput input.scaffold (events t.val))
  actualClassify : Trace b d → Class
  paperClassify : Structure n → Class
  classifier_agreement : ∀ t : PositiveTrace b factor next terminal d s,
    actualClassify t.val = paperClassify (renderedPairMap t.val)

section RootBinding
variable {State Class : Type*} (b : ℕ) (factor : State → Fin b → ℝ)
    (next : State → Fin b → State) (terminal : State → ℝ)
    (d : ℕ) (s : State) (input : PaperInput n) (energy : PhysicalEnergy n)
    (admission : RootAdmission b factor next terminal d s input energy Class)

/-- Geometry admission constructs membership in the independent paper
ensemble; that membership is not assumed as one desired-output field. -/
theorem admitted_root_in_gamma (t : PositiveTrace b factor next terminal d s) :
    Gamma input (rootOutput input.scaffold (admission.events t.val)) := by
  exact ⟨generatedPairs input.scaffold (admission.events t.val),
    admission.generated_secondary t, admission.generated_planar t,
    admission.endpoint_ownership t, admission.density_two t,
    admission.hard_constraints t, rfl⟩

theorem admitted_rendered_root_in_gamma (t : PositiveTrace b factor next terminal d s) :
    Gamma input (admission.renderedPairMap t.val) := by
  rw [admission.render_lossless t]
  exact admitted_root_in_gamma b factor next terminal d s input energy admission t

theorem admitted_paper_weight_positive (t : PositiveTrace b factor next terminal d s) :
    0 < paperWeight energy (rootOutput input.scaffold (admission.events t.val)) := by
  by_contra h
  have hprod := mul_nonpos_of_nonneg_of_nonpos admission.rootGauge_positive.le
    (le_of_not_gt h)
  rw [← admission.physical_weight t] at hprod
  exact (not_le_of_gt t.property) hprod

def admittedPositiveOutput (t : PositiveTrace b factor next terminal d s) :
    PositivePaperStructure input energy :=
  ⟨⟨rootOutput input.scaffold (admission.events t.val),
    admitted_root_in_gamma b factor next terminal d s input energy admission t⟩,
      admitted_paper_weight_positive b factor next terminal d s input energy admission t⟩

theorem admittedPositiveOutput_bijective : Function.Bijective
    (admittedPositiveOutput b factor next terminal d s input energy admission) := by
  constructor
  · intro t u h
    apply admission.unambiguous
    exact congrArg (fun P : PositivePaperStructure input energy => P.val.val) h
  · intro P
    obtain ⟨t, h⟩ := admission.exhaustive P
    exact ⟨t, Subtype.ext (Subtype.ext h)⟩

/-- The equivalence is DERIVED from explicit coverage/unique-output source
obligations; it was not supplied as an interpret field or self-model identity. -/
noncomputable def admittedPaperContract :
    SupportedTracePaperContract b factor next terminal d s
      (PositivePaperStructure input energy) Class where
  interpret := Equiv.ofBijective
    (admittedPositiveOutput b factor next terminal d s input energy admission)
    (admittedPositiveOutput_bijective b factor next terminal d s input energy admission)
  paperWeight := fun P => admission.rootGauge * paperWeight energy P.val.val
  actualClassify := admission.actualClassify
  paperClassify := fun P => admission.paperClassify P.val.val
  weight_preserved := admission.physical_weight
  classifier_commutes := by
    intro t
    change admission.actualClassify t.val =
      admission.paperClassify (rootOutput input.scaffold (admission.events t.val))
    rw [admission.classifier_agreement t, admission.render_lossless t]

/-- Conditional root law over the ENTIRE independently specified raw Gamma,
including zero-weight paper objects. Source trace/model/numeric execution and
all RootAdmission fields still require actual-source construction. -/
theorem admitted_root_selected_class_probability [DecidableEq Class]
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (hroot : 0 < partition b factor next terminal d s) (c : Class) :
    (∑ t : Trace b d, if admission.actualClassify t = c then
      traceProbability b factor next terminal d s t else 0) =
      (∑ P : PaperStructure input, if admission.paperClassify P.val = c then
        paperWeight energy P.val else 0) /
      (∑ P : PaperStructure input, paperWeight energy P.val) := by
  have h := supported_trace_paper_class_probability b factor next terminal d s
    (admittedPaperContract b factor next terminal d s input energy admission) hf ht hroot c
  change (∑ t : Trace b d, if admission.actualClassify t = c then
    traceProbability b factor next terminal d s t else 0) =
    (∑ P : PositivePaperStructure input energy, if admission.paperClassify P.val.val = c then
      admission.rootGauge * paperWeight energy P.val.val else 0) /
    (∑ P : PositivePaperStructure input energy, admission.rootGauge * paperWeight energy P.val.val) at h
  have hnum : (∑ P : PositivePaperStructure input energy,
      if admission.paperClassify P.val.val = c then
        admission.rootGauge * paperWeight energy P.val.val else 0) =
      admission.rootGauge * (∑ P : PositivePaperStructure input energy,
        if admission.paperClassify P.val.val = c then paperWeight energy P.val.val else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    split_ifs <;> simp
  have hden : (∑ P : PositivePaperStructure input energy,
      admission.rootGauge * paperWeight energy P.val.val) =
      admission.rootGauge * (∑ P : PositivePaperStructure input energy,
        paperWeight energy P.val.val) := by rw [Finset.mul_sum]
  rw [hnum,hden,mul_div_mul_left _ _ (ne_of_gt admission.rootGauge_positive)] at h
  rw [sum_restrict_positive_paper input energy
    (fun P => if admission.paperClassify P.val = c then paperWeight energy P.val else 0)
    (by intro P hz; simp [hz]),
    sum_restrict_positive_paper input energy
      (fun P => paperWeight energy P.val) (fun _ hz => hz)]
  exact h

end RootBinding

#print axioms cross_symmetric
#print axioms cross_irrefl
#print axioms cross_not_nested
#print axioms endpoints_disjoint_symmetric
#print axioms secondary_union_of_fresh
#print axioms common_crossing_neighbor_iff
#print axioms bandCore_iff_mainBandCore
#print axioms nested_set_has_outer_pair
#print axioms band_coverage_is_outer_closed_span
#print axioms fresh_implies_pair_disjoint
#print axioms extension_recovered
#print axioms gamma_extension_unique
#print axioms gamma_secondary
#print axioms gamma_extension_planar
#print axioms paperWeight_nonnegative
#print axioms paperWeight_positive_iff
#print axioms paper_weight_zero_outside_positive
#print axioms sum_restrict_positive_paper
#print axioms generated_pairs_exclude_scaffold
#print axioms admitted_root_in_gamma
#print axioms admitted_rendered_root_in_gamma
#print axioms admitted_paper_weight_positive
#print axioms admittedPositiveOutput_bijective
#print axioms admitted_root_selected_class_probability
end UnifiedLean.Source.E8PaperGammaAdmission
