import UnifiedLean.Source.SourceProgramTransport
import UnifiedLean.Source.UnrankedGenealogyObservation

/-!
# Opaque entering-root grafting for actual original source operations

Contributor: dot, 2026-10-03. The finite carrier Root labels CURRENT roots at
the component input, not the descendant leaves of the opaque carried trees.
Desc is arbitrary and need not be finite. Explicit opaque mergers, population
moves and current-owner independent/common pulses are compared to the already
constructed positive-rate original source law. No desired law equality is a
source input. Calendar-times are deliberately outside the accepted G1 contract.
-/
namespace G1OpaqueSourceGrafting
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical NNReal

variable {Root Desc : Type*}

/-- Substitute each complete already-formed input tree for its root token. -/
def graftInput (input : Root → Genealogy Desc) : Genealogy Root → Genealogy Desc
  | .leaf l => input l
  | .graft a b => .graft (graftInput input a) (graftInput input b)

theorem graftInput_substitute {Mid : Type*} (f : Root → Genealogy Mid)
    (g : Mid → Genealogy Desc) (t : Genealogy Root) :
    graftInput g (graftInput f t) = graftInput (fun l => graftInput g (f l)) t := by
  induction t with
  | leaf l => rfl
  | graft a b ih1 ih2 => simp only [graftInput, ih1, ih2]

theorem graftInput_unordered [DecidableEq Root] [DecidableEq Desc]
    (input : Root → Genealogy Desc) {a b : Genealogy Root} (h : UnorderedEquiv a b) :
    UnorderedEquiv (graftInput input a) (graftInput input b) := by
  induction h with
  | refl a => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | graft _ _ ih1 ih2 => exact .graft ih1 ih2
  | swap a b => exact .swap _ _

/-- Actual child-swap quotient; no leaf erasure or associativity is added. -/
def graftUnranked [DecidableEq Root] [DecidableEq Desc]
    (input : Root → Genealogy Desc) : UnrankedTree Root → UnrankedTree Desc :=
  Quotient.map (graftInput input) (fun _ _ h => graftInput_unordered input h)

lemma graftUnranked_toUnranked [DecidableEq Root] [DecidableEq Desc]
    (input : Root → Genealogy Desc) (t : Genealogy Root) :
    graftUnranked input (toUnranked t) = toUnranked (graftInput input t) := rfl

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Root] [Fintype Root]

/-- Finite source control plus arbitrarily large carried genealogy trees.
Control contains current live-owner/population/register semantics, while the
opaque trees are evolved independently by the actual merger operations below.
Dead-coordinate garbage is canonicalized and has no output meaning. -/
@[ext] structure OpaqueState (N : RootedBinary V E X) (sample : Root → X) (Desc : Type*) where
  control : Code N sample
  tree : Root → Genealogy Desc

noncomputable def liftOpaque (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) : OpaqueState N sample Desc where
  control := s
  tree l := if l ∈ (state s).live then graftInput input ((state s).genealogy l) else input l

omit [DecidableEq E] [Fintype Root] in
@[simp] lemma liftOpaque_control (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) :
    (liftOpaque N input s).control = s := rfl

/-- The actual direct opaque merger uses the two CURRENT root trees. -/
noncomputable def opaqueDestination (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : OpaqueState N sample Desc) :
    Option (Choice N s.control) → OpaqueState N sample Desc
  | none => s
  | some p =>
      { control := stepDestination N s.control (some p)
        tree l := if l ∈ (state s.control).live.erase p.2.val.2 then
          if l = p.2.val.1 then .graft (s.tree p.2.val.1) (s.tree p.2.val.2) else s.tree l
          else input l }

theorem actual_opaque_merger_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) (p : Option (Choice N s)) :
    opaqueDestination N input (liftOpaque N input s) p =
      liftOpaque N input (stepDestination N s p) := by
  cases p with
  | none => rfl
  | some p =>
      have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
        (originalPlace_not_node N p.1) p.2.property
      apply OpaqueState.ext
      · rfl
      · funext l
        have hg : ∀ z ∈ (merge (state s) p.2.val.1 p.2.val.2).live,
            (state (stepDestination N s (some p))).genealogy z =
              (merge (state s) p.2.val.1 p.2.val.2).genealogy z := by
          intro z hz
          exact decode_encode_live_genealogy N.root _
            (merge_source_valid N sample _ s.property hm).forest hz
        change (if l ∈ (state s).live.erase p.2.val.2 then
          if l = p.2.val.1 then .graft ((liftOpaque N input s).tree p.2.val.1)
            ((liftOpaque N input s).tree p.2.val.2) else (liftOpaque N input s).tree l
          else input l) =
          if l ∈ (state s).live.erase p.2.val.2 then
            graftInput input ((state (stepDestination N s (some p))).genealogy l) else input l
        by_cases hl : l ∈ (state s).live.erase p.2.val.2
        · rw [if_pos hl, if_pos hl, hg l hl]
          by_cases ha : l = p.2.val.1
          · subst l
            simp only [ite_true, liftOpaque, if_pos hm.first_live, if_pos hm.second_live,
              merge, graftInput]
          · simp only [if_neg ha, merge, liftOpaque, if_pos (Finset.mem_erase.mp hl).2]
        · rw [if_neg hl, if_neg hl]

/-- Holding-or-merger weights are actual source rate weights. Descendant-tree
size does not appear in those weights or in their normalization. -/
noncomputable def opaqueStep (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc)
    (s : OpaqueState N sample Desc) : PMF (OpaqueState N sample Desc) :=
  (choicePMF N r s.control).map (opaqueDestination N input s)

theorem actual_opaque_step_grafting (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) (s : Code N sample) :
    opaqueStep N r input (liftOpaque N input s) =
      (sourceStep N r s).map (liftOpaque N input) := by
  rw [opaqueStep, sourceStep, PMF.map_comp]
  congr 1
  funext p
  exact actual_opaque_merger_grafting N input s p

/-- Boundary transports act on original populations and leave carried trees
unchanged. Independent choices are still indexed by CURRENT AtNode owners. -/
noncomputable def opaqueMove (N : RootedBinary V E X) {sample : Root → X}
    (s : OpaqueState N sample Desc) (d : Code N sample) : OpaqueState N sample Desc :=
  ⟨d,s.tree⟩

lemma actual_transport_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample)
    (whereTo : Root → Location V E) (event : SourceEvent V E Root)
    (hs : SourceValid N sample (transport (state s) whereTo event)) :
    opaqueMove N (liftOpaque N input s)
      (admittedCode N sample (transport (state s) whereTo event) hs) =
      liftOpaque N input (admittedCode N sample (transport (state s) whereTo event) hs) := by
  apply OpaqueState.ext
  · rfl
  · funext l
    change (if l ∈ (state s).live then graftInput input ((state s).genealogy l) else input l) =
      if l ∈ (state s).live then
        graftInput input ((decodeSnapshot N.root (encodeSnapshot
          (transport (state s) whereTo event) hs.forest)).genealogy l) else input l
    by_cases hl : l ∈ (state s).live
    · rw [if_pos hl,if_pos hl,decode_encode_live_genealogy N.root _ hs.forest hl]
      rfl
    · rw [if_neg hl,if_neg hl]

lemma exit_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) (e : E) :
    opaqueMove N (liftOpaque N input s) (exitCode N s e) = liftOpaque N input (exitCode N s e) :=
  actual_transport_grafting N input s _ _ (exitEdge_source_valid N sample _ s.property e)

lemma ordinary_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) (e : E) :
    opaqueMove N (liftOpaque N input s) (ordinaryCode N s e) = liftOpaque N input (ordinaryCode N s e) :=
  actual_transport_grafting N input s _ _ (enterEdge_source_valid N sample _ s.property e)

lemma root_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) :
    opaqueMove N (liftOpaque N input s) (rootCode N s) = liftOpaque N input (rootCode N s) :=
  actual_transport_grafting N input s _ _ (enterRoot_source_valid N sample _ s.property)

lemma pulse_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) (H : GProgram.G2.OriginalHybridParents N)
    (coin : AtNode (state s) H.hybrid → Bool) :
    opaqueMove N (liftOpaque N input s) (pulseCode H s coin) = liftOpaque N input (pulseCode H s coin) :=
  actual_transport_grafting N input s _ _ (pulse_source_valid H sample _ s.property coin)

noncomputable def opaqueBoundary (N : RootedBinary V E X) {sample : Root → X}
    (op : BoundaryOperation N) (s : OpaqueState N sample Desc) : PMF (OpaqueState N sample Desc) :=
  match op with
  | .exit e => PMF.pure (opaqueMove N s (exitCode N s.control e))
  | .ordinary e _ => PMF.pure (opaqueMove N s (ordinaryCode N s.control e))
  | .root => PMF.pure (opaqueMove N s (rootCode N s.control))
  | .independent H gamma =>
      (currentCoinPMF (AtNode (state s.control) H.hybrid) gamma).map
        (fun coin => opaqueMove N s (pulseCode H s.control coin))
  | .common H => PMF.pure
      (opaqueMove N s (pulseCode H s.control (fun _ => (state s.control).register H.hybrid)))

theorem actual_opaque_boundary_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) (op : BoundaryOperation N) :
    opaqueBoundary N op (liftOpaque N input s) = (boundaryKernel N op s).map (liftOpaque N input) := by
  cases op with
  | exit e => simp only [opaqueBoundary,boundaryKernel,PMF.pure_map,liftOpaque_control,exit_grafting]
  | ordinary e hd => simp only [opaqueBoundary,boundaryKernel,PMF.pure_map,liftOpaque_control,ordinary_grafting]
  | root => simp only [opaqueBoundary,boundaryKernel,PMF.pure_map,liftOpaque_control,root_grafting]
  | common H => simp only [opaqueBoundary,boundaryKernel,PMF.pure_map,liftOpaque_control,pulse_grafting]
  | independent H gamma =>
      rw [opaqueBoundary,boundaryKernel,independentPulseKernel,PMF.map_comp]
      congr 1
      funext coin
      exact pulse_grafting N input s H coin

noncomputable def opaqueIteration (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) :
    Nat → OpaqueState N sample Desc → PMF (OpaqueState N sample Desc)
  | 0,s => PMF.pure s
  | n+1,s => (opaqueStep N r input s).bind (opaqueIteration N r input n)

theorem actual_opaque_iteration_grafting (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) (n : Nat) (s : Code N sample) :
    opaqueIteration N r input n (liftOpaque N input s) =
      (sourceIteration N r n s).map (liftOpaque N input) := by
  induction n generalizing s with
  | zero => simp only [opaqueIteration,sourceIteration,PMF.pure_map]
  | succ n ih =>
      rw [opaqueIteration,actual_opaque_step_grafting,PMF.bind_map]
      change (sourceStep N r s).bind
        (fun d => opaqueIteration N r input n (liftOpaque N input d)) = _
      simp_rw [ih]
      rw [sourceIteration,PMF.map_bind]

noncomputable def opaqueTimeKernel (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) (t : ℝ≥0)
    (s : OpaqueState N sample Desc) : PMF (OpaqueState N sample Desc) :=
  (countPMF (globalClockRate (Copy := Root) r * t)).bind
    (fun n => opaqueIteration N r input n s)

theorem actual_opaque_time_grafting (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) (t : ℝ≥0) (s : Code N sample) :
    opaqueTimeKernel N r input t (liftOpaque N input s) =
      (sourceTimeKernel N r t s).map (liftOpaque N input) := by
  rw [opaqueTimeKernel,sourceTimeKernel,PMF.map_bind]
  simp_rw [actual_opaque_iteration_grafting]

noncomputable def opaqueProgramStep (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) (op : ProgramStep N)
    (s : OpaqueState N sample Desc) : PMF (OpaqueState N sample Desc) :=
  match op with
  | .interval t => opaqueTimeKernel N r input t s
  | .boundary b => opaqueBoundary N b s

theorem actual_opaque_program_step_grafting (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) (op : ProgramStep N) (s : Code N sample) :
    opaqueProgramStep N r input op (liftOpaque N input s) =
      (sourceProgramStep N r op s).map (liftOpaque N input) := by
  cases op with
  | interval t => exact actual_opaque_time_grafting N r input t s
  | boundary b => exact actual_opaque_boundary_grafting N input s b

noncomputable def opaqueProgram (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc) :
    List (ProgramStep N) → OpaqueState N sample Desc → PMF (OpaqueState N sample Desc)
  | [],s => PMF.pure s
  | op::ops,s => (opaqueProgramStep N r input op s).bind (opaqueProgram N r input ops)

/-- Exact derived law for the independently updated opaque forest source.
No bound or finite enumeration of descendant leaves is used anywhere. -/
theorem actual_opaque_program_grafting (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (input : Root → Genealogy Desc)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    opaqueProgram N r input ops (liftOpaque N input s) =
      (sourceProgram N r ops s).map (liftOpaque N input) := by
  induction ops generalizing s with
  | nil => simp only [opaqueProgram,sourceProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [opaqueProgram,actual_opaque_program_step_grafting,PMF.bind_map]
      change (sourceProgramStep N r op s).bind
        (fun d => opaqueProgram N r input ops (liftOpaque N input d)) = _
      simp_rw [ih]
      rw [sourceProgram,PMF.map_bind]

end G1OpaqueSourceGrafting
