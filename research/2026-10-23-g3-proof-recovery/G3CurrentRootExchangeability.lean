import G3OriginalCopyBoundary
import G3OriginalSampleParametricity
import G1OriginalCurrentRootReconstruction

/-!
UNCOMPILED source candidate, existing G3 owner,22October2026.
Compose the constructed original copy transport with actual raw-state
sample parametricity. Derive the invariant initializer from EXISTING
enteringState/enteringCode/actualCurrentRootCode. This is not a symmetry
axiom, a numerical M/Phi formula, or a fresh-source/recognition theorem.
-/
namespace G3CurrentRootExchangeability
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open G1OpaqueSourceGrafting G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.UnrankedGenealogyObservation
open G3OriginalCopyEquivalence G3OriginalCopyBoundary G3OriginalSampleParametricity
open scoped Classical

variable {A B V E X : Type*}
variable [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- Both input Codes are ACTUALLY valid in their own sample charts. Equality
of the transported raw input is the only coupling premise. It does not hold
for arbitrary different tip allocations, and no such equality is asserted. -/
theorem actual_program_raw_copy_to_sample (N : RootedBinary V E X) (e : A ≃ B)
    (sampleA : A → X) (sampleB : B → X) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (sA : Code N sampleA) (sB : Code N sampleB)
    (hinit : copySnapshot e sA.val = sB.val) :
    (sourceProgram N r ops sA).map (fun d => copySnapshot e d.val) =
      (sourceProgram N r ops sB).map Subtype.val := by
  calc
    _ = ((sourceProgram N r ops sA).map (originalCodeEquiv N e sampleA)).map
        Subtype.val := by
      rw [PMF.map_comp]
      rfl
    _ = (sourceProgram N r ops (originalCodeEquiv N e sampleA sA)).map
        Subtype.val := by rw [original_program_copy_equiv]
    _ = _ := actual_source_program_raw_sample_transport N
      (fun b => sampleA (e.symm b)) sampleB r ops
      (originalCodeEquiv N e sampleA sA) sB hinit

theorem actual_completed_raw_copy_to_sample (N : RootedBinary V E X) (e : A ≃ B)
    (sampleA : A → X) (sampleB : B → X) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (k : Nat) (sA : Code N sampleA) (sB : Code N sampleB)
    (hinit : copySnapshot e sA.val = sB.val) :
    ((sourceProgram N r ops sA).bind (ancestralCompletion N r k)).map
        (fun d => copySnapshot e d.val) =
      ((sourceProgram N r ops sB).bind (ancestralCompletion N r k)).map Subtype.val := by
  calc
    _ = (((sourceProgram N r ops sA).bind (ancestralCompletion N r k)).map
        (originalCodeEquiv N e sampleA)).map Subtype.val := by
      rw [PMF.map_comp]
      rfl
    _ = ((sourceProgram N r ops (originalCodeEquiv N e sampleA sA)).bind
        (ancestralCompletion N r k)).map Subtype.val := by
      rw [original_completedProgram_copy_equiv]
    _ = _ := actual_completed_program_raw_sample_transport N
      (fun b => sampleA (e.symm b)) sampleB r ops k
      (originalCodeEquiv N e sampleA sA) sB hinit

/-- Direct fields of the EXISTING singleton-current-root initializer. The
original place/register are fixed, and every current root is live. -/
theorem entering_copy_fields (e : A ≃ B) (place : Location V E) (register : V → Bool) :
    CopyFields e (enteringState (Root := A) place register)
      (enteringState (Root := B) place register) := by
  constructor
  · change (Finset.univ : Finset B) = (Finset.univ : Finset A).image e
    ext b
    constructor
    · intro _
      exact Finset.mem_image.mpr ⟨e.symm b,Finset.mem_univ _,e.apply_symm_apply b⟩
    · intro _
      exact Finset.mem_univ b
  · intro b
    exact (e.apply_symm_apply b).symm
  · intro b
    change Genealogy.leaf b = Genealogy.leaf (e (e.symm b))
    exact congrArg Genealogy.leaf (e.apply_symm_apply b).symm
  · intro b
    rfl
  · rfl

/-- No hypothetical raw initializer: these are the literal enteringCodes
already used by the actual current-root/opaque-graft receiver. -/
theorem enteringCode_raw_copy (N : RootedBinary V E X) (e : A ≃ B)
    (sampleA : A → X) (sampleB : B → X) (place : Location V E) (register : V → Bool)
    (descA : ∀ a, DescendsTo N place (sampleA a))
    (descB : ∀ b, DescendsTo N place (sampleB b)) :
    copySnapshot e (enteringCode N sampleA place register descA).val =
      (enteringCode N sampleB place register descB).val := by
  exact encode_copy_fields e _ _ (enteringState_valid place register)
    (enteringState_valid place register) (entering_copy_fields e place register)

/-- Arbitrary bijective current-root carrier, actual original graph and
literal same chronological word. Taxon charts remain explicit and valid. -/
theorem actual_entering_raw_copy_to_sample (N : RootedBinary V E X) (e : A ≃ B)
    (sampleA : A → X) (sampleB : B → X) (place : Location V E) (register : V → Bool)
    (descA : ∀ a, DescendsTo N place (sampleA a))
    (descB : ∀ b, DescendsTo N place (sampleB b))
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    (sourceProgram N r ops (enteringCode N sampleA place register descA)).map
        (fun d => copySnapshot e d.val) =
      (sourceProgram N r ops (enteringCode N sampleB place register descB)).map Subtype.val :=
  actual_program_raw_copy_to_sample N e sampleA sampleB r ops _ _
    (enteringCode_raw_copy N e sampleA sampleB place register descA descB)

theorem actual_entering_raw_exchangeable (N : RootedBinary V E X) (e : A ≃ A)
    (sample : A → X) (place : Location V E) (register : V → Bool)
    (descendant : ∀ a, DescendsTo N place (sample a))
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    (sourceProgram N r ops (enteringCode N sample place register descendant)).map
        (fun d => copySnapshot e d.val) =
      (sourceProgram N r ops (enteringCode N sample place register descendant)).map Subtype.val :=
  actual_entering_raw_copy_to_sample N e sample sample place register
    descendant descendant r ops

/-- Reuses the actual original graph/source current-root constructor; no
all-original-descendants colocation or descendant-count bound is introduced. -/
theorem actual_current_root_raw_exchangeable {Copy : Type*} [DecidableEq Copy] [Fintype Copy]
    (N : RootedBinary V E X) (sample : Copy → X) (s : Code N sample)
    (place : Location V E) (hplace : ∀ l ∈ (state s).live, (state s).location l = place)
    (e : SelectedCopy (state s).live ≃ SelectedCopy (state s).live)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    (sourceProgram N r ops (actualCurrentRootCode N s place hplace)).map
        (fun d => copySnapshot e d.val) =
      (sourceProgram N r ops (actualCurrentRootCode N s place hplace)).map Subtype.val :=
  actual_entering_raw_exchangeable N e (selectedSample sample (state s).live)
    place (state s).register (current_root_descendant N s place hplace) r ops

/-- Existing opaque substitution with a leaf at the new name is exactly
the actual ordered-tree label map, before the child-swap quotient. -/
theorem graft_leaf_labels (e : A ≃ B) (t : Genealogy A) :
    graftInput (fun a => Genealogy.leaf (e a)) t = mapLabels e t := by
  induction t with
  | leaf a => rfl
  | graft a b iha ihb => simp only [graftInput,mapLabels,iha,ihb]

noncomputable def copyForest (e : A ≃ B) (F : Finset (UnrankedTree A)) :
    Finset (UnrankedTree B) := F.image (graftUnranked (fun a => Genealogy.leaf (e a)))

/-- Raw-field spelling of the existing rootForest observer, not a new
finite kernel or a change to the admitted source carrier. -/
noncomputable def rawRootForest (root : V) (s : Snapshot V E A) : Finset (UnrankedTree A) :=
  s.live.image (fun a => toUnranked ((decodeSnapshot root s).genealogy a))

theorem rawRootForest_code (N : RootedBinary V E X) (sample : A → X) (s : Code N sample) :
    rawRootForest N.root s.val = rootForest N s := rfl

theorem rawRootForest_copy (root : V) (e : A ≃ B) (s : Snapshot V E A) :
    rawRootForest root (copySnapshot e s) = copyForest e (rawRootForest root s) := by
  unfold rawRootForest copyForest
  change (s.live.image e).image
      (fun b => toUnranked ((decodeSnapshot root (copySnapshot e s)).genealogy b)) = _
  rw [Finset.image_image,Finset.image_image]
  apply Finset.image_congr
  intro a _
  change toUnranked ((decodeSnapshot root (copySnapshot e s)).genealogy (e a)) =
    graftUnranked (fun a => Genealogy.leaf (e a))
      (toUnranked ((decodeSnapshot root s).genealogy a))
  rw [decode_copy_genealogy,Equiv.symm_apply_apply,graftUnranked_toUnranked,graft_leaf_labels]

/-- Complete ROOTED UNRANKED forest-law exchangeability at the actual
singleton-current-root input, for the supplied whole original word. It
preserves the graph, original rates/parent convention and SAME register. -/
theorem actual_entering_forest_exchangeable (N : RootedBinary V E X) (e : A ≃ A)
    (sample : A → X) (place : Location V E) (register : V → Bool)
    (descendant : ∀ a, DescendsTo N place (sample a))
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    (enteringForestKernel N sample place descendant r ops register).map (copyForest e) =
      enteringForestKernel N sample place descendant r ops register := by
  have h := congrArg (fun law : PMF (Snapshot V E A) => law.map (rawRootForest N.root))
    (actual_entering_raw_exchangeable N e sample place register descendant r ops)
  simpa only [enteringForestKernel,sourceForestKernel,PMF.map_comp,Function.comp_def,
    rawRootForest_copy,rawRootForest_code] using h

#print axioms actual_program_raw_copy_to_sample
#print axioms actual_completed_raw_copy_to_sample
#print axioms enteringCode_raw_copy
#print axioms actual_current_root_raw_exchangeable
#print axioms actual_entering_forest_exchangeable
end G3CurrentRootExchangeability
