import ActualStoredRegister

/-!
UNCOMPILED source candidate, existing G3 owner,22October2026.
Restore the SAME original private register after an actual no-read prefix,
then run the actual original future. No fresh graph or numerical M is assumed.
No new compiler/model/native job was selected. Source-level proof only.
-/
namespace G3ActualUnusedBankRestore
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterProgram
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open DotG34.ActualStoredRegister
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Nonhybrid private slots return to their actual natural-initializer value.
The bank is indexed by the ORIGINAL private hybrid nodes, not fresh indices. -/
noncomputable def restorePrivateSnapshot (N : RootedBinary V E X) (P : Finset V)
    (seed : PrivateHybrid N P → Bool) (s : Snapshot V E Copy) : Snapshot V E Copy :=
  { s with register := fun v =>
      if hv : v ∈ P then
        if hh : N.graph.IsHybrid v then seed ⟨⟨v,hh⟩,hv⟩ else false
      else s.register v }

theorem restorePrivateSnapshot_sourceValid (N : RootedBinary V E X)
    (sample : Copy → X) (P : Finset V) (seed : PrivateHybrid N P → Bool)
    (s : Snapshot V E Copy) (hs : SourceValid N sample (decodeSnapshot N.root s)) :
    SourceValid N sample (decodeSnapshot N.root (restorePrivateSnapshot N P seed s)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hs.forest.ancestor_live
    · exact hs.forest.representative
    · exact hs.forest.leaf_fiber
    · exact hs.forest.wellLabelled
  · exact hs.original_descendant

noncomputable def restorePrivateCode (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (seed : PrivateHybrid N P → Bool) (s : Code N sample) : Code N sample :=
  ⟨restorePrivateSnapshot N P seed s.val,
    restorePrivateSnapshot_sourceValid N sample P seed s.val s.property⟩

/-- A support identity, not an inverse assertion on arbitrary register values.
All nonhybrid original slots are false in the supplied original register. -/
theorem restore_erase_of_original_register (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (coin : Hybrid N → Bool) (s : Code N sample)
    (hs : (state s).register = originalRegister N coin) :
    restorePrivateCode N P (fun h => coin h.val) (erasePrivateCode N P s) = s := by
  apply Subtype.ext
  apply Snapshot.ext <;> try rfl
  funext v
  have hvreg := congrFun hs v
  change s.val.register v = originalRegister N coin v at hvreg
  change (if hv : v ∈ P then
      if hh : N.graph.IsHybrid v then coin ⟨v,hh⟩ else false
    else if v ∈ P then false else s.val.register v) = s.val.register v
  rw [hvreg]
  by_cases hv : v ∈ P <;> by_cases hh : N.graph.IsHybrid v <;>
    simp [hv,hh,originalRegister]

/-- The required register premise is DERIVED from actual original program
support. This holds even if the prefix itself reads private COMMON bits. -/
theorem actual_prefix_restore (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (coin : Hybrid N → Bool) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (d : Code N sample)
    (hd : d ∈ (sourceProgram N r ops
      (initialCode N sample (originalRegister N coin))).support) :
    restorePrivateCode N P (fun h => coin h.val) (erasePrivateCode N P d) = d := by
  apply restore_erase_of_original_register N P coin d
  exact actual_program_register_support N r ops
    (initialCode N sample (originalRegister N coin)) d hd

private theorem map_eq_on_support {A B : Type*} (p : PMF A) (f g : A → B)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  apply PMF.ext
  intro b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · have hs : a ∈ p.support := by
      change p a ≠ 0
      exact ha
    rw [h a hs]

/-- Actual natural initialization, with its once-drawn original bank label,
followed by the actual original prefix kernel. -/
noncomputable def actualNaturalPrefixJoint (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) : PMF ((PrivateHybrid N P → Bool) × Code N sample) :=
  (naturalInitialJoint N P sample p).bind (fun a =>
    (sourceProgram N r ops a.2).map (fun d => (a.1,d)))

noncomputable def outsidePrefixLaw (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) : PMF (Code N sample) :=
  (outsideInitialCodeLaw N P sample p).bind (sourceProgram N r ops)

/-- Whole-bank product at the actual endpoint. No history endpoint extractor
or source/history identification is assumed. No-read is on the literal word. -/
theorem actual_prefix_joint_product (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops) :
    (actualNaturalPrefixJoint N P sample p r ops).map
      (fun a => (a.1,erasePrivateCode N P a.2)) =
    independentPMF (privateSeedPMF N P p) (outsidePrefixLaw N P sample p r ops) := by
  have hrow (a : (PrivateHybrid N P → Bool) × Code N sample) :
      ((sourceProgram N r ops a.2).map (fun d => (a.1,d))).map
        (fun b => (b.1,erasePrivateCode N P b.2)) =
      (sourceProgram N r ops (erasePrivateCode N P a.2)).map (fun d => (a.1,d)) := by
    rw [PMF.map_comp]
    change (sourceProgram N r ops a.2).map
      ((fun d => (a.1,d)) ∘ erasePrivateCode N P) = _
    rw [← PMF.map_comp,actual_sourceProgram_erasure N r P ops hops a.2]
  rw [actualNaturalPrefixJoint,PMF.map_bind]
  simp_rw [hrow]
  change (naturalInitialJoint N P sample p).bind
    ((fun a : (PrivateHybrid N P → Bool) × Code N sample =>
      (sourceProgram N r ops a.2).map (fun d => (a.1,d))) ∘
      (fun a => (a.1,erasePrivateCode N P a.2))) = _
  rw [← PMF.bind_map,actual_natural_joint_initial_product N P sample p]
  simp only [independentPMF,outsidePrefixLaw,PMF.bind_bind,PMF.bind_map,
    PMF.map_bind,PMF.map_comp,Function.comp_def]

/-- Restoring after actual-prefix erasure is identity on its actual joint
law, including the SAME original seed label and all outside register slots. -/
theorem actual_prefix_restore_joint (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) :
    (actualNaturalPrefixJoint N P sample p r ops).map
      (fun a => (a.1,restorePrivateCode N P a.1 (erasePrivateCode N P a.2))) =
      actualNaturalPrefixJoint N P sample p r ops := by
  simp only [actualNaturalPrefixJoint,naturalInitialJoint,
    PMF.bind_map,PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext coin
  apply map_eq_on_support
  intro d hd
  exact Prod.ext rfl (actual_prefix_restore N P sample coin r ops d hd)

/-- Source-derived disintegration: one independent whole bank plus an
outside prefix Code reconstructs the ACTUAL joint prefix endpoint law. -/
theorem actual_restored_prefix_joint (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops) :
    (independentPMF (privateSeedPMF N P p) (outsidePrefixLaw N P sample p r ops)).map
      (fun a => (a.1,restorePrivateCode N P a.1 a.2)) =
      actualNaturalPrefixJoint N P sample p r ops := by
  rw [← actual_prefix_joint_product N P sample p r ops hops,PMF.map_comp]
  exact actual_prefix_restore_joint N P sample p r ops

/-- The natural seed label is internal; its Code marginal is precisely the
existing natural initializer, not a replacement entering distribution. -/
theorem natural_joint_code_marginal (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) :
    (naturalInitialJoint N P sample p).map Prod.snd = naturalInitialCodeLaw N sample p := by
  simp only [naturalInitialJoint,naturalInitialCodeLaw,originalRegisterPMF,
    PMF.map_comp,Function.comp_def]

theorem actual_prefix_code_marginal (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) :
    (actualNaturalPrefixJoint N P sample p r ops).map Prod.snd =
      (naturalInitialCodeLaw N sample p).bind (sourceProgram N r ops) := by
  simp only [actualNaturalPrefixJoint,PMF.map_bind,PMF.map_comp,Function.comp_def]
  simp only [PMF.map_id]
  change (naturalInitialJoint N P sample p).bind (sourceProgram N r ops ∘ Prod.snd) = _
  rw [← PMF.bind_map,natural_joint_code_marginal N P sample p]

/-- The continuation IS the supplied actual original future kernel. Its
readout may be any map; legal menu admission remains a use-site obligation. -/
theorem actual_restored_future (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops future : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops)
    {Obs : Type*} (readout : Code N sample → Obs) :
    (actualNaturalPrefixJoint N P sample p r ops).bind
      (fun a => (sourceProgram N r future a.2).map readout) =
    (privateSeedPMF N P p).bind (fun seed =>
      (outsidePrefixLaw N P sample p r ops).bind (fun d =>
        (sourceProgram N r future (restorePrivateCode N P seed d)).map readout)) := by
  rw [← actual_restored_prefix_joint N P sample p r ops hops]
  simp only [independentPMF,PMF.bind_map,PMF.bind_bind,Function.comp_def]

theorem sourceProgram_append_same_source (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E)
    (ops future : List (ProgramStep N)) (s : Code N sample) :
    sourceProgram N r (ops ++ future) s =
      (sourceProgram N r ops s).bind (sourceProgram N r future) := by
  induction ops generalizing s with
  | nil => simp only [List.nil_append,sourceProgram,PMF.pure_bind]
  | cons op ops ih =>
      simp only [List.cons_append,sourceProgram,ih,PMF.bind_bind]

/-- Natural original whole-word law: erase through the no-read prefix,
restore the SAME once-drawn bank, then execute the literal actual future.
No no-read condition is imposed on that future; it may use those original
COMMON bits. Nothing is refreshed inside the future or at each private cell. -/
theorem actual_natural_word_after_restore (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops future : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops)
    {Obs : Type*} (readout : Code N sample → Obs) :
    ((naturalInitialCodeLaw N sample p).bind
      (sourceProgram N r (ops ++ future))).map readout =
    (privateSeedPMF N P p).bind (fun seed =>
      (outsidePrefixLaw N P sample p r ops).bind (fun d =>
        (sourceProgram N r future (restorePrivateCode N P seed d)).map readout)) := by
  simp_rw [sourceProgram_append_same_source N r ops future]
  rw [← PMF.bind_bind,← actual_prefix_code_marginal N P sample p r ops,
    PMF.bind_map,PMF.map_bind]
  exact actual_restored_future N P sample p r ops future hops readout

/-- A supplied final stochastic kernel is retained too, for an actual
ancestral completion or admitted observer once its caller binding is given.
This statement does not itself grant legality to an arbitrary finish map. -/
theorem actual_natural_word_after_restore_kernel (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ops future : List (ProgramStep N))
    (hops : NoPrivateWordRead N P ops) {Obs : Type*}
    (finish : Code N sample → PMF Obs) :
    ((naturalInitialCodeLaw N sample p).bind
      (sourceProgram N r (ops ++ future))).bind finish =
    (privateSeedPMF N P p).bind (fun seed =>
      (outsidePrefixLaw N P sample p r ops).bind (fun d =>
        (sourceProgram N r future (restorePrivateCode N P seed d)).bind finish)) := by
  have he := actual_natural_word_after_restore N P sample p r ops future hops
    (fun d : Code N sample => d)
  simp only [PMF.map_id] at he
  rw [he]
  simp only [PMF.bind_bind]

#print axioms restorePrivateSnapshot_sourceValid
#print axioms actual_prefix_restore
#print axioms actual_prefix_joint_product
#print axioms actual_prefix_restore_joint
#print axioms actual_restored_prefix_joint
#print axioms actual_natural_word_after_restore
#print axioms actual_natural_word_after_restore_kernel
end G3ActualUnusedBankRestore
