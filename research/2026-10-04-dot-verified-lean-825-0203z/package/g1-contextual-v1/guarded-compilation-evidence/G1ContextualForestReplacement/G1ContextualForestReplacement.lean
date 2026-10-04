import G1OpaqueSourceGrafting

/-!
# Constructed current-entering-root forest interface in arbitrary exteriors

Contributor: dot, 2026-10-03. Accepted G1 is UNRANKED. The source label is
computed from actual original operations, not a supplied simplex/kernel or an
assumed whole-law equality. The outer continuation sees the exact unranked
carried forest and the SAME original register and retained exterior/root
history. All results hold for arbitrary opaque input trees of uncapped size.
Graph extraction, bigon erasure, core bounds and displayed Q/S are separate.
-/
namespace G1ContextualForestReplacement
open Nanuq.Source GProgram.SourceForest
open G1OpaqueSourceGrafting
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical NNReal
variable {V E X Root Desc : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Root] [Fintype Root] [DecidableEq Desc]

/-- Surviving tokens are quotiented to their complete rooted unranked trees;
survivor implementation IDs and child ordering are absent from this interface. -/
noncomputable def rootForest (N : RootedBinary V E X) {sample : Root → X}
    (s : Code N sample) : Finset (UnrankedTree Root) :=
  (state s).live.image (fun l => toUnranked ((state s).genealogy l))

noncomputable def opaqueForest (N : RootedBinary V E X) {sample : Root → X}
    (s : OpaqueState N sample Desc) : Finset (UnrankedTree Desc) :=
  (state s.control).live.image (fun l => toUnranked (s.tree l))

omit [DecidableEq E] [Fintype Root] in
theorem actual_live_root_quotient_grafting (N : RootedBinary V E X) {sample : Root → X}
    (input : Root → Genealogy Desc) (s : Code N sample) :
    opaqueForest N (liftOpaque N input s) = (rootForest N s).image (graftUnranked input) := by
  rw [opaqueForest,rootForest,Finset.image_image]
  apply Finset.image_congr
  intro l hl
  change l ∈ (state s).live at hl
  simp only [liftOpaque,if_pos hl,graftUnranked_toUnranked,Function.comp_apply]

/-- Extracted finite kernel is the actual whole source-program forest law. -/
noncomputable def sourceForestKernel (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    PMF (Finset (UnrankedTree Root)) := (sourceProgram N r ops s).map (rootForest N)

theorem actual_opaque_unranked_forest_law (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (input : Root → Genealogy Desc) (s : Code N sample) :
    (opaqueProgram N r input ops (liftOpaque N input s)).map (opaqueForest N) =
      (sourceForestKernel N r ops s).map (fun F => F.image (graftUnranked input)) := by
  rw [actual_opaque_program_grafting,sourceForestKernel,PMF.map_comp,PMF.map_comp]
  congr 1
  funext d
  exact actual_live_root_quotient_grafting N input d

lemma actual_step_register_retained (N : RootedBinary V E X) {sample : Root → X}
    (s : Code N sample) (p : Option (Choice N s)) :
    (state (stepDestination N s p)).register = (state s).register := by
  cases p <;> rfl

lemma actual_source_step_register_support (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceStep N r s).support) : (state d).register = (state s).register := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hp]
  exact actual_step_register_retained N s p

lemma actual_iteration_register_support (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceIteration N r n s).support) : (state d).register = (state s).register := by
  induction n generalizing s with
  | zero =>
      have he : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      rw [he]
  | succ n ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact (ih z hdz).trans (actual_source_step_register_support N r s hz)

lemma actual_time_register_support (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : (state d).register = (state s).register := by
  obtain ⟨n,_,hdn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_iteration_register_support N r n s hdn

lemma actual_boundary_register_support (N : RootedBinary V E X) {sample : Root → X}
    (op : BoundaryOperation N) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N op s).support) : (state d).register = (state s).register := by
  cases op with
  | exit e =>
      have he : d = exitCode N s e := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; rfl
  | ordinary e degree =>
      have he : d = ordinaryCode N s e := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; rfl
  | root =>
      have he : d = rootCode N s := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; rfl
  | common H =>
      have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d; rfl
  | independent H gamma =>
      obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      rw [← hc]
      rfl

/-- The original exposed/shared register is retained by every actual source
operation, including the entire duration mixture. No fresh marginal resample. -/
theorem actual_program_register_support (N : RootedBinary V E X) {sample : Root → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) : (state d).register = (state s).register := by
  induction ops generalizing s with
  | nil =>
      have he : d = s := by simpa only [sourceProgram,PMF.mem_support_pure_iff] using hd
      rw [he]
  | cons op ops ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      apply (ih z hdz).trans
      cases op with
      | interval t => exact actual_time_register_support N r t s hz
      | boundary b => exact actual_boundary_register_support N b s hz

lemma map_eq_of_eq_on_support {A B : Type*} (p : PMF A) (f g : A → B)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply,PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp only [ha,ite_self]
  · rw [h a ha]

/-- The boundary readout jointly exposes exactly the carried unranked forest,
the same original register, and arbitrary retained exterior/root history. -/
noncomputable def opaqueInterface (N : RootedBinary V E X) {sample : Root → X}
    {History : Type*} (history : History) (s : OpaqueState N sample Desc) :
    History × (V → Bool) × Finset (UnrankedTree Desc) :=
  (history,(state s.control).register,opaqueForest N s)

theorem actual_conditional_interface_law (N : RootedBinary V E X) {sample : Root → X}
    {History : Type*} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (input : Root → Genealogy Desc) (history : History) (s : Code N sample) :
    (opaqueProgram N r input ops (liftOpaque N input s)).map (opaqueInterface N history) =
      (sourceForestKernel N r ops s).map
        (fun F => (history,(state s).register,F.image (graftUnranked input))) := by
  rw [actual_opaque_program_grafting,sourceForestKernel,PMF.map_comp,PMF.map_comp]
  apply map_eq_of_eq_on_support
  intro d hd
  change (history,(state d).register,opaqueForest N (liftOpaque N input d)) = _
  rw [actual_program_register_support N r ops s hd,actual_live_root_quotient_grafting]
  rfl

/-- Full contextual replacement for EVERY causal exterior continuation at
the accepted interface. Neither an output-law identity nor a continuation
equality is supplied as a hypothesis: both sides execute the SAME exterior.
The root history and exposed register can influence every subsequent step. -/
theorem actual_contextual_opaque_forest_replacement
    (N : RootedBinary V E X) {sample : Root → X} {History Obs : Type*}
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (input : Root → Genealogy Desc) (history : History) (s : Code N sample)
    (exterior : History × (V → Bool) × Finset (UnrankedTree Desc) → PMF Obs) :
    (opaqueProgram N r input ops (liftOpaque N input s)).bind
      (fun d => exterior (opaqueInterface N history d)) =
    (sourceForestKernel N r ops s).bind
      (fun F => exterior (history,(state s).register,F.image (graftUnranked input))) := by
  change (opaqueProgram N r input ops (liftOpaque N input s)).bind
    (exterior ∘ opaqueInterface N history) = _
  rw [← PMF.bind_map,actual_conditional_interface_law,PMF.bind_map]
  rfl

/-- Actual one-population component input. Root contains one label for each
CURRENT incoming token, regardless of how many descendants its tree carries. -/
def enteringState (place : Location V E) (register : V → Bool) : State V E Root where
  live := Finset.univ
  ancestor := id
  genealogy := Genealogy.leaf
  location := fun _ => place
  register := register
  history := []

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] in
theorem enteringState_valid (place : Location V E) (register : V → Bool) :
    Valid (enteringState (Root := Root) place register) := by
  constructor
  · intro x; exact Finset.mem_univ x
  · intro l _; rfl
  · intro l _ x; simp [enteringState,Genealogy.leaves,eq_comm]
  · intro l _; trivial

omit [DecidableEq E] in
theorem enteringState_source_valid (N : RootedBinary V E X) (sample : Root → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ l, DescendsTo N place (sample l)) :
    SourceValid N sample (enteringState place register) :=
  ⟨enteringState_valid place register,descendant⟩

noncomputable def enteringCode (N : RootedBinary V E X) (sample : Root → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ l, DescendsTo N place (sample l)) : Code N sample :=
  admittedCode N sample (enteringState place register)
    (enteringState_source_valid N sample place register descendant)

@[simp] theorem enteringCode_live (N : RootedBinary V E X) (sample : Root → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ l, DescendsTo N place (sample l)) :
    (state (enteringCode N sample place register descendant)).live = Finset.univ := rfl

@[simp] theorem enteringCode_register (N : RootedBinary V E X) (sample : Root → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ l, DescendsTo N place (sample l)) :
    (state (enteringCode N sample place register descendant)).register = register := rfl

@[simp] theorem enteringCode_genealogy (N : RootedBinary V E X) (sample : Root → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ l, DescendsTo N place (sample l)) (l : Root) :
    (state (enteringCode N sample place register descendant)).genealogy l = .leaf l := by
  exact decode_encode_live_genealogy N.root _ (enteringState_valid place register) (Finset.mem_univ l)

omit [DecidableEq Desc] in
/-- Before any component operation, the direct source really contains the
supplied opaque trees, rather than fictitious independently pulsed leaves. -/
theorem actual_entering_opaque_tree (N : RootedBinary V E X) (sample : Root → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ l, DescendsTo N place (sample l)) (input : Root → Genealogy Desc) (l : Root) :
    (liftOpaque N input (enteringCode N sample place register descendant)).tree l = input l := by
  simp only [liftOpaque,enteringCode_live,Finset.mem_univ,ite_true,enteringCode_genealogy,graftInput]

/-- The full family K_k is constructed from the actual positive-rate source
and original routing operations at each entering-root count k. Desc does not
occur in its domain, its state dimension, or its normalization. -/
noncomputable def enteringForestKernel (N : RootedBinary V E X) (sample : Root → X)
    (place : Location V E) (descendant : ∀ l, DescendsTo N place (sample l))
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (register : V → Bool) :
    PMF (Finset (UnrankedTree Root)) :=
  sourceForestKernel N r ops (enteringCode N sample place register descendant)

theorem actual_entering_contextual_replacement
    (N : RootedBinary V E X) (sample : Root → X) {History Obs : Type*}
    (place : Location V E) (descendant : ∀ l, DescendsTo N place (sample l))
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (register : V → Bool)
    (input : Root → Genealogy Desc) (history : History)
    (exterior : History × (V → Bool) × Finset (UnrankedTree Desc) → PMF Obs) :
    (opaqueProgram N r input ops
      (liftOpaque N input (enteringCode N sample place register descendant))).bind
      (fun d => exterior (opaqueInterface N history d)) =
    (enteringForestKernel N sample place descendant r ops register).bind
      (fun F => exterior (history,register,F.image (graftUnranked input))) := by
  exact actual_contextual_opaque_forest_replacement N r ops input history
    (enteringCode N sample place register descendant) exterior

/-- Conditioning/integration may correlate incoming opaque forest, original
register and all exterior/root history arbitrarily. The replacement reuses the
very same conditional case and register; it never draws their marginals anew. -/
theorem actual_joint_history_register_replacement
    (N : RootedBinary V E X) (sample : Root → X) {History Obs : Type*}
    (place : Location V E) (descendant : ∀ l, DescendsTo N place (sample l))
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (prior : PMF ((Root → Genealogy Desc) × (V → Bool) × History))
    (exterior : History × (V → Bool) × Finset (UnrankedTree Desc) → PMF Obs) :
    prior.bind (fun c =>
      (opaqueProgram N r c.1 ops
        (liftOpaque N c.1 (enteringCode N sample place c.2.1 descendant))).bind
        (fun d => exterior (opaqueInterface N c.2.2 d))) =
    prior.bind (fun c =>
      (enteringForestKernel N sample place descendant r ops c.2.1).bind
        (fun F => exterior (c.2.2,c.2.1,F.image (graftUnranked c.1)))) := by
  congr 1
  funext c
  exact actual_entering_contextual_replacement N sample place descendant r ops c.2.1 c.1 c.2.2 exterior

omit [DecidableEq E] [DecidableEq Desc] in
theorem opaque_interface_root_cap (N : RootedBinary V E X) {sample : Root → X}
    (s : OpaqueState N sample Desc) :
    (opaqueForest N s).card ≤ Fintype.card Root := by
  exact (Finset.card_image_le).trans (Finset.card_le_univ _)

omit [DecidableEq E] [DecidableEq Desc] in
/-- The accepted cap counts CURRENT input roots, never the leaves of their
previously formed subtrees. This includes the empty entering forest k=0. -/
theorem current_entering_root_cap {k m : Nat} (hkm : k ≤ m)
    (N : RootedBinary V E X) {sample : Fin k → X}
    (s : OpaqueState N sample Desc) : (opaqueForest N s).card ≤ m := by
  have h : (opaqueForest N s).card ≤ k := by
    simpa only [Fintype.card_fin] using opaque_interface_root_cap N s
  exact h.trans hkm

end G1ContextualForestReplacement
