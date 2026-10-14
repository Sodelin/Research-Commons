import G4PairedNaturalTreeCore

namespace DotG4.PairedNaturalTreeCertificate
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open Nanuq.Source GProgram.G5 GProgram.G5.NonbridgeRoutes
open GProgram.G5.AttainedChronology GProgram.G5.ComponentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open DotG4.ActualObservableBankCertificate DotG4.ActualNaturalCombMoments
open DotG4.ActualSelectedPathExposure DotG4.ActualBankFirstMeeting
open scoped Classical BigOperators ENNReal NNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

section EnumeratedCopyTransport
open GProgram.SourceForest GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceEmbeddedJumpLaw UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCompletedUnrankedTree UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceUnrankedCopyProjectivity
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Pure finite label transport needed to identify an enumerated selected
three-copy carrier. No source-law equality is a field of this construction. -/
noncomputable def renameTree (e : A ≃ B) (t : WellLabelledTree A) : WellLabelledTree B :=
  ⟨mapLabels e t.val,mapLabels_wellLabelled e e.injective t.val t.property⟩

noncomputable def renameSnapshot (e : A ≃ B) (s : Snapshot V E A) : Snapshot V E B where
  live := s.live.image e
  ancestor x := e (s.ancestor (e.symm x))
  genealogy x := (s.genealogy (e.symm x)).map (renameTree e)
  population x := s.population (e.symm x)
  register := s.register

lemma renameSnapshot_genealogy (root : V) (e : A ≃ B) (s : Snapshot V E A) (x : B) :
    (decodeSnapshot root (renameSnapshot e s)).genealogy x =
      mapLabels e ((decodeSnapshot root s).genealogy (e.symm x)) := by
  cases h : s.genealogy (e.symm x) with
  | none => simp [decodeSnapshot,renameSnapshot,h,mapLabels]
  | some t => simp [decodeSnapshot,renameSnapshot,h,renameTree]

lemma renameSnapshot_copyLocation (root : V) (e : A ≃ B) (s : Snapshot V E A) (x : B) :
    copyLocation (decodeSnapshot root (renameSnapshot e s)) x =
      copyLocation (decodeSnapshot root s) (e.symm x) := by
  simp only [copyLocation,decodeSnapshot,renameSnapshot,Equiv.symm_apply_apply]

lemma renameSnapshot_valid (root : V) (e : A ≃ B) (s : Snapshot V E A)
    (hs : Valid (decodeSnapshot root s)) : Valid (decodeSnapshot root (renameSnapshot e s)) := by
  constructor
  · intro x
    exact Finset.mem_image.mpr ⟨_,hs.ancestor_live (e.symm x),rfl⟩
  · intro l hl
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    simpa only [decodeSnapshot,renameSnapshot,Equiv.symm_apply_apply] using
      congrArg e (hs.representative k hk)
  · intro l hl x
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    rw [renameSnapshot_genealogy,mapLabels_leaves]
    simp only [Equiv.symm_apply_apply,decodeSnapshot,renameSnapshot]
    constructor
    · intro hx
      obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
      have ha := (hs.leaf_fiber k hk y).mp hy
      subst x
      simpa only [decodeSnapshot,Equiv.symm_apply_apply] using congrArg e ha
    · intro hx
      have ha : (decodeSnapshot root s).ancestor (e.symm x) = k := e.injective hx
      exact Finset.mem_image.mpr ⟨e.symm x,(hs.leaf_fiber k hk _).mpr ha,e.apply_symm_apply x⟩
  · intro l hl
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    rw [renameSnapshot_genealogy,Equiv.symm_apply_apply]
    exact mapLabels_wellLabelled e e.injective _ (hs.wellLabelled k hk)

noncomputable def renameCode (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : Code N (sample ∘ e.symm) :=
  ⟨renameSnapshot e s.val,⟨renameSnapshot_valid N.root e s.val (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest),by
    intro x
    rw [renameSnapshot_copyLocation]
    exact s.property.original_descendant (e.symm x)⟩⟩

lemma renameCode_live (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : (state (renameCode N e s)).live = (state s).live.image e := rfl
lemma renameCode_ancestor (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (x : B) :
    (state (renameCode N e s)).ancestor x = e ((state s).ancestor (e.symm x)) := rfl
lemma renameCode_location (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (x : B) :
    (state (renameCode N e s)).location x = (state s).location (e.symm x) := rfl
lemma renameCode_register (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : (state (renameCode N e s)).register = (state s).register := rfl
lemma renameCode_genealogy (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (x : B) :
    (state (renameCode N e s)).genealogy x = mapLabels e ((state s).genealogy (e.symm x)) :=
  renameSnapshot_genealogy N.root e s.val x

lemma renameCode_population_member (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (place : Location V E) (x : A) :
    e x ∈ populationRoots (state (renameCode N e s)) place ↔ x ∈ populationRoots (state s) place := by
  simp only [populationRoots,Finset.mem_filter,renameCode_live,renameCode_location,Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hx,hplace⟩
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    exact ⟨e.injective he ▸ hy,hplace⟩
  · rintro ⟨hx,hplace⟩
    exact ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,hplace⟩

lemma renameCode_population_pair (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (place : Location V E) (a b : A) :
    (e a,e b) ∈ (populationRoots (state (renameCode N e s)) place).offDiag ↔
      (a,b) ∈ (populationRoots (state s) place).offDiag := by
  simp only [Finset.mem_offDiag,renameCode_population_member,e.injective.ne_iff]

noncomputable def renameChoiceEquiv (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : Choice N s ≃ Choice N (renameCode N e s) where
  toFun p := ⟨p.1,⟨(e p.2.val.1,e p.2.val.2),(renameCode_population_pair N e s _ _ _).mpr p.2.property⟩⟩
  invFun p := ⟨p.1,⟨(e.symm p.2.val.1,e.symm p.2.val.2),by
    apply (renameCode_population_pair N e s _ _ _).mp
    simpa only [Equiv.apply_symm_apply] using p.2.property⟩⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

lemma renameCode_totalRate (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    totalRate N r (renameCode N e s) = totalRate N r s := by
  unfold totalRate
  exact (Fintype.sum_equiv (renameChoiceEquiv N e s) _ _ (fun p => rfl)).symm

lemma rename_globalRateBound (r : PositivePairRates E) (e : A ≃ B) :
    globalRateBound (Copy := B) r = globalRateBound (Copy := A) r := by
  simp only [globalRateBound,Fintype.card_congr e]

lemma renameChoice_mass (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) (q : Option (Choice N s)) :
    choiceMass N r (renameCode N e s) (q.map (renameChoiceEquiv N e s)) = choiceMass N r s q := by
  cases q <;> simp only [Option.map_none,Option.map_some,choiceMass,renameCode_totalRate,
    rename_globalRateBound r e,choiceRate,renameChoiceEquiv] <;> rfl

lemma renameChoice_pmf (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (choicePMF N r s).map (Equiv.optionCongr (renameChoiceEquiv N e s)) = choicePMF N r (renameCode N e s) := by
  apply PMF.ext
  intro b
  rw [map_equiv_mass]
  let q := Equiv.optionCongr (renameChoiceEquiv N e s)
  have hm := renameChoice_mass N r e s (q.symm b)
  have he : (q.symm b).map (renameChoiceEquiv N e s) = b := q.apply_symm_apply b
  rw [he] at hm
  simpa only [choicePMF,PMF.ofFintype_apply] using congrArg ENNReal.ofReal hm.symm

/-- Field-level merger transport isolates raw finite snapshots from dependent
source-choice and source-validity proofs. The actual source instantiation follows. -/
lemma renameSnapshot_merge (σ : A ≃ B) (s : State V E A) (t : State V E B)
    (a b : A) (hv : Valid (merge s a b)) (hv' : Valid (merge t (σ a) (σ b)))
    (hLive : t.live = s.live.image σ)
    (hAnc : ∀ x, t.ancestor x = σ (s.ancestor (σ.symm x)))
    (hTree : ∀ x, t.genealogy x = mapLabels σ (s.genealogy (σ.symm x)))
    (hLoc : ∀ x, t.location x = s.location (σ.symm x))
    (hReg : t.register = s.register) :
    renameSnapshot σ (encodeSnapshot (merge s a b) hv) =
      encodeSnapshot (merge t (σ a) (σ b)) hv' := by
  apply Snapshot.ext
  · simp only [renameSnapshot,encodeSnapshot,merge,hLive]
    exact Finset.image_erase σ.injective _ _
  · funext x
    obtain ⟨y,rfl⟩ := σ.surjective x
    simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
      hAnc,σ.injective.eq_iff]
    split <;> rfl
  · funext x
    obtain ⟨y,rfl⟩ := σ.surjective x
    have hl : σ y ∈ t.live ↔ y ∈ s.live := by
      rw [hLive]
      simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
    by_cases hy : y ∈ s.live.erase b
    · have hy' : σ y ∈ t.live.erase (σ b) := by
        simpa only [Finset.mem_erase,σ.injective.ne_iff,hl] using hy
      simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
        dif_pos hy,dif_pos hy',Option.map_some]
      apply congrArg some
      apply Subtype.ext
      by_cases ha : y = a
      · subst y
        simp only [renameTree,if_pos rfl,hTree,
          Equiv.symm_apply_apply,mapLabels,ite_true]
      · simp only [renameTree,if_neg ha,if_neg (σ.injective.ne_iff.mpr ha),
          hTree,Equiv.symm_apply_apply]
    · have hy' : σ y ∉ t.live.erase (σ b) := by
        simpa only [Finset.mem_erase,σ.injective.ne_iff,hl] using hy
      simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
        dif_neg hy,dif_neg hy',Option.map_none]
  · funext x
    obtain ⟨y,rfl⟩ := σ.surjective x
    have hl : σ y ∈ t.live ↔ y ∈ s.live := by
      rw [hLive]
      simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
    simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
      Finset.mem_erase,σ.injective.ne_iff,hl,hLoc]
  · change s.register = t.register
    exact hReg.symm

lemma renameCode_destination (N : RootedBinary V E X) {sample : A → X}
    (σ : A ≃ B) (s : Code N sample)
    (q : Option (Choice N s)) :
    renameCode N σ (stepDestination N s q) =
      stepDestination N (renameCode N σ s) (q.map (renameChoiceEquiv N σ s)) := by
  cases q with
  | none => rfl
  | some q =>
    apply Subtype.ext
    exact renameSnapshot_merge σ (state s) (state (renameCode N σ s))
      q.2.val.1 q.2.val.2 (actual_choice_merge_valid N s q)
      (actual_choice_merge_valid N (renameCode N σ s) (renameChoiceEquiv N σ s q))
      (renameCode_live N σ s) (renameCode_ancestor N σ s)
      (renameCode_genealogy N σ s) (renameCode_location N σ s) (renameCode_register N σ s)


lemma renameCode_sourceStep (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (sourceStep N r s).map (renameCode N e) = sourceStep N r (renameCode N e s) := by
  unfold sourceStep
  rw [← renameChoice_pmf N r e s,PMF.map_comp,PMF.map_comp]
  congr 1
  funext q
  exact renameCode_destination N e s q

lemma renameCode_iteration (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (k : Nat) (s : Code N sample) :
    (sourceIteration N r k s).map (renameCode N e) = sourceIteration N r k (renameCode N e s) := by
  induction k generalizing s with
  | zero => simp only [sourceIteration,PMF.pure_map]
  | succ k ih =>
    rw [sourceIteration,PMF.map_bind,sourceIteration,← renameCode_sourceStep N r e s,PMF.bind_map]
    congr 1
    funext d
    exact ih d

lemma rename_globalClockRate (r : PositivePairRates E) (e : A ≃ B) :
    globalClockRate (Copy := B) r = globalClockRate (Copy := A) r := by
  apply Subtype.ext
  exact rename_globalRateBound r e

lemma renameCode_time (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (renameCode N e) = sourceTimeKernel N r t (renameCode N e s) := by
  rw [sourceTimeKernel,PMF.map_bind,sourceTimeKernel,rename_globalClockRate r e]
  congr 1
  funext k
  exact renameCode_iteration N r e k s

/-- The corresponding raw transport identity retains every encoded field;
only the prescribed new population functions need to agree after relabelling. -/
lemma renameSnapshot_transport (e : A ≃ B) (s : State V E A) (t : State V E B)
    (f : A → Location V E) (g : B → Location V E)
    (ev : SourceEvent V E A) (ev' : SourceEvent V E B)
    (hv : Valid (transport s f ev)) (hv' : Valid (transport t g ev'))
    (hLive : t.live = s.live.image e)
    (hAnc : ∀ x, t.ancestor x = e (s.ancestor (e.symm x)))
    (hTree : ∀ x, t.genealogy x = mapLabels e (s.genealogy (e.symm x)))
    (hReg : t.register = s.register) (hfg : ∀ x, g (e x) = f x) :
    renameSnapshot e (encodeSnapshot (transport s f ev) hv) =
      encodeSnapshot (transport t g ev') hv' := by
  apply Snapshot.ext
  · exact (hLive).symm
  · funext x
    exact (hAnc x).symm
  · funext x
    obtain ⟨y,rfl⟩ := e.surjective x
    have hl : e y ∈ t.live ↔ y ∈ s.live := by
      rw [hLive]
      simp only [Finset.mem_image,e.injective.eq_iff,exists_eq_right]
    by_cases hy : y ∈ s.live
    · have hy' := hl.mpr hy
      simp only [renameSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,
        dif_pos hy,dif_pos hy',Option.map_some]
      apply congrArg some
      apply Subtype.ext
      simpa only [renameTree,Equiv.symm_apply_apply] using (hTree (e y)).symm
    · have hy' : e y ∉ t.live := mt hl.mp hy
      simp only [renameSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,
        dif_neg hy,dif_neg hy',Option.map_none]
  · funext x
    obtain ⟨y,rfl⟩ := e.surjective x
    have hl : e y ∈ t.live ↔ y ∈ s.live := by
      rw [hLive]
      simp only [Finset.mem_image,e.injective.eq_iff,exists_eq_right]
    simp only [renameSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,hl,hfg]
  · change s.register = t.register
    exact hReg.symm

lemma renameCode_transport (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (f : A → Location V E) (g : B → Location V E)
    (ev : SourceEvent V E A) (ev' : SourceEvent V E B)
    (hv : SourceValid N sample (transport (state s) f ev))
    (hv' : SourceValid N (sample ∘ e.symm) (transport (state (renameCode N e s)) g ev'))
    (hfg : ∀ x, g (e x) = f x) :
    renameCode N e (admittedCode N sample (transport (state s) f ev) hv) =
      admittedCode N (sample ∘ e.symm) (transport (state (renameCode N e s)) g ev') hv' := by
  apply Subtype.ext
  exact renameSnapshot_transport e (state s) (state (renameCode N e s)) f g ev ev'
    hv.forest hv'.forest (renameCode_live N e s) (renameCode_ancestor N e s)
    (renameCode_genealogy N e s) (renameCode_register N e s) hfg

lemma renameCode_exit (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (edge : E) :
    renameCode N e (exitCode N s edge) = exitCode N (renameCode N e s) edge := by
  apply renameCode_transport N e s
  intro x
  simp only [renameCode_location,Equiv.symm_apply_apply]
lemma renameCode_ordinary (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (edge : E) :
    renameCode N e (ordinaryCode N s edge) = ordinaryCode N (renameCode N e s) edge := by
  apply renameCode_transport N e s
  intro x
  simp only [renameCode_location,Equiv.symm_apply_apply]
lemma renameCode_root (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : renameCode N e (rootCode N s) = rootCode N (renameCode N e s) := by
  apply renameCode_transport N e s
  intro x
  simp only [renameCode_location,Equiv.symm_apply_apply]

lemma renameCode_node_member (N : RootedBinary V E X) {sample : A → X}
    (σ : A ≃ B) (s : Code N sample)
    (v : V) (x : A) :
    (σ x ∈ (state (renameCode N σ s)).live ∧ (state (renameCode N σ s)).location (σ x) = .node v) ↔
      (x ∈ (state s).live ∧ (state s).location x = .node v) := by
  simpa only [populationRoots,Finset.mem_filter] using
    renameCode_population_member N σ s (.node v) x

noncomputable def renameNodeEquiv (N : RootedBinary V E X) {sample : A → X}
    (σ : A ≃ B) (s : Code N sample)
    (v : V) : AtNode (state s) v ≃ AtNode (state (renameCode N σ s)) v where
  toFun a := ⟨σ a.val,(renameCode_node_member N σ s v a.val).mpr a.property⟩
  invFun a := ⟨σ.symm a.val,by
    apply (renameCode_node_member N σ s v _).mp
    simpa only [Equiv.apply_symm_apply] using a.property⟩
  left_inv a := by apply Subtype.ext; exact σ.symm_apply_apply a.val
  right_inv a := by apply Subtype.ext; exact σ.apply_symm_apply a.val

lemma renameCode_pulse (N : RootedBinary V E X) {sample : A → X}
    (H : GProgram.G2.OriginalHybridParents N)
    (σ : A ≃ B) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) :
    renameCode N σ (pulseCode H s coin) =
      pulseCode H (renameCode N σ s)
        (GProgram.G7.CoinReindexing.coinTransport (renameNodeEquiv N σ s H.hybrid) coin) := by
  apply renameCode_transport N σ s
  intro x
  by_cases hx : x ∈ (state s).live ∧ (state s).location x = .node H.hybrid
  · have hx' := (renameCode_node_member N σ s H.hybrid x).mpr hx
    simp only [dif_pos hx,dif_pos hx',GProgram.G7.CoinReindexing.coinTransport]
    congr 2
    apply congrArg coin
    apply Subtype.ext
    exact σ.symm_apply_apply x
  · have hx' := mt (renameCode_node_member N σ s H.hybrid x).mp hx
    rw [dif_neg hx',dif_neg hx]
    simpa only [Equiv.symm_apply_apply] using renameCode_location N σ s (σ x)

lemma renameCode_independentPulse (N : RootedBinary V E X) {sample : A → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (σ : A ≃ B) (s : Code N sample) :
    (independentPulseKernel H gamma s).map (renameCode N σ) =
      independentPulseKernel H gamma (renameCode N σ s) := by
  unfold independentPulseKernel
  rw [← GProgram.G7.CoinReindexing.current_coin_pmf (renameNodeEquiv N σ s H.hybrid) gamma,
    PMF.map_comp,PMF.map_comp]
  congr 1
  funext coin
  exact renameCode_pulse N H σ s coin

lemma renameCode_boundary (N : RootedBinary V E X) {sample : A → X}
    (op : BoundaryOperation N) (hop : IndependentBoundary N op) (e : A ≃ B) (s : Code N sample) :
    (boundaryKernel N op s).map (renameCode N e) = boundaryKernel N op (renameCode N e s) := by
  cases op with
  | exit edge => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (renameCode_exit N e s edge)
  | ordinary edge he => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (renameCode_ordinary N e s edge)
  | root => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (renameCode_root N e s)
  | independent H gamma => exact renameCode_independentPulse N H gamma e s
  | common H => exact False.elim hop

lemma renameCode_program (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (hops : IndependentWord N ops)
    (e : A ≃ B) (s : Code N sample) :
    (sourceProgram N r ops s).map (renameCode N e) = sourceProgram N r ops (renameCode N e s) := by
  induction ops generalizing s with
  | nil => simp only [sourceProgram,PMF.pure_map]
  | cons op ops ih =>
    have ht : IndependentWord N ops := fun x hx => hops x (List.mem_cons_of_mem _ hx)
    have hh := hops op (List.mem_cons_self ..)
    cases op with
    | interval t =>
      simp only [sourceProgram,PMF.map_bind,sourceProgramStep]
      rw [← renameCode_time N r e t s,PMF.bind_map]
      congr 1
      funext d
      exact ih ht d
    | boundary b =>
      simp only [sourceProgram,PMF.map_bind,sourceProgramStep]
      rw [← renameCode_boundary N b hh e s,PMF.bind_map]
      congr 1
      funext d
      exact ih ht d

lemma renameChoice_jumpMass (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) (q : Option (Choice N s)) :
    jumpMass N r (renameCode N e s) (q.map (renameChoiceEquiv N e s)) = jumpMass N r s q := by
  cases q <;> simp only [Option.map_none,Option.map_some,jumpMass,renameCode_totalRate,choiceRate,renameChoiceEquiv] <;> rfl

lemma renameChoice_jumpPMF (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (sourceJumpChoice N r s).map (Equiv.optionCongr (renameChoiceEquiv N e s)) =
      sourceJumpChoice N r (renameCode N e s) := by
  apply PMF.ext
  intro b
  rw [map_equiv_mass]
  let q := Equiv.optionCongr (renameChoiceEquiv N e s)
  have hm := renameChoice_jumpMass N r e s (q.symm b)
  have he : (q.symm b).map (renameChoiceEquiv N e s) = b := q.apply_symm_apply b
  rw [he] at hm
  simpa only [sourceJumpChoice,PMF.ofFintype_apply] using congrArg ENNReal.ofReal hm.symm

lemma renameCode_jumpStep (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (sourceJumpStep N r s).map (renameCode N e) = sourceJumpStep N r (renameCode N e s) := by
  unfold sourceJumpStep
  rw [← renameChoice_jumpPMF N r e s,PMF.map_comp,PMF.map_comp]
  congr 1
  funext q
  exact renameCode_destination N e s q

lemma renameCode_completion (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (fuel : Nat) (s : Code N sample) :
    (ancestralCompletion N r fuel s).map (renameCode N e) =
      ancestralCompletion N r fuel (renameCode N e s) := by
  induction fuel generalizing s with
  | zero => simp only [ancestralCompletion,PMF.pure_map]
  | succ fuel ih =>
    rw [ancestralCompletion,PMF.map_bind,ancestralCompletion,← renameCode_jumpStep N r e s,PMF.bind_map]
    congr 1
    funext d
    exact ih d

lemma renameCode_completed_program (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (hops : IndependentWord N ops)
    (e : A ≃ B) (s : Code N sample) :
    ((sourceProgram N r ops s).bind (ancestralCompletion N r (Fintype.card A))).map (renameCode N e) =
      (sourceProgram N r ops (renameCode N e s)).bind (ancestralCompletion N r (Fintype.card B)) := by
  rw [PMF.map_bind,← renameCode_program N r ops hops e s,PMF.bind_map]
  congr 1
  funext d
  rw [renameCode_completion,Fintype.card_congr e]
  rfl

open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler

lemma renameCode_initial (N : RootedBinary V E X) (sample : A → X) (e : A ≃ B) (ρ : V → Bool) :
    renameCode N e (initialCode N sample ρ) = initialCode N (sample ∘ e.symm) ρ := by
  apply Subtype.ext
  apply Snapshot.ext
  · simp [renameCode,renameSnapshot,initialCode,admittedCode,encodeSnapshot,initial]
  · funext x
    simp [renameCode,renameSnapshot,initialCode,admittedCode,encodeSnapshot,initial]
  · funext x
    simp only [renameCode,renameSnapshot,initialCode,admittedCode,encodeSnapshot,initial,
      Finset.mem_univ,dif_pos,Option.map_some]
    apply congrArg some
    apply Subtype.ext
    simp [renameTree,mapLabels]
  · funext x
    simp [renameCode,renameSnapshot,initialCode,admittedCode,encodeSnapshot,initial,Function.comp_apply]
  · rfl

lemma renameCode_fullForest (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) :
    sourceUnrankedForest (state (renameCode N e s)) Finset.univ =
      (sourceUnrankedForest (state s) Finset.univ).image (mapUnranked e) := by
  rw [fullForest_image,fullForest_image,Finset.image_image]
  ext t
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply,
    renameCode_genealogy,renameCode_ancestor,Equiv.symm_apply_apply,mapUnranked_toUnranked]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨e.symm x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨e x,by simpa only [Equiv.symm_apply_apply] using hx⟩

/-- The actual completed independent source law is equivariant under this
explicit copy enumeration, including initialization, original register,
current-owner pulses, ordered mergers and rate-free completion. -/
theorem independent_completed_copy_enumeration (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : A → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (e : A ≃ B) (coin : Hybrid N → Bool) :
    (((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => false))
      (initialCode N sample (originalRegister N coin))).bind
      (ancestralCompletion N r (Fintype.card A))).map
      (fun s => sourceUnrankedForest (state s) Finset.univ)).map
      (fun F => F.image (mapUnranked e)) =
    ((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => false))
      (initialCode N (sample ∘ e.symm) (originalRegister N coin))).bind
      (ancestralCompletion N r (Fintype.card B))).map
      (fun s => sourceUnrankedForest (state s) Finset.univ) := by
  rw [← renameCode_initial N sample e,
    ← renameCode_completed_program N r _ (actual_independent_calendar N C H (originalGamma p)) e,
    PMF.map_comp,PMF.map_comp]
  congr 1
  funext s
  exact (renameCode_fullForest N e s).symm

/-- One original bank average, unchanged by the selected-copy enumeration. -/
theorem natural_independent_copy_enumeration (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : A → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (e : A ≃ B) :
    (naturalCompletedUnrankedLaw N C sample H p (fun _ => false) r).map
      (fun F => F.image (mapUnranked e)) =
      naturalCompletedUnrankedLaw N C (sample ∘ e.symm) H p (fun _ => false) r := by
  unfold naturalCompletedUnrankedLaw naturalCompletedLaw naturalCalendarLaw originalRegisterPMF
  rw [PMF.bind_map,PMF.bind_bind,PMF.map_bind,PMF.map_bind,
    PMF.bind_map,PMF.bind_bind,PMF.map_bind]
  congr 1
  funext coin
  exact independent_completed_copy_enumeration N C sample H p r e coin

end EnumeratedCopyTransport

section SharedLegalQueries
open UnifiedLean.Source.UniformizedSourceStep G1CutChildPorts
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceUnrankedCopyProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceUnrankedAllPanels GProgram.G2.LiteralTimedObservationPruning
open DotG4.ActualLegalPanelComb DotG34.SpecifiedCombEvent
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- The all-taxon observed forest is pruned by an explicit passive function;
its selected three-copy event is identified by a proved source enumeration. -/
lemma actual_selected_independent_crossed (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (sample : Copy → X) (keep : Finset Copy) (e : Fin 3 ≃ SelectedCopy keep) (i j : X)
    (he : ∀ a, sample (e a).val = tripleSample i j a) :
    ((naturalCompletedUnrankedLaw N C sample H p (fun _ => false) r).map (pruneForest keep))
      ((({threeCherry 0} : Finset (UnrankedTree (Fin 3))).image (mapUnranked e)).image
        (mapUnranked Subtype.val)) = naturalCrossedMass N C H p r (fun _ => false) i j := by
  have hobs : (naturalCompletedUnrankedLaw N C sample H p (fun _ => false) r).map (pruneForest keep) =
      (naturalCompletedUnrankedLaw N C (selectedSample sample keep) H p (fun _ => false) r).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
    calc
      _ = (naturalCompletedLaw N C sample H p (fun _ => false) r).map
          (fun s => sourceUnrankedForest (state s) keep) := by
        unfold naturalCompletedUnrankedLaw
        rw [PMF.map_comp]
        congr 1
        funext s
        exact prune_source_forest (state s) (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest) keep
      _ = _ := actual_complete_unranked_all_panel_projectivity N C sample keep H p (fun _ => false) r
  have hs : tripleSample i j ∘ e.symm = selectedSample sample keep := by
    funext x
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,selectedSample] using (he (e.symm x)).symm
  have hn := natural_independent_copy_enumeration N C (tripleSample i j) H p r e
  rw [hs] at hn
  rw [hobs,pmf_map_injective_mass _ _
    (Finset.image_injective (selected_mapUnranked_injective keep (e 0))),← hn]
  have hinj : Function.Injective (mapUnranked e) :=
    (mapUnranked_leftInverse e e.symm (fun x => e.symm_apply_apply x)).injective
  rw [pmf_map_injective_mass _ _ (Finset.image_injective hinj)]
  rfl

noncomputable def sharedSample (i : X) (m : Nat) : X ⊕ Fin m → X := Sum.elim id (fun _ => i)

def sharedEmbedding (i j : X) (m : Nat) : Fin m ⊕ Bool → X ⊕ Fin m
  | .inl a => .inr a
  | .inr true => .inl i
  | .inr false => .inl j

lemma sharedEmbedding_injective (i j : X) (hij : i ≠ j) (m : Nat) :
    Function.Injective (sharedEmbedding i j m) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => simpa only [sharedEmbedding,Sum.inr.injEq,Sum.inl.injEq] using h
    | inr b => cases b <;> simp [sharedEmbedding] at h
  | inr a => cases b with
    | inl b => cases a <;> simp [sharedEmbedding] at h
    | inr b => cases a <;> cases b <;> simp_all [sharedEmbedding,Ne.symm hij]

noncomputable def sharedKeep (i j : X) (m : Nat) : Finset (X ⊕ Fin m) :=
  Finset.univ.image (sharedEmbedding i j m)

noncomputable def sharedSelected (i j : X) (m : Nat) (a : Fin m ⊕ Bool) : SelectedCopy (sharedKeep i j m) :=
  ⟨sharedEmbedding i j m a,Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩⟩
noncomputable def sharedB (i j : X) (m : Nat) : SelectedCopy (sharedKeep i j m) :=
  sharedSelected i j m (.inr false)
noncomputable def sharedA (i j : X) (m : Nat) : List (SelectedCopy (sharedKeep i j m)) :=
  (List.finRange m).map (fun a => sharedSelected i j m (.inl a)) ++ [sharedSelected i j m (.inr true)]

lemma sharedSelected_injective (i j : X) (hij : i ≠ j) (m : Nat) :
    Function.Injective (sharedSelected i j m) := by
  intro a b h
  exact sharedEmbedding_injective i j hij m (congrArg Subtype.val h)

lemma shared_cover (i j : X) (m : Nat) (x : SelectedCopy (sharedKeep i j m)) :
    x = sharedB i j m ∨ x ∈ sharedA i j m := by
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp x.property
  have hx : x = sharedSelected i j m a := Subtype.ext he.symm
  rw [hx]
  cases a with
  | inl a => exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨a,List.mem_finRange a,rfl⟩))
  | inr a => cases a <;> simp [sharedB,sharedA]

lemma shared_A_samples (i j : X) (hij : i ≠ j) (m : Nat)
    (x : SelectedCopy (sharedKeep i j m)) (hx : x ≠ sharedB i j m) : sharedSample i m x.val = i := by
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp x.property
  have hxe : x = sharedSelected i j m a := Subtype.ext he.symm
  rw [hxe]
  cases a with
  | inl a => rfl
  | inr a => cases a with
    | true => rfl
    | false => exact False.elim (hx hxe)

lemma sharedA_nodup (i j : X) (hij : i ≠ j) (m : Nat) : (sharedA i j m).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange m).map ((sharedSelected_injective i j hij m).comp Sum.inl_injective),by simp,?_⟩
  intro x hx y hy he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  have hy' : y = sharedSelected i j m (.inr true) := by simpa using hy
  rw [hy'] at he
  have hf := sharedSelected_injective i j hij m he
  cases hf

lemma sharedA_excludes_B (i j : X) (hij : i ≠ j) (m : Nat) : sharedB i j m ∉ sharedA i j m := by
  intro h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨a,ha,he⟩ := List.mem_map.mp h
    have hf := sharedSelected_injective i j hij m he
    cases hf
  · have he : sharedB i j m = sharedSelected i j m (.inr true) := by simpa using h
    have hf := sharedSelected_injective i j hij m he
    cases hf

lemma sharedA_length (i j : X) (m : Nat) : (sharedA i j m).length = m+1 := by simp [sharedA]
lemma sharedA_nonempty (i j : X) (m : Nat) : sharedA i j m ≠ [] := by simp [sharedA]

noncomputable def sharedCombEvent (i j : X) (m : Nat) : Finset (UnrankedTree (X ⊕ Fin m)) :=
  {toUnranked (comb (sharedB i j m).val ((sharedA i j m).map Subtype.val))}

lemma sharedSample_surjective (i : X) (m : Nat) : Function.Surjective (sharedSample i m) :=
  fun x => ⟨Sum.inl x,rfl⟩

lemma actual_shared_common_comb (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) (m : Nat) :
    (((naturalCompletedUnrankedLaw N C (sharedSample i m) H p (fun _ => true) r).map
      (pruneForest (sharedKeep i j m))) (sharedCombEvent i j m)).toReal =
      DotG4.ActualObservableBankCertificate.combProbability N C H p r i j (m+1) := by
  unfold sharedCombEvent DotG4.ActualObservableBankCertificate.combProbability
  rw [actual_full_panel_selected_comb_moment N C H p r i j (sharedSample i m)
    (sharedSample_surjective i m) (sharedKeep i j m) (sharedB i j m) rfl
    (shared_A_samples i j hij m) (sharedA i j m) (shared_cover i j m)
    (sharedA_nodup i j hij m) (sharedA_excludes_B i j hij m) (sharedA_nonempty i j m),
    sharedA_length,actual_natural_completed_comb_moment N C H p r i j (m+1) (by omega)]

noncomputable def sharedTripleMap (i j : X) : Fin 3 → SelectedCopy (sharedKeep i j 1)
  | 0 => sharedSelected i j 1 (.inr true)
  | 1 => sharedSelected i j 1 (.inl 0)
  | 2 => sharedSelected i j 1 (.inr false)

lemma sharedTripleMap_bijective (i j : X) (hij : i ≠ j) :
    Function.Bijective (sharedTripleMap i j) := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hf := sharedSelected_injective i j hij 1 h
    all_goals cases hf
  · intro x
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp x.property
    have hx : sharedSelected i j 1 a = x := Subtype.ext he
    cases a with
    | inl a => fin_cases a; exact ⟨1,hx⟩
    | inr a => cases a with
      | false => exact ⟨2,hx⟩
      | true => exact ⟨0,hx⟩

noncomputable def sharedTripleEquiv (i j : X) (hij : i ≠ j) : Fin 3 ≃ SelectedCopy (sharedKeep i j 1) :=
  Equiv.ofBijective (sharedTripleMap i j) (sharedTripleMap_bijective i j hij)

lemma sharedTriple_sample (i j : X) (hij : i ≠ j) (a : Fin 3) :
    sharedSample i 1 (sharedTripleEquiv i j hij a).val = tripleSample i j a := by
  fin_cases a <;> rfl

lemma sharedTriple_event (i j : X) (hij : i ≠ j) :
    ((({threeCherry 0} : Finset (UnrankedTree (Fin 3))).image
      (mapUnranked (sharedTripleEquiv i j hij))).image (mapUnranked Subtype.val)) =
      sharedCombEvent i j 1 := by
  rw [threeCherry_zero_eq_specified]
  simp only [Finset.image_singleton,mapUnranked_toUnranked,mapLabels_comb,List.map_cons,List.map_nil]
  rfl

lemma actual_shared_independent_crossed (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    (((naturalCompletedUnrankedLaw N C (sharedSample i 1) H p (fun _ => false) r).map
      (pruneForest (sharedKeep i j 1))) (sharedCombEvent i j 1)).toReal =
      independentCrossedProbability N C H p r i j := by
  have h := actual_selected_independent_crossed N C H p r (sharedSample i 1)
    (sharedKeep i j 1) (sharedTripleEquiv i j hij) i j (sharedTriple_sample i j hij)
  rw [sharedTriple_event] at h
  exact congrArg ENNReal.toReal h

/-- Three full-law requests per taxon: COMMON with one extra, COMMON with two
extras, and INDEPENDENT with one extra. No request depends on the other taxon. -/
def pairedQueryExtras (q : Fin 3) : Nat := if q = 1 then 2 else 1

def pairedQueryMode (q : Fin 3) : Bool := if q = 2 then false else true

noncomputable def pairedQueryLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i : X) (q : Fin 3) : PMF (Finset (UnrankedTree (X ⊕ Fin (pairedQueryExtras q)))) :=
  naturalCompletedUnrankedLaw N C (sharedSample i (pairedQueryExtras q)) H p
    (fun _ => pairedQueryMode q) r

lemma pairedQuery_all_taxa (i : X) (q : Fin 3) :
    Function.Surjective (sharedSample i (pairedQueryExtras q)) := sharedSample_surjective i _

lemma pairedQuery_copy_budget (q : Fin 3) :
    Fintype.card (X ⊕ Fin (pairedQueryExtras q)) ≤ Fintype.card X + 2 := by
  fin_cases q <;> simp [pairedQueryExtras]

lemma pairedQuery_menu_budget : Fintype.card (X × Fin 3) = 3 * Fintype.card X := by
  simp [Nat.mul_comm]

/-- A scalar reader of a full shared query; pruning is a function of the
observed unranked forest and does not expose a latent route or bank. -/
noncomputable def pairedQueryReadout (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (q : Fin 3) : ℝ :=
  (((pairedQueryLaw N C H p r i q).map (pruneForest (sharedKeep i j (pairedQueryExtras q))))
    (sharedCombEvent i j (pairedQueryExtras q))).toReal

def LegalPairedCertificate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E) : Prop :=
  ∀ i j, i ≠ j →
    18 * pairedQueryReadout N C H p r i j 1 = (3 * pairedQueryReadout N C H p r i j 0)^3 ∧
    pairedQueryReadout N C H p r i j 2 = pairedQueryReadout N C H p r i j 0

lemma pairedQueryReadout_zero (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    pairedQueryReadout N C H p r i j 0 = combProbability N C H p r i j 2 := by
  exact actual_shared_common_comb N C H p r i j hij 1

lemma pairedQueryReadout_one (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    pairedQueryReadout N C H p r i j 1 = combProbability N C H p r i j 3 := by
  exact actual_shared_common_comb N C H p r i j hij 2

lemma pairedQueryReadout_two (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    pairedQueryReadout N C H p r i j 2 = independentCrossedProbability N C H p r i j := by
  exact actual_shared_independent_crossed N C H p r i j hij

/-- Physical ordinary-tree recognition by the actual legal shared full laws.
No calibrated geometry, route mixture or exchangeable-reader value is an input. -/
theorem actual_legal_paired_certificate_iff_noHybrids
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (hcut : CutChild N) :
    LegalPairedCertificate N C H p r ↔ NoHybrids N := by
  have he : LegalPairedCertificate N C H p r ↔ PairedNaturalCalibration N C H p r := by
    unfold LegalPairedCertificate PairedNaturalCalibration
    apply forall_congr'; intro i
    apply forall_congr'; intro j
    apply imp_congr_right; intro hij
    rw [pairedQueryReadout_zero N C H p r i j hij,pairedQueryReadout_one N C H p r i j hij,
      pairedQueryReadout_two N C H p r i j hij]
  exact he.trans (actual_paired_natural_calibration_iff_noHybrids N C H p r hcut)

variable {V' E' : Type*} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']

lemma pairedQuery_equal_scalar_data
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E')
    (hq : ∀ i q, pairedQueryLaw N' C' H' p' r' i q = pairedQueryLaw N C H p r i q) :
    (∀ i j, i ≠ j → combProbability N' C' H' p' r' i j 2 = combProbability N C H p r i j 2) ∧
    (∀ i j, i ≠ j → combProbability N' C' H' p' r' i j 3 = combProbability N C H p r i j 3) ∧
    (∀ i j, i ≠ j → independentCrossedProbability N' C' H' p' r' i j =
      independentCrossedProbability N C H p r i j) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    have h := congrArg (fun μ => ((μ.map (pruneForest (sharedKeep i j 1))) (sharedCombEvent i j 1)).toReal) (hq i 0)
    change pairedQueryReadout N' C' H' p' r' i j 0 = pairedQueryReadout N C H p r i j 0 at h
    simpa only [pairedQueryReadout_zero N C H p r i j hij,
      pairedQueryReadout_zero N' C' H' p' r' i j hij] using h
  · intro i j hij
    have h := congrArg (fun μ => ((μ.map (pruneForest (sharedKeep i j 2))) (sharedCombEvent i j 2)).toReal) (hq i 1)
    change pairedQueryReadout N' C' H' p' r' i j 1 = pairedQueryReadout N C H p r i j 1 at h
    simpa only [pairedQueryReadout_one N C H p r i j hij,
      pairedQueryReadout_one N' C' H' p' r' i j hij] using h
  · intro i j hij
    have h := congrArg (fun μ => ((μ.map (pruneForest (sharedKeep i j 1))) (sharedCombEvent i j 1)).toReal) (hq i 2)
    change pairedQueryReadout N' C' H' p' r' i j 2 = pairedQueryReadout N C H p r i j 2 at h
    simpa only [pairedQueryReadout_two N C H p r i j hij,
      pairedQueryReadout_two N' C' H' p' r' i j hij] using h

/-- The inherited ordinary-target contract: the three shared all-taxon laws per
taxon force every future natural response in BOTH modes, against arbitrary
finite rival graph carriers. The query budget is proved above, not assumed. -/
theorem actual_ordinary_target_shared_queries_all_future
    (hn4 : 4 ≤ Fintype.card X)
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (hn : NoHybrids N)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E') (hcut' : CutChild N')
    (hq : ∀ i q, pairedQueryLaw N' C' H' p' r' i q = pairedQueryLaw N C H p r i q) :
    ∀ (Copy : Type*) [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
      (common : Hybrid N → Bool) (common' : Hybrid N' → Bool),
      naturalCompletedUnrankedLaw N' C' sample H' p' common' r' =
        naturalCompletedUnrankedLaw N C sample H p common r := by
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨hc,hd,hu⟩ := pairedQuery_equal_scalar_data N C H p r N' C' H' p' r' hq
  exact actual_ordinary_target_paired_all_future N C H p r hn N' C' H' p' r' hcut' hc hd hu

end SharedLegalQueries

end DotG4.PairedNaturalTreeCertificate
