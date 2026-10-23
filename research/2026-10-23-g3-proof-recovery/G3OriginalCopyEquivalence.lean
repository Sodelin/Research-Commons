import UnifiedLean.Source.SourceCopyCarrierTransport
import UnifiedLean.Source.SourcePoissonKernel

/-!
UNCOMPILED source candidate, existing G3 owner,22October2026.
Direct bijection on the LITERAL source Snapshot, including dead-slot options.
SourceValid/sample transport and inverse are constructed; original graph,
parent orientation, locations, rate bank and register coordinates stay fixed.
Actual choice/merger/clock transport is constructed below. Numerical M/Phi
and a fresh graph are not assumed. All proof text remains UNCOMPILED.
-/
namespace G3OriginalCopyEquivalence
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open scoped Classical BigOperators

variable {A B C V E X : Type*}
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

theorem labels_inverse (e : A ≃ B) (t : Genealogy A) :
    mapLabels e.symm (mapLabels e t) = t := by
  induction t with
  | leaf x => simp only [mapLabels,Equiv.symm_apply_apply]
  | graft a b iha ihb => simp only [mapLabels,iha,ihb]

noncomputable def copyTree (e : A ≃ B) (t : WellLabelledTree A) : WellLabelledTree B :=
  ⟨mapLabels e t.val,mapLabels_wellLabelled e e.injective t.val t.property⟩

theorem copyTree_inverse (e : A ≃ B) (t : WellLabelledTree A) :
    copyTree e.symm (copyTree e t) = t := by
  apply Subtype.ext
  exact labels_inverse e t.val

theorem label_leaf_iff (e : A ≃ B) (t : Genealogy A) (b : B) :
    b ∈ (mapLabels e t).leaves ↔ e.symm b ∈ t.leaves := by
  rw [mapLabels_leaves]
  constructor
  · intro hb
    obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
    have h := congrArg e.symm hab
    simp only [Equiv.symm_apply_apply] at h
    simpa only [← h] using ha
  · intro hb
    exact Finset.mem_image.mpr ⟨e.symm b,hb,e.apply_symm_apply b⟩

/-- Every raw field is transported, including optional DEAD tree/population
values which the AdmittedSnapshot subtype does not require to be absent. -/
noncomputable def copySnapshot (e : A ≃ B) (s : Snapshot V E A) : Snapshot V E B where
  live := s.live.image e
  ancestor b := e (s.ancestor (e.symm b))
  genealogy b := (s.genealogy (e.symm b)).map (copyTree e)
  population b := s.population (e.symm b)
  register := s.register

theorem copy_live_iff (e : A ≃ B) (s : Snapshot V E A) (b : B) :
    b ∈ (copySnapshot e s).live ↔ e.symm b ∈ s.live := by
  constructor
  · intro hb
    obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
    have h := congrArg e.symm hab
    simp only [Equiv.symm_apply_apply] at h
    simpa only [← h] using ha
  · intro hb
    exact Finset.mem_image.mpr ⟨e.symm b,hb,e.apply_symm_apply b⟩

theorem decode_copy_genealogy (root : V) (e : A ≃ B) (s : Snapshot V E A) (b : B) :
    (decodeSnapshot root (copySnapshot e s)).genealogy b =
      mapLabels e ((decodeSnapshot root s).genealogy (e.symm b)) := by
  cases hg : s.genealogy (e.symm b) with
  | none => simp [decodeSnapshot,copySnapshot,hg,mapLabels]
  | some t => simp [decodeSnapshot,copySnapshot,hg,copyTree]

theorem decode_copy_location (root : V) (e : A ≃ B) (s : Snapshot V E A) (b : B) :
    (decodeSnapshot root (copySnapshot e s)).location b =
      (decodeSnapshot root s).location (e.symm b) := rfl

theorem decode_copy_copyLocation (root : V) (e : A ≃ B) (s : Snapshot V E A) (b : B) :
    copyLocation (decodeSnapshot root (copySnapshot e s)) b =
      copyLocation (decodeSnapshot root s) (e.symm b) := by
  change (decodeSnapshot root (copySnapshot e s)).location
    (e (s.ancestor (e.symm b))) = _
  rw [decode_copy_location,Equiv.symm_apply_apply]
  rfl

theorem copySnapshot_valid (root : V) (e : A ≃ B) (s : Snapshot V E A)
    (hs : Valid (decodeSnapshot root s)) :
    Valid (decodeSnapshot root (copySnapshot e s)) := by
  constructor
  · intro b
    exact Finset.mem_image.mpr
      ⟨s.ancestor (e.symm b),hs.ancestor_live (e.symm b),rfl⟩
  · intro b hb
    have ho := (copy_live_iff e s b).mp hb
    have hr := hs.representative (e.symm b) ho
    change s.ancestor (e.symm b) = e.symm b at hr
    change e (s.ancestor (e.symm b)) = b
    rw [hr,Equiv.apply_symm_apply]
  · intro b hb x
    have ho := (copy_live_iff e s b).mp hb
    rw [decode_copy_genealogy,label_leaf_iff,hs.leaf_fiber (e.symm b) ho (e.symm x)]
    change s.ancestor (e.symm x) = e.symm b ↔ e (s.ancestor (e.symm x)) = b
    constructor
    · intro h
      rw [h,Equiv.apply_symm_apply]
    · intro h
      simpa only [Equiv.symm_apply_apply] using congrArg e.symm h
  · intro b hb
    rw [decode_copy_genealogy]
    exact mapLabels_wellLabelled e e.injective _
      (hs.wellLabelled (e.symm b) ((copy_live_iff e s b).mp hb))

/-- The original taxon carried by each reindexed copy is retained explicitly.
No equality between two different sample functions is asserted. -/
theorem copySnapshot_sourceValid (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Snapshot V E A)
    (hs : SourceValid N sample (decodeSnapshot N.root s)) :
    SourceValid N (fun b => sample (e.symm b)) (decodeSnapshot N.root (copySnapshot e s)) := by
  refine ⟨copySnapshot_valid N.root e s hs.forest,?_⟩
  intro b
  rw [decode_copy_copyLocation]
  exact hs.original_descendant (e.symm b)

theorem copySnapshot_inverse (e : A ≃ B) (s : Snapshot V E A) :
    copySnapshot e.symm (copySnapshot e s) = s := by
  apply Snapshot.ext
  · ext a
    simp only [copy_live_iff,Equiv.symm_symm,Equiv.symm_apply_apply]
  · funext a
    simp only [copySnapshot,Equiv.symm_symm,Equiv.symm_apply_apply]
  · funext a
    simp only [copySnapshot,Equiv.symm_symm,Equiv.symm_apply_apply,Option.map_map]
    cases s.genealogy a with
    | none => rfl
    | some t => exact congrArg some (copyTree_inverse e t)
  · funext a
    simp only [copySnapshot,Equiv.symm_symm,Equiv.symm_apply_apply]
  · rfl

noncomputable def rawSnapshotEquiv (e : A ≃ B) : Snapshot V E A ≃ Snapshot V E B where
  toFun := copySnapshot e
  invFun := copySnapshot e.symm
  left_inv := copySnapshot_inverse e
  right_inv s := by simpa only [Equiv.symm_symm] using copySnapshot_inverse e.symm s

/-- Genuine actual-source carrier equivalence, not a renamed abstract finite
state range. All raw fields are retained and SourceValid is reconstructed. -/
noncomputable def originalCodeEquiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) : Code N sample ≃ Code N (fun b => sample (e.symm b)) where
  toFun s := ⟨copySnapshot e s.val,copySnapshot_sourceValid N e sample s.val s.property⟩
  invFun s := ⟨copySnapshot e.symm s.val,by
    have h := copySnapshot_sourceValid N e.symm (fun b => sample (e.symm b)) s.val s.property
    simpa only [Equiv.symm_symm,Equiv.symm_apply_apply] using h⟩
  left_inv s := by
    apply Subtype.ext
    exact copySnapshot_inverse e s.val
  right_inv s := by
    apply Subtype.ext
    simpa only [Equiv.symm_symm] using copySnapshot_inverse e.symm s.val

theorem originalCodeEquiv_register (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) :
    (state (originalCodeEquiv N e sample s)).register = (state s).register := rfl

theorem originalCodeEquiv_copyLocation (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (b : B) :
    copyLocation (state (originalCodeEquiv N e sample s)) b =
      copyLocation (state s) (e.symm b) :=
  decode_copy_copyLocation N.root e s.val b

/-- A label BIJECTION preserves the existing global source clock budget.
This is unrelated to changing the number of roots or bounding word length. -/
theorem original_globalRateBound_copy_equiv (e : A ≃ B) (r : PositivePairRates E) :
    globalRateBound (Copy := A) r = globalRateBound (Copy := B) r := by
  unfold globalRateBound
  rw [Fintype.card_congr e]

theorem original_globalClockRate_copy_equiv (e : A ≃ B) (r : PositivePairRates E) :
    globalClockRate (Copy := A) r = globalClockRate (Copy := B) r := by
  apply Subtype.ext
  exact original_globalRateBound_copy_equiv e r

theorem originalCodeEquiv_live_iff (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (b : B) :
    b ∈ (state (originalCodeEquiv N e sample s)).live ↔ e.symm b ∈ (state s).live :=
  copy_live_iff e s.val b

theorem originalCodeEquiv_location (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (b : B) :
    (state (originalCodeEquiv N e sample s)).location b =
      (state s).location (e.symm b) :=
  decode_copy_location N.root e s.val b

theorem original_populationRoots_iff (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (place : Location V E) (b : B) :
    b ∈ populationRoots (state (originalCodeEquiv N e sample s)) place ↔
      e.symm b ∈ populationRoots (state s) place := by
  simp only [populationRoots,Finset.mem_filter]
  rw [originalCodeEquiv_live_iff,originalCodeEquiv_location]

/-- Every actual ordered pair retains its original population occurrence.
Only its COPY labels change; both orientations and their half-rates remain. -/
noncomputable def originalChoiceEquiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) :
    Choice N s ≃ Choice N (originalCodeEquiv N e sample s) where
  toFun p := ⟨p.1,⟨(e p.2.val.1,e p.2.val.2),by
    rcases Finset.mem_offDiag.mp p.2.property with ⟨ha,hb,hne⟩
    apply Finset.mem_offDiag.mpr
    refine ⟨?_,?_,fun h => hne (e.injective h)⟩
    · apply (original_populationRoots_iff N e sample s _ _).mpr
      simpa only [Equiv.symm_apply_apply] using ha
    · apply (original_populationRoots_iff N e sample s _ _).mpr
      simpa only [Equiv.symm_apply_apply] using hb⟩⟩
  invFun p := ⟨p.1,⟨(e.symm p.2.val.1,e.symm p.2.val.2),by
    rcases Finset.mem_offDiag.mp p.2.property with ⟨ha,hb,hne⟩
    exact Finset.mem_offDiag.mpr
      ⟨(original_populationRoots_iff N e sample s _ _).mp ha,
       (original_populationRoots_iff N e sample s _ _).mp hb,
       fun h => hne (e.symm.injective h)⟩⟩⟩
  left_inv p := by
    rcases p with ⟨i,⟨⟨a,b⟩,hp⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨i,⟨⟨a,b⟩,hp⟩⟩
    simp only [Equiv.apply_symm_apply]

theorem original_choiceRate_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) (p : Choice N s) :
    choiceRate N r (originalCodeEquiv N e sample s) (originalChoiceEquiv N e sample s p) =
      choiceRate N r s p := rfl

theorem original_totalRate_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) :
    totalRate N r (originalCodeEquiv N e sample s) = totalRate N r s := by
  exact (Equiv.sum_comp (originalChoiceEquiv N e sample s)
    (fun q => choiceRate N r (originalCodeEquiv N e sample s) q)).symm

noncomputable def originalOptionChoiceEquiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) :
    Option (Choice N s) ≃ Option (Choice N (originalCodeEquiv N e sample s)) :=
  Equiv.optionCongr (originalChoiceEquiv N e sample s)

theorem original_choiceMass_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E)
    (q : Option (Choice N s)) :
    choiceMass N r (originalCodeEquiv N e sample s)
      (originalOptionChoiceEquiv N e sample s q) = choiceMass N r s q := by
  cases q with
  | none =>
      change 1-totalRate N r (originalCodeEquiv N e sample s)/globalRateBound (Copy := B) r =
        1-totalRate N r s/globalRateBound (Copy := A) r
      rw [original_totalRate_copy_equiv,← original_globalRateBound_copy_equiv e r]
  | some p =>
      change (pairRate r p.1/2)/globalRateBound (Copy := B) r =
        (pairRate r p.1/2)/globalRateBound (Copy := A) r
      rw [← original_globalRateBound_copy_equiv e r]

/-- Equality of the actual fields read by encodeSnapshot, under the given
copy bijection. This is a proof relation on existing States, not a fitted
Markov carrier. Ranked State.history is outside the Snapshot interface. -/
structure CopyFields (e : A ≃ B) (u : State V E A) (v : State V E B) : Prop where
  live_eq : v.live = u.live.image e
  ancestor_eq : ∀ b, v.ancestor b = e (u.ancestor (e.symm b))
  genealogy_eq : ∀ b, v.genealogy b = mapLabels e (u.genealogy (e.symm b))
  location_eq : ∀ b, v.location b = u.location (e.symm b)
  register_eq : v.register = u.register

theorem decode_copy_fields (root : V) (e : A ≃ B) (s : Snapshot V E A) :
    CopyFields e (decodeSnapshot root s) (decodeSnapshot root (copySnapshot e s)) := by
  exact ⟨rfl,fun _ => rfl,decode_copy_genealogy root e s,
    decode_copy_location root e s,rfl⟩

theorem copy_fields_live_iff (e : A ≃ B) (u : State V E A) (v : State V E B)
    (h : CopyFields e u v) (b : B) : b ∈ v.live ↔ e.symm b ∈ u.live := by
  rw [h.live_eq]
  constructor
  · intro hb
    obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
    have he := congrArg e.symm hab
    simp only [Equiv.symm_apply_apply] at he
    simpa only [← he] using ha
  · intro hb
    exact Finset.mem_image.mpr ⟨e.symm b,hb,e.apply_symm_apply b⟩

/-- Encoding a REAL destination normalizes dead fields on both sides.
This is deliberately separate from rawSnapshotEquiv, which retains them. -/
theorem encode_copy_fields (e : A ≃ B) (u : State V E A) (v : State V E B)
    (hu : Valid u) (hv : Valid v) (h : CopyFields e u v) :
    copySnapshot e (encodeSnapshot u hu) = encodeSnapshot v hv := by
  apply Snapshot.ext
  · exact h.live_eq.symm
  · exact funext (fun b => (h.ancestor_eq b).symm)
  · funext b
    have hm := copy_fields_live_iff e u v h b
    by_cases hb : b ∈ v.live
    · have ha := hm.mp hb
      simp only [copySnapshot,encodeSnapshot,dif_pos ha,dif_pos hb,Option.map_some]
      apply congrArg some
      apply Subtype.ext
      exact (h.genealogy_eq b).symm
    · have ha : e.symm b ∉ u.live := fun ha => hb (hm.mpr ha)
      simp only [copySnapshot,encodeSnapshot,dif_neg ha,dif_neg hb,Option.map_none]
  · funext b
    have hm := copy_fields_live_iff e u v h b
    by_cases hb : b ∈ v.live
    · have ha := hm.mp hb
      simp only [copySnapshot,encodeSnapshot,if_pos ha,if_pos hb]
      exact congrArg some (h.location_eq b).symm
    · have ha : e.symm b ∉ u.live := fun ha => hb (hm.mpr ha)
      simp only [copySnapshot,encodeSnapshot,if_neg ha,if_neg hb]
  · exact h.register_eq.symm

theorem original_admittedCode_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (u : State V E A) (v : State V E B)
    (hu : SourceValid N sample u)
    (hv : SourceValid N (fun b => sample (e.symm b)) v) (h : CopyFields e u v) :
    originalCodeEquiv N e sample (admittedCode N sample u hu) =
      admittedCode N (fun b => sample (e.symm b)) v hv := by
  apply Subtype.ext
  exact encode_copy_fields e u v hu.forest hv.forest h

/-- Literal SourceForest.merge keeps its FIRST ordered representative and
grafts the two actual earlier trees. Both ordered orientations are covered. -/
theorem merge_copy_fields (e : A ≃ B) (u : State V E A) (v : State V E B)
    (h : CopyFields e u v) (a b : A) :
    CopyFields e (merge u a b) (merge v (e a) (e b)) := by
  constructor
  · change v.live.erase (e b) = (u.live.erase b).image e
    rw [h.live_eq]
    ext c
    constructor
    · intro hc
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hc
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_image.mpr ⟨x,
        Finset.mem_erase.mpr ⟨fun he => hne (congrArg e he),hx⟩,rfl⟩
    · intro hc
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr
        ⟨fun he => hne (e.injective he),Finset.mem_image.mpr ⟨x,hm,rfl⟩⟩
  · intro c
    change (if v.ancestor c = e b then e a else v.ancestor c) =
      e (if u.ancestor (e.symm c) = b then a else u.ancestor (e.symm c))
    rw [h.ancestor_eq c]
    by_cases hc : u.ancestor (e.symm c) = b
    · simp only [hc,ite_true]
    · have hce : e (u.ancestor (e.symm c)) ≠ e b := fun he => hc (e.injective he)
      rw [if_neg hce,if_neg hc]
  · intro c
    change (if c = e a then Genealogy.graft (v.genealogy (e a)) (v.genealogy (e b))
      else v.genealogy c) =
      mapLabels e (if e.symm c = a then Genealogy.graft (u.genealogy a) (u.genealogy b)
        else u.genealogy (e.symm c))
    by_cases hc : c = e a
    · subst c
      simp only [ite_true,Equiv.symm_apply_apply,mapLabels]
      rw [h.genealogy_eq (e a),h.genealogy_eq (e b)]
      simp only [Equiv.symm_apply_apply]
    · have hci : e.symm c ≠ a := by
        intro he
        apply hc
        exact (e.apply_symm_apply c).symm.trans (congrArg e he)
      rw [if_neg hc,if_neg hci]
      exact h.genealogy_eq c
  · exact h.location_eq
  · exact h.register_eq

/-- Actual merger coding commutes with relabelling. The none branch keeps
the original RAW Code exactly, including any dead-slot optional fields. -/
theorem original_stepDestination_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (q : Option (Choice N s)) :
    originalCodeEquiv N e sample (stepDestination N s q) =
      stepDestination N (originalCodeEquiv N e sample s)
        (originalOptionChoiceEquiv N e sample s q) := by
  cases q with
  | none => rfl
  | some p =>
      apply Subtype.ext
      change copySnapshot e (encodeSnapshot (merge (state s) p.2.val.1 p.2.val.2) _) =
        encodeSnapshot (merge (state (originalCodeEquiv N e sample s))
          (e p.2.val.1) (e p.2.val.2)) _
      apply encode_copy_fields
      exact merge_copy_fields e _ _ (decode_copy_fields N.root e s.val) _ _

/-- A probability is transported by the literal bijection; there is exactly
one preimage. The full PMF is retained, not merely a diagonal coordinate. -/
theorem pmf_map_equiv_apply {U W : Type*} (f : U ≃ W) (p : PMF U) (w : W) :
    (p.map f) w = p (f.symm w) := by
  classical
  rw [PMF.map_apply]
  have he (u : U) : w = f u ↔ u = f.symm w := by
    constructor
    · intro h
      exact (f.symm_apply_apply u).symm.trans (congrArg f.symm h).symm
    · intro h
      exact (f.apply_symm_apply w).symm.trans (congrArg f h).symm
  simp only [he]
  simp

theorem original_choicePMF_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) :
    (choicePMF N r s).map (originalOptionChoiceEquiv N e sample s) =
      choicePMF N r (originalCodeEquiv N e sample s) := by
  apply PMF.ext
  intro q
  rw [pmf_map_equiv_apply]
  change ENNReal.ofReal (choiceMass N r s
      ((originalOptionChoiceEquiv N e sample s).symm q)) =
    ENNReal.ofReal (choiceMass N r (originalCodeEquiv N e sample s) q)
  have hm := original_choiceMass_copy_equiv N e sample s r
    ((originalOptionChoiceEquiv N e sample s).symm q)
  rw [Equiv.apply_symm_apply] at hm
  exact congrArg ENNReal.ofReal hm.symm

/-- The ACTUAL uniformized source step, including dummy holding and both
orientations of each legal original-population merger, intertwines. -/
theorem original_sourceStep_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) :
    (sourceStep N r s).map (originalCodeEquiv N e sample) =
      sourceStep N r (originalCodeEquiv N e sample s) := by
  simp only [sourceStep,PMF.map_comp]
  rw [← original_choicePMF_copy_equiv N e sample s r,PMF.map_comp]
  congr 1
  funext q
  exact original_stepDestination_copy_equiv N e sample s q

theorem original_sourceIteration_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) (k : Nat) :
    (sourceIteration N r k s).map (originalCodeEquiv N e sample) =
      sourceIteration N r k (originalCodeEquiv N e sample s) := by
  induction k generalizing s with
  | zero => simp only [sourceIteration,PMF.pure_map]
  | succ k ih =>
      simp only [sourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (sourceStep N r s).bind
          ((sourceIteration N r k) ∘ originalCodeEquiv N e sample) =
        (sourceStep N r (originalCodeEquiv N e sample s)).bind (sourceIteration N r k)
      rw [← PMF.bind_map,original_sourceStep_copy_equiv]

/-- A literal full-state time-kernel map at the SAME original global clock.
No finite graph-saturation or number-of-root/word bound is inferred. -/
theorem original_sourceTimeKernel_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) (t : ℝ≥0) :
    (sourceTimeKernel N r t s).map (originalCodeEquiv N e sample) =
      sourceTimeKernel N r t (originalCodeEquiv N e sample s) := by
  simp only [sourceTimeKernel,PMF.map_bind]
  simp_rw [original_sourceIteration_copy_equiv N e sample]
  rw [original_globalClockRate_copy_equiv e r]

#print axioms copySnapshot_sourceValid
#print axioms rawSnapshotEquiv
#print axioms originalCodeEquiv
#print axioms original_globalClockRate_copy_equiv
#print axioms originalChoiceEquiv
#print axioms original_totalRate_copy_equiv
#print axioms original_choiceMass_copy_equiv
#print axioms encode_copy_fields
#print axioms original_stepDestination_copy_equiv
#print axioms original_choicePMF_copy_equiv
#print axioms original_sourceStep_copy_equiv
#print axioms original_sourceTimeKernel_copy_equiv
end G3OriginalCopyEquivalence
