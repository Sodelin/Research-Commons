import UnifiedLean.Source.SourceCopyCarrierTransport
import G7EffectivePopulationCoefficients
import Mathlib.Data.List.Nodup

/-!
dot, 2026-10-22. SOURCE PROPOSAL, UNELABORATED.
Literal copy-carrier transport. This is not the existing vertex/edge relabelling.
No native execution, parser correctness or original Code coverage is assumed.
-/
namespace Dot.CopyCarrierTransport
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.SourceForestKingmanPopulationProjection

variable {V E X A B C : Type*}
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- The actual ordered `copies` list determines the local-to-panel equivalence.
Only no-duplicates and exact coverage are premises, not coefficient equality. -/
noncomputable def listedPanelEquiv (copies : List A) (keep : Finset A)
    (hn : copies.Nodup) (hc : ∀ x, x ∈ copies ↔ x ∈ keep) :
    Fin copies.length ≃ SelectedCopy keep :=
  Equiv.ofBijective
    (fun i => ⟨copies.get i, (hc _).mp (List.mem_iff_get.mpr ⟨i, rfl⟩)⟩)
    ⟨fun i j h => hn.injective_get (congrArg Subtype.val h), by
      intro x
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((hc x.val).mpr x.property)
      exact ⟨i, Subtype.ext hi⟩⟩

theorem listedPanelEquiv_value (copies : List A) (keep : Finset A)
    (hn : copies.Nodup) (hc : ∀ x, x ∈ copies ↔ x ∈ keep) (i : Fin copies.length) :
    (listedPanelEquiv copies keep hn hc i).val = copies.get i := rfl

theorem labels_comp (f : A → B) (g : B → C) (t : Genealogy A) :
    mapLabels g (mapLabels f t) = mapLabels (g ∘ f) t := by
  induction t with
  | leaf x => rfl
  | graft a b ha hb => simp only [mapLabels, ha, hb]

theorem labels_id (t : Genealogy A) : mapLabels id t = t := by
  induction t with
  | leaf x => rfl
  | graft a b ha hb => simp only [mapLabels, ha, hb]

theorem labels_inverse (e : A ≃ B) (t : Genealogy A) :
    mapLabels e.symm (mapLabels e t) = t := by
  rw [labels_comp]
  have h : (e.symm ∘ e : A → A) = id := by funext x; simp
  rw [h, labels_id]

def tree (e : A ≃ B) (t : WellLabelledTree A) : WellLabelledTree B :=
  ⟨mapLabels e t.val, mapLabels_wellLabelled e e.injective t.val t.property⟩

theorem tree_inverse (e : A ≃ B) (t : WellLabelledTree A) :
    tree e.symm (tree e t) = t := by
  apply Subtype.ext
  exact labels_inverse e t.val

def event (e : A ≃ B) : SourceEvent V E A → SourceEvent V E B
  | .merger a b p => .merger (e a) (e b) p
  | .parentPulse v coins => .parentPulse v (fun y => coins (e.symm y))
  | .edgeExit edge => .edgeExit edge
  | .ordinaryEntry edge => .ordinaryEntry edge
  | .rootEntry v => .rootEntry v

noncomputable def state (e : A ≃ B) (s : State V E A) : State V E B where
  live := s.live.image e
  ancestor y := e (s.ancestor (e.symm y))
  genealogy y := mapLabels e (s.genealogy (e.symm y))
  location y := s.location (e.symm y)
  register := s.register
  history := s.history.map (event e)

@[simp] theorem mem_live (e : A ≃ B) (s : State V E A) (x : A) :
    e x ∈ (state e s).live ↔ x ∈ s.live := by
  simp [state]

theorem valid (e : A ≃ B) (s : State V E A) (hs : Valid s) : Valid (state e s) := by
  constructor
  · intro y
    exact Finset.mem_image.mpr
      ⟨s.ancestor (e.symm y), hs.ancestor_live (e.symm y), rfl⟩
  · intro y hy
    have hy' : e.symm y ∈ s.live := by
      have h := (mem_live e s (e.symm y)).mp
      exact h (by simpa using hy)
    change e (s.ancestor (e.symm y)) = y
    rw [hs.representative _ hy', e.apply_symm_apply]
  · intro y hy z
    have hy' : e.symm y ∈ s.live := by
      exact (mem_live e s (e.symm y)).mp (by simpa using hy)
    change z ∈ (mapLabels e (s.genealogy (e.symm y))).leaves ↔
      e (s.ancestor (e.symm z)) = y
    rw [mapLabels_leaves]
    constructor
    · intro hz
      obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
      subst z
      simpa using congrArg e ((hs.leaf_fiber _ hy' x).mp hx)
    · intro hz
      apply Finset.mem_image.mpr
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      apply (hs.leaf_fiber _ hy' _).mpr
      have h := congrArg e.symm hz
      simpa using h
  · intro y hy
    have hy' : e.symm y ∈ s.live :=
      (mem_live e s (e.symm y)).mp (by simpa using hy)
    exact mapLabels_wellLabelled e e.injective _ (hs.wellLabelled _ hy')

@[simp] theorem copy_location (e : A ≃ B) (s : State V E A) (y : B) :
    copyLocation (state e s) y = copyLocation s (e.symm y) := by
  simp [copyLocation, state]

theorem source_valid (N : RootedBinary V E X) (sample : A → X)
    (e : A ≃ B) (s : State V E A) (hs : SourceValid N sample s) :
    SourceValid N (sample ∘ e.symm) (state e s) := by
  refine ⟨valid e s hs.forest, ?_⟩
  intro y
  rw [copy_location]
  exact hs.original_descendant (e.symm y)

noncomputable def snapshot (e : A ≃ B) (s : Snapshot V E A) : Snapshot V E B where
  live := s.live.image e
  ancestor y := e (s.ancestor (e.symm y))
  genealogy y := (s.genealogy (e.symm y)).map (tree e)
  population y := s.population (e.symm y)
  register := s.register

theorem decode_commutes (e : A ≃ B) (root : V) (s : Snapshot V E A) :
    decode root (snapshot e s) = state e (decode root s) := by
  cases s with
  | mk live ancestor genealogy population register =>
    simp only [decode, snapshot, state, List.map_nil]
    congr 1
    funext y
    cases hg : genealogy (e.symm y) with
    | none => simp [mapLabels]
    | some t => rfl

noncomputable def code (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (s : Code N sample) : Code N (sample ∘ e.symm) := by
  refine ⟨snapshot e s.val, ?_⟩
  change SourceValid N (sample ∘ e.symm) (decode N.root (snapshot e s.val))
  rw [decode_commutes]
  exact source_valid N sample e (decode N.root s.val) s.property

/-- Literal full-state coordinates, including the register, are transported.
This is stronger than equality of selected marginal observations. -/
theorem code_state (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (s : Code N sample) :
    decode N.root (code N e s).val = state e (decode N.root s.val) :=
  decode_commutes e N.root s.val

theorem snapshot_inverse (e : A ≃ B) (s : Snapshot V E A) :
    snapshot e.symm (snapshot e s) = s := by
  apply Snapshot.ext
  · ext x
    simp [snapshot]
  · funext x
    simp [snapshot]
  · funext x
    simp only [snapshot, Equiv.symm_symm, Equiv.symm_apply_apply, Option.map_map]
    cases h : s.genealogy x with
    | none => rfl
    | some t => simp only [Option.map_some, Function.comp_apply, tree_inverse]
  · funext x
    simp [snapshot]
  · rfl

/-- Bijection on the entire original admitted Code carrier, including
noncanonical dead options. No native enumeration-coverage claim is hidden here. -/
noncomputable def codeEquiv (N : RootedBinary V E X) (sample : A → X)
    (e : A ≃ B) : Code N sample ≃ Code N (sample ∘ e.symm) where
  toFun := code N e
  invFun d := ⟨snapshot e.symm d.val, by
    change SourceValid N sample (decode N.root (snapshot e.symm d.val))
    rw [decode_commutes]
    have h := source_valid N (sample ∘ e.symm) e.symm
      (decode N.root d.val) d.property
    simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using h⟩
  left_inv s := Subtype.ext (snapshot_inverse e s.val)
  right_inv d := Subtype.ext (snapshot_inverse e.symm d.val)

theorem merge_commutes (e : A ≃ B) (s : State V E A) (a b : A) :
    state e (merge s a b) = merge (state e s) (e a) (e b) := by
  unfold state merge
  simp only [Finset.image_erase e.injective, List.map_append, List.map_cons,
    List.map_nil, event, Equiv.symm_apply_apply]
  congr 1
  · funext y
    by_cases h : s.ancestor (e.symm y) = b
    · simp [h]
    · have h' : e (s.ancestor (e.symm y)) ≠ e b := fun he => h (e.injective he)
      simp [h, h']
  · funext y
    by_cases h : e.symm y = a
    · have h' : y = e a := by simpa using congrArg e h
      simp [h, h', mapLabels]
    · have h' : y ≠ e a := fun he => h (by simp [he])
      simp [h, h']

theorem encode_commutes (e : A ≃ B) (s : State V E A) (hs : Valid s) :
    snapshot e (encode s hs) = encode (state e s) (valid e s hs) := by
  apply Snapshot.ext
  · rfl
  · rfl
  · funext y
    by_cases hy : e.symm y ∈ s.live
    · have hy' : y ∈ (state e s).live :=
        by simpa using (mem_live e s (e.symm y)).mpr hy
      simp [snapshot, encode, state, tree, hy, hy']
    · have hy' : y ∉ (state e s).live := by
        intro h
        exact hy ((mem_live e s (e.symm y)).mp (by simpa using h))
      simp [snapshot, encode, hy, hy']
  · funext y
    by_cases hy : e.symm y ∈ s.live
    · have hy' : y ∈ (state e s).live :=
        by simpa using (mem_live e s (e.symm y)).mpr hy
      simp [snapshot, encode, state, hy, hy']
    · have hy' : y ∉ (state e s).live := by
        intro h
        exact hy ((mem_live e s (e.symm y)).mp (by simpa using h))
      simp [snapshot, encode, hy, hy']
  · rfl

theorem pair_mem_code (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (s : Code N sample) (i : Option E) (a b : A) :
    (e a, e b) ∈ (populationRoots
      (decode N.root (code N e s).val) (originalPlace N i)).offDiag ↔
    (a,b) ∈ (populationRoots (decode N.root s.val) (originalPlace N i)).offDiag := by
  rw [code_state]
  simp [Finset.mem_offDiag, populationRoots, state]

noncomputable def choiceEquiv (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (s : Code N sample) : Choice N s ≃ Choice N (code N e s) where
  toFun p := ⟨p.1, ⟨(e p.2.val.1, e p.2.val.2),
    (pair_mem_code N e s p.1 p.2.val.1 p.2.val.2).mpr p.2.property⟩⟩
  invFun q := ⟨q.1, ⟨(e.symm q.2.val.1, e.symm q.2.val.2),
    (pair_mem_code N e s q.1 (e.symm q.2.val.1) (e.symm q.2.val.2)).mp
      (by simpa using q.2.property)⟩⟩
  left_inv p := by
    rcases p with ⟨i, ⟨⟨a,b⟩, h⟩⟩
    simp
  right_inv q := by
    rcases q with ⟨i, ⟨⟨a,b⟩, h⟩⟩
    simp

theorem code_live_card (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (s : Code N sample) :
    (code N e s).val.live.card = s.val.live.card := by
  change (s.val.live.image e).card = _
  exact Finset.card_image_iff.mpr (fun a _ b _ h => e.injective h)

variable [FinEnum V] [FinEnum E] [FinEnum A] [FinEnum B]

theorem merger_commutes (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (s : Code N sample) (p : Choice N s) :
    code N e (merger N s p) = merger N (code N e s) (choiceEquiv N e s p) := by
  apply Subtype.ext
  change snapshot e (encode (merge (decode N.root s.val) p.2.val.1 p.2.val.2) _) =
    encode (merge (decode N.root (code N e s).val)
      (e p.2.val.1) (e p.2.val.2)) _
  rw [encode_commutes, merge_commutes, code_state]

theorem enumeration_transport (e : A ≃ B) :
    ((FinEnum.toList A).map e).Perm (FinEnum.toList B) := by
  apply (List.perm_ext_iff_of_nodup
    ((FinEnum.nodup_toList (α := A)).map e.injective)
    (FinEnum.nodup_toList (α := B))).mpr
  intro y
  constructor
  · intro _
    exact FinEnum.mem_toList y
  · intro _
    exact List.mem_map.mpr ⟨e.symm y, FinEnum.mem_toList _, e.apply_symm_apply y⟩

/-- Literal rational term lists agree up to permutation, for every fuel and
every original destination. No comparison of only evaluations is substituted. -/
theorem coefficients_perm (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (fuel : Nat) (s d : Code N sample) :
    (coefficients N fuel s d).Perm
      (coefficients N fuel (code N e s) (code N e d)) := by
  have heq (a b : Code N sample) : code N e a = code N e b ↔ a = b :=
    (codeEquiv N sample e).injective.eq_iff
  induction fuel generalizing s with
  | zero => simp [coefficients, heq]
  | succ fuel ih =>
    by_cases hk : s.val.live.card ≤ 1
    · simp [coefficients, code_live_card, hk, heq]
    · simp only [coefficients, code_live_card, if_neg hk]
      apply List.Perm.append
      · simp [heq]
      · let c := choiceEquiv N e s
        let n := s.val.live.card.choose 2
        let f : Choice N s → Expr := fun p =>
          liftExpr n (coefficients N fuel (merger N s p) d)
        let g : Choice N (code N e s) → Expr := fun p =>
          liftExpr n (coefficients N fuel (merger N (code N e s) p) (code N e d))
        change ((FinEnum.toList (Choice N s)).flatMap f).Perm
          ((FinEnum.toList (Choice N (code N e s))).flatMap g)
        have hrec : ((FinEnum.toList (Choice N s)).flatMap f).Perm
            ((FinEnum.toList (Choice N s)).flatMap (fun p => g (c p))) := by
          apply (List.Perm.refl _).flatMap
          intro p _
          have h := (ih (merger N s p)).flatMap_right (liftTerm n)
          simpa only [f, g, c, liftExpr, merger_commutes] using h
        have horder := (enumeration_transport c).flatMap_right g
        exact hrec.trans (by simpa only [List.flatMap_map] using horder)

theorem coefficients_polynomial_transport (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (fuel : Nat) (s d : Code N sample) :
    exprPolynomial (coefficients N fuel s d) =
      exprPolynomial (coefficients N fuel (code N e s) (code N e d)) := by
  unfold exprPolynomial
  exact ((coefficients_perm N e fuel s d).map _).sum_eq

end Dot.CopyCarrierTransport
