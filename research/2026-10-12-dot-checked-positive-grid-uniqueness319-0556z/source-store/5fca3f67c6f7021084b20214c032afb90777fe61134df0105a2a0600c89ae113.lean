import G2WholeMatrixAges

/-!
Chronological validity of actual graft-age decorations.
Contributor: dot (OpenAI), 6 October 2026.
Leaf sampling dates are fixed original data. Internal bounds apply only to
already created grafts, so future dormant singleton samples are not incorrectly
forced below the current calendar time.
-/
namespace GProgram.G2.ChronologicalDecoration
set_option backward.isDefEq.respectTransparency false
open GProgram.SourceForest Nanuq.Source
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.SourceGraftDecoration
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def rootAge (leafAge : Copy → ℝ) : (t : Genealogy Copy) → Decoration t → ℝ
  | .leaf x,_ => leafAge x
  | .graft _ _,d => d.1

noncomputable def Chronological (leafAge : Copy → ℝ) : (t : Genealogy Copy) → Decoration t → Prop
  | .leaf _,_ => True
  | .graft a b,d => Chronological leafAge a d.2.1 ∧ Chronological leafAge b d.2.2 ∧
      rootAge leafAge a d.2.1 < d.1 ∧ rootAge leafAge b d.2.2 < d.1

noncomputable def InternalBound (bound : ℝ) : (t : Genealogy Copy) → Decoration t → Prop
  | .leaf _,_ => True
  | .graft a b,d => d.1 ≤ bound ∧ InternalBound bound a d.2.1 ∧ InternalBound bound b d.2.2

lemma internal_bound_mono {a b : ℝ} (hab : a ≤ b) (t : Genealogy Copy) (d : Decoration t)
    (h : InternalBound a t d) : InternalBound b t d := by
  induction t with
  | leaf x => trivial
  | graft t u ht hu => exact ⟨h.1.trans hab,ht d.2.1 h.2.1,hu d.2.2 h.2.2⟩

lemma root_age_le (leafAge : Copy → ℝ) (t : Genealogy Copy) (d : Decoration t) (bound : ℝ)
    (hi : InternalBound bound t d) (hl : ∀ x ∈ t.leaves, leafAge x ≤ bound) :
    rootAge leafAge t d ≤ bound := by
  cases t with
  | leaf x => exact hl x (Finset.mem_singleton_self x)
  | graft a b => exact hi.1

noncomputable def TimedBound (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (bound : ℝ) : Prop :=
  ∀ l ∈ s.live, ∃ d : Decoration (s.genealogy l),
    (∀ x ∈ (s.genealogy l).leaves, ∀ y ∈ (s.genealogy l).leaves,
      M x y = pairAge leafAge (s.genealogy l) d x y) ∧
    Chronological leafAge (s.genealogy l) d ∧ InternalBound bound (s.genealogy l) d

lemma timed_bound_decorates (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (bound : ℝ) (h : TimedBound leafAge M s bound) : ForestDecorates leafAge M s := by
  intro l hl
  obtain ⟨d,hd,_,_⟩ := h l hl
  exact ⟨d,hd⟩

lemma timed_bound_mono (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) {a b : ℝ} (hab : a ≤ b) (h : TimedBound leafAge M s a) :
    TimedBound leafAge M s b := by
  intro l hl
  obtain ⟨d,hd,hc,hi⟩ := h l hl
  exact ⟨d,hd,hc,internal_bound_mono hab _ d hi⟩

variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
lemma initial_timed_bound (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool)
    (leafAge : Copy → ℝ) (bound : ℝ) : TimedBound leafAge (fun x _ => leafAge x) (initial N sample register) bound := by
  intro l hl
  refine ⟨PUnit.unit,?_,True.intro,True.intro⟩
  intro x hx y hy
  have he : x = l := Finset.mem_singleton.mp hx
  subst x
  rfl

lemma updated_child_decode (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) {a b l : Copy} (hm : LegalMerge s a b)
    (hl : l ∈ s.live) (d : Decoration (s.genealogy l))
    (hd : ∀ x ∈ (s.genealogy l).leaves, ∀ y ∈ (s.genealogy l).leaves,
      M x y = pairAge leafAge (s.genealogy l) d x y) (age : ℝ) :
    decode (mergeAgeMatrix s a b age M) (s.genealogy l) = d := by
  apply decode_of_pair_agreement leafAge _ (hs.wellLabelled l hl)
  intro x hx y hy
  rw [same_operand_keeps_age s hm.different ((hs.leaf_fiber l hl x).mp hx) ((hs.leaf_fiber l hl y).mp hy)]
  exact hd x hx y hy

/-- New actual grafts are strictly older than both children once the source
clock advances beyond the previous internal bound and active leaf dates. -/
theorem merge_timed_bound (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) {a b : Copy} (hm : LegalMerge s a b)
    (bound age : ℝ) (hstrict : bound < age) (hM : TimedBound leafAge M s bound)
    (hLa : ∀ x ∈ (s.genealogy a).leaves, leafAge x ≤ bound)
    (hLb : ∀ x ∈ (s.genealogy b).leaves, leafAge x ≤ bound) :
    TimedBound leafAge (mergeAgeMatrix s a b age M) (merge s a b) age := by
  have hf := actual_merge_decorates leafAge M s hs hm age (timed_bound_decorates leafAge M s bound hM)
  intro l hl
  have hll : l ∈ s.live := (Finset.mem_erase.mp hl).2
  by_cases hla : l = a
  · subst l
    obtain ⟨da,hda,hca,hia⟩ := hM a hm.first_live
    obtain ⟨db,hdb,hcb,hib⟩ := hM b hm.second_live
    have hgen : (merge s a b).genealogy a = .graft (s.genealogy a) (s.genealogy b) := by simp [merge]
    have hfa := hf a hl
    rw [hgen] at hfa ⊢
    obtain ⟨dm,hdm⟩ := hfa
    have hwm : (Genealogy.graft (s.genealogy a) (s.genealogy b)).WellLabelled :=
      ⟨hs.wellLabelled a hm.first_live,hs.wellLabelled b hm.second_live,
        distinct_live_genealogies_disjoint s hs hm.first_live hm.second_live hm.different⟩
    have hdec := decode_of_pair_agreement leafAge _ hwm dm (mergeAgeMatrix s a b age M) hdm
    have hx := (hs.leaf_fiber a hm.first_live (witness (s.genealogy a))).mp (witness_mem _)
    have hy := (hs.leaf_fiber b hm.second_live (witness (s.genealogy b))).mp (witness_mem _)
    have hr : mergeAgeMatrix s a b age M (witness (s.genealogy a)) (witness (s.genealogy b)) = age := by
      simp [mergeAgeMatrix,hx,hy]
    have hdecode : decode (mergeAgeMatrix s a b age M) (.graft (s.genealogy a) (s.genealogy b)) = (age,da,db) := by
      simp only [decode,hr,updated_child_decode leafAge M s hs hm hm.first_live da hda age,
        updated_child_decode leafAge M s hs hm hm.second_live db hdb age]
    have he : dm = (age,da,db) := hdec.symm.trans hdecode
    rw [he] at hdm
    exact ⟨(age,da,db),hdm,⟨hca,hcb,(root_age_le leafAge _ da bound hia hLa).trans_lt hstrict,
      (root_age_le leafAge _ db bound hib hLb).trans_lt hstrict⟩,
      ⟨le_rfl,internal_bound_mono hstrict.le _ da hia,internal_bound_mono hstrict.le _ db hib⟩⟩
  · have hgen : (merge s a b).genealogy l = s.genealogy l := by simp [merge,hla]
    rw [hgen]
    obtain ⟨dl,hdl,hcl,hil⟩ := hM l hll
    refine ⟨dl,?_,hcl,internal_bound_mono hstrict.le _ dl hil⟩
    intro x hx y hy
    rw [same_operand_keeps_age s hm.different ((hs.leaf_fiber l hll x).mp hx) ((hs.leaf_fiber l hll y).mp hy)]
    exact hdl x hx y hy

open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceCalendarCompatibility
open GProgram.SourceForestKingmanPopulationProjection

lemma snapshot_preserves_timed_bound (root : V) (s : State V E Copy) (hs : Valid s)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (bound : ℝ) (hM : TimedBound leafAge M s bound) :
    TimedBound leafAge M (decodeSnapshot root (encodeSnapshot s hs)) bound := by
  intro l hl
  have hl' : l ∈ s.live := hl
  rw [decode_encode_live_genealogy root s hs hl']
  exact hM l hl'

/-- Original spatial descent plus the existing temporal compiler invariant
puts every active operand leaf below the current epoch start. -/
lemma active_original_leaf_bound (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    {sample : Copy → X} (s : Code N sample) {a b : ℝ}
    (he : EpochCompatible N C a b (state s)) (x : Copy)
    (hn : ∀ v, copyLocation (state s) x ≠ .node v) : C.age (N.leaf (sample x)) ≤ a := by
  have hd : DescendsTo N (copyLocation (state s) x) (sample x) := s.property.original_descendant x
  have ht := he x
  cases hp : copyLocation (state s) x with
  | node v => exact False.elim (hn v hp)
  | edge e =>
      rw [hp] at hd ht
      exact (C.age_le_of_directed hd).trans ht.1
  | rootPopulation v =>
      rw [hp] at hd ht
      have hh := C.age_le_of_directed hd.2
      simpa only [hd.1] using hh.trans (by simpa only [hd.1] using ht.2)

/-- Actual coded graft validity, with active leaf-age premises DERIVED from
source/calendar legality and earlier internal ages retained below the bound. -/
theorem actual_coded_timed_graft (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) {a b bound age : ℝ}
    (he : EpochCompatible N C a b (state s)) (ha : a ≤ bound) (hstrict : bound < age)
    (M : Copy → Copy → ℝ) (hM : TimedBound (fun x => C.age (N.leaf (sample x))) M (state s) bound) :
    TimedBound (fun x => C.age (N.leaf (sample x)))
      (codedAgeUpdate N s (stepDestination N s (some p)) age M)
      (state (stepDestination N s (some p))) age := by
  have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  have hLa : ∀ x ∈ ((state s).genealogy p.2.val.1).leaves, C.age (N.leaf (sample x)) ≤ bound := by
    intro x hx
    apply (active_original_leaf_bound N C s he x ?_).trans ha
    intro v hv
    have hax : (state s).ancestor x = p.2.val.1 := (s.property.forest.leaf_fiber _ hm.first_live x).mp hx
    change (state s).location ((state s).ancestor x) = .node v at hv
    rw [hax] at hv
    exact hm.population_not_node v hv
  have hLb : ∀ x ∈ ((state s).genealogy p.2.val.2).leaves, C.age (N.leaf (sample x)) ≤ bound := by
    intro x hx
    apply (active_original_leaf_bound N C s he x ?_).trans ha
    intro v hv
    have hbx : (state s).ancestor x = p.2.val.2 := (s.property.forest.leaf_fiber _ hm.second_live x).mp hx
    change (state s).location ((state s).ancestor x) = .node v at hv
    rw [hbx] at hv
    exact hm.population_not_node v (hm.same_population.trans hv)
  rw [coded_update_is_actual_graft]
  exact snapshot_preserves_timed_bound N.root (merge (state s) p.2.val.1 p.2.val.2)
    (merge_valid (state s) s.property.forest hm) _ _ age
    (merge_timed_bound _ M (state s) s.property.forest hm bound age hstrict hM hLa hLb)

#print axioms actual_coded_timed_graft
#print axioms active_original_leaf_bound
#print axioms merge_timed_bound
#print axioms initial_timed_bound
end GProgram.G2.ChronologicalDecoration
