import ResearchCommons.MSCI.JC69Source
import G2LiteralTimedObservationPruning

/-! Mutation probabilities respect the ORIGINAL child-swap quotient.
A transported decoration retains every age, original label and branch clock.
No associativity, label erasure or desired probability equality is assumed.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69Unranked
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ChronologicalDecoration
open GProgram.G2.LiteralTimedObservationPruning
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Tree
open ResearchCommons.MSCI.JC69Source
open scoped Classical BigOperators
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

def Preserves (leafAge : Copy → ℝ) {a b : Genealogy Copy}
    (e : Decoration a ≃ Decoration b) : Prop :=
  ∀ d, rootAge leafAge a d = rootAge leafAge b (e d) ∧
    (∀ x y, pairAge leafAge a d x y = pairAge leafAge b (e d) x y) ∧
    (∀ c p, likelihood a (clockSurvivals leafAge a d) c (labelPattern a p) =
      likelihood b (clockSurvivals leafAge b (e d)) c (labelPattern b p))

/-- The equivalence exists inside Prop: induction on the actual quotient
proof does not eliminate arbitrary proof data into a new source/clock object.
Every graft age and original pair-age entry is transported literally. -/
theorem unordered_decoration_transport (leafAge : Copy → ℝ)
    {a b : Genealogy Copy} (h : UnorderedEquiv a b) :
    a.WellLabelled → ∃ e : Decoration a ≃ Decoration b, Preserves leafAge e := by
  induction h with
  | refl a =>
      intro ha
      exact ⟨Equiv.refl _,fun d => ⟨rfl,fun _ _ => rfl,fun _ _ => rfl⟩⟩
  | @symm a b h ih =>
      intro hb
      obtain ⟨e,he⟩ := ih ((unordered_wellLabelled h).mpr hb)
      refine ⟨e.symm,?_⟩
      intro d
      have hd := he (e.symm d)
      rw [e.apply_symm_apply d] at hd
      exact ⟨hd.1.symm,fun x y => (hd.2.1 x y).symm,
        fun c p => (hd.2.2 c p).symm⟩
  | @trans a b c h1 h2 ih1 ih2 =>
      intro ha
      obtain ⟨e,he⟩ := ih1 ha
      obtain ⟨f,hf⟩ := ih2 ((unordered_wellLabelled h1).mp ha)
      refine ⟨e.trans f,?_⟩
      intro d
      exact ⟨(he d).1.trans (hf (e d)).1,
        fun x y => ((he d).2.1 x y).trans ((hf (e d)).2.1 x y),
        fun c p => ((he d).2.2 c p).trans ((hf (e d)).2.2 c p)⟩
  | @graft a b c d h1 h2 ih1 ih2 =>
      intro ht
      obtain ⟨el,hl⟩ := ih1 ht.1
      obtain ⟨er,hr⟩ := ih2 ht.2.1
      let e : Decoration (.graft a b) ≃ Decoration (.graft c d) :=
        { toFun := fun z => (z.1,el z.2.1,er z.2.2)
          invFun := fun z => (z.1,el.symm z.2.1,er.symm z.2.2)
          left_inv := by
            rintro ⟨t,u,v⟩
            simp only [el.symm_apply_apply,er.symm_apply_apply]
          right_inv := by
            rintro ⟨t,u,v⟩
            simp only [el.apply_symm_apply,er.apply_symm_apply] }
      refine ⟨e,?_⟩
      intro z
      obtain ⟨hLA,hLP,hLL⟩ := hl z.2.1
      obtain ⟨hRA,hRP,hRL⟩ := hr z.2.2
      refine ⟨rfl,?_,?_⟩
      · intro x y
        change pairAge leafAge (.graft a b) z x y =
          pairAge leafAge (.graft c d) (z.1,el z.2.1,er z.2.2) x y
        simp only [pairAge,← unordered_leaves h1,← unordered_leaves h2]
        by_cases hL : x ∈ a.leaves ∧ y ∈ a.leaves
        · rw [if_pos hL,if_pos hL]
          exact hLP x y
        · rw [if_neg hL,if_neg hL]
          by_cases hR : x ∈ b.leaves ∧ y ∈ b.leaves
          · rw [if_pos hR,if_pos hR]
            exact hRP x y
          · rw [if_neg hR,if_neg hR]
      · intro base p
        change likelihood (.graft a b) (clockSurvivals leafAge (.graft a b) z)
          base (labelPattern (.graft a b) p) =
          likelihood (.graft c d)
            (clockSurvivals leafAge (.graft c d) (z.1,el z.2.1,er z.2.2))
            base (labelPattern (.graft c d) p)
        simp only [clockSurvivals,likelihood,labelPattern]
        rw [← hLA,← hRA]
        simp_rw [hLL,hRL]
  | swap a b =>
      intro ht
      let e : Decoration (.graft a b) ≃ Decoration (.graft b a) :=
        { toFun := fun z => (z.1,z.2.2,z.2.1)
          invFun := fun z => (z.1,z.2.2,z.2.1)
          left_inv := by rintro ⟨t,u,v⟩; rfl
          right_inv := by rintro ⟨t,u,v⟩; rfl }
      refine ⟨e,?_⟩
      intro z
      refine ⟨rfl,?_,?_⟩
      · intro x y
        change pairAge leafAge (.graft a b) z x y =
          pairAge leafAge (.graft b a) (z.1,z.2.2,z.2.1) x y
        simp only [pairAge]
        by_cases hL : x ∈ a.leaves ∧ y ∈ a.leaves
        · have hR : ¬ (x ∈ b.leaves ∧ y ∈ b.leaves) :=
            fun h => Finset.disjoint_left.mp ht.2.2 hL.1 h.1
          rw [if_pos hL,if_neg hR,if_pos hL]
        · rw [if_neg hL]
          by_cases hR : x ∈ b.leaves ∧ y ∈ b.leaves
          · rw [if_pos hR,if_pos hR]
          · rw [if_neg hR,if_neg hR,if_neg hL]
      · intro base p
        change likelihood (.graft a b) (clockSurvivals leafAge (.graft a b) z)
          base (labelPattern (.graft a b) p) =
          likelihood (.graft b a) (clockSurvivals leafAge (.graft b a) (z.1,z.2.2,z.2.1))
            base (labelPattern (.graft b a) p)
        simp only [clockSurvivals,likelihood,labelPattern]
        exact mul_comm _ _

/-- SAME observed matrix, with its actual original decoration on one
representative. The quotient transports that decoration and the EXISTING
decoder uniqueness identifies the other representative; no new fit is made. -/
theorem decoded_root_probability_unordered (leafAge : Copy → ℝ)
    {a b : Genealogy Copy} (h : UnorderedEquiv a b) (ha : a.WellLabelled)
    (d : Decoration a) (M : Copy → Copy → ℝ)
    (hM : ∀ x ∈ a.leaves, ∀ y ∈ a.leaves, M x y = pairAge leafAge a d x y)
    (p : Copy → Base) :
    rootLikelihood a (clockSurvivals leafAge a (decode M a)) (labelPattern a p) =
      rootLikelihood b (clockSurvivals leafAge b (decode M b)) (labelPattern b p) := by
  obtain ⟨e,he⟩ := unordered_decoration_transport leafAge h ha
  have hA := decode_of_pair_agreement leafAge a ha d M hM
  have hB : decode M b = e d := by
    apply decode_of_pair_agreement leafAge b ((unordered_wellLabelled h).mp ha) (e d) M
    intro x hx y hy
    have hx' : x ∈ a.leaves := by rw [unordered_leaves h]; exact hx
    have hy' : y ∈ a.leaves := by rw [unordered_leaves h]; exact hy
    exact (hM x hx' y hy').trans ((he d).2.1 x y)
  rw [hA,hB]
  unfold rootLikelihood
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun v : ℝ => (1/4 : ℝ)*v) ((he d).2.2 c p)

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [Nonempty Copy]

/-- Derive the actual ONE unranked tree from full completed-source support.
Original survivor IDs, dead fields, populations and stored bits are not
additional tree observations. -/
theorem completed_forest_singleton (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) (hcard : (state d).live.card ≤ 1) :
    sourceUnrankedForest (state d) Finset.univ =
      {toUnranked ((state d).genealogy (selectedRoot N d))} := by
  ext q
  rw [mem_forest_iff_live (state d) d.property.forest Finset.univ]
  simp only [prune_all,optionUnranked,Option.map_some,Option.some.injEq,
    Finset.mem_singleton]
  constructor
  · rintro ⟨l,hl,hq⟩
    have hroot : l = selectedRoot N d :=
      Finset.card_le_one.mp hcard l hl _ (selected_root_live N d)
    simpa only [hroot] using hq.symm
  · intro hq
    exact ⟨selectedRoot N d,selected_root_live N d,hq.symm⟩

variable {V' E' X' : Type*}
variable [DecidableEq V'] [DecidableEq E'] [Fintype V'] [Fintype E'] [Fintype X']

/-- Actual conditional probability depends only on the full original
unranked forest and SAME matrix on admitted completed points. Desired
probability equality is a CONCLUSION; no register/exterior independence,
rerouting, extra observation or representative convention is a premise. -/
theorem conditional_kernel_same_timed_observation (N : RootedBinary V E X) (N' : RootedBinary V' E' X')
    {sample : Copy → X} {sample' : Copy → X'} (leafAge : Copy → ℝ)
    (a : Code N sample) (b : Code N' sample')
    (M : Copy → Copy → ℝ)
    (ha : GoodPoint N leafAge (a,M)) (hb : GoodPoint N' leafAge (b,M))
    (hf : sourceUnrankedForest (state a) Finset.univ =
      sourceUnrankedForest (state b) Finset.univ) :
    conditionalKernel N leafAge (a,M) = conditionalKernel N' leafAge (b,M) := by
  have ht : toUnranked ((state a).genealogy (selectedRoot N a)) =
      toUnranked ((state b).genealogy (selectedRoot N' b)) := by
    rw [completed_forest_singleton N a ha.1,completed_forest_singleton N' b hb.1] at hf
    simpa only [Finset.singleton_inj] using hf
  obtain ⟨d,hd,_,_⟩ := ha.2.choose_spec (selectedRoot N a) (selected_root_live N a)
  apply PMF.ext
  intro p
  rw [conditional_kernel_probability N leafAge (a,M) ha p,
    conditional_kernel_probability N' leafAge (b,M) hb p]
  apply congrArg ENNReal.ofReal
  exact decoded_root_probability_unordered leafAge
    ((toUnranked_eq_iff _ _).mp ht) (a.property.forest.wellLabelled _ (selected_root_live N a))
    d M hd p

/-- The same conditional congruence holds for EVERY finite locus before source
mixing. One original timed tree/matrix is shared by every site. -/
theorem conditional_locus_same_timed_observation (L : ℕ) (N : RootedBinary V E X) (N' : RootedBinary V' E' X')
    {sample : Copy → X} {sample' : Copy → X'} (leafAge : Copy → ℝ)
    (a : Code N sample) (b : Code N' sample')
    (M : Copy → Copy → ℝ)
    (ha : GoodPoint N leafAge (a,M)) (hb : GoodPoint N' leafAge (b,M))
    (hf : sourceUnrankedForest (state a) Finset.univ =
      sourceUnrankedForest (state b) Finset.univ) :
    conditionalLocusKernel L N leafAge (a,M) = conditionalLocusKernel L N' leafAge (b,M) := by
  have hk := conditional_kernel_same_timed_observation N N' leafAge a b M ha hb hf
  apply PMF.ext
  intro p
  change (∏ j, conditionalKernel N leafAge (a,M) (p j)) =
    (∏ j, conditionalKernel N' leafAge (b,M) (p j))
  rw [hk]

end ResearchCommons.MSCI.JC69Unranked
