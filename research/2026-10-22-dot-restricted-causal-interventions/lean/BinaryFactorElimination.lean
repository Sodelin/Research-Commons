import BinaryAncestralMarginal

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Finite algebra for D1's moral-component factorization: eliminating a
coordinate from a product of factors depending on disjoint variable sets
preserves that separation and deletes the eliminated dependence. This is
an actual two-point-sum induction, not a global-Markov premise.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def DependsOn (S : Finset V) (f : Assignment V → ℚ) : Prop :=
  ∀ a b, (∀ v ∈ S, a v = b v) → f a = f b

theorem dependsOn_mono {S T : Finset V} {f : Assignment V → ℚ}
    (h : DependsOn S f) (subset : S ⊆ T) : DependsOn T f :=
  fun a b agree => h a b (fun v member => agree v (subset member))

theorem dependsOn_update_outside {S : Finset V} {f : Assignment V → ℚ}
    (h : DependsOn S f) {vertex : V} (outside : vertex ∉ S) (w : Assignment V) (b : Bool) :
    f (pointAssignment vertex w b) = f w := by
  apply h
  intro v member
  have different : v ≠ vertex := by intro same; subst v; exact outside member
  simp only [pointAssignment, if_neg different]

theorem dependsOn_sumAt {S : Finset V} {f : Assignment V → ℚ}
    (h : DependsOn S f) (vertex : V) : DependsOn (S.erase vertex) (sumAt vertex f) := by
  intro a b agree
  have equalUpdated : ∀ bit, f (pointAssignment vertex a bit) = f (pointAssignment vertex b bit) := by
    intro bit
    apply h
    intro v member
    by_cases same : v = vertex
    · subst v; simp only [pointAssignment, if_pos rfl]
    · simp only [pointAssignment, if_neg same]
      exact agree v (Finset.mem_erase.mpr ⟨same, member⟩)
  unfold sumAt
  rw [equalUpdated false, equalUpdated true]

theorem sumAt_product_left {R : Finset V} {f g : Assignment V → ℚ}
    («right» : DependsOn R g) {vertex : V} (outside : vertex ∉ R) :
    sumAt vertex (fun w => f w * g w) = fun w => sumAt vertex f w * g w := by
  funext w
  unfold sumAt
  rw [dependsOn_update_outside «right» outside w false, dependsOn_update_outside «right» outside w true]
  ring

theorem sumAt_product_right {L : Finset V} {f g : Assignment V → ℚ}
    («left» : DependsOn L f) {vertex : V} (outside : vertex ∉ L) :
    sumAt vertex (fun w => f w * g w) = fun w => f w * sumAt vertex g w := by
  funext w
  unfold sumAt
  rw [dependsOn_update_outside «left» outside w false, dependsOn_update_outside «left» outside w true]
  ring

theorem erase_sdiff_list (S : Finset V) (vertex : V) (rest : List V) :
    (S.erase vertex) \ rest.toFinset = S \ (vertex :: rest).toFinset := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_cons, not_or]
  constructor
  · rintro ⟨⟨different, member⟩, outside⟩
    exact ⟨member, different, outside⟩
  · rintro ⟨member, different, outside⟩
    exact ⟨⟨different, member⟩, outside⟩

theorem sdiff_list_of_outside (S : Finset V) (vertex : V) (outside : vertex ∉ S) (rest : List V) :
    S \ rest.toFinset = S \ (vertex :: rest).toFinset := by
  ext v
  simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, not_or]
  constructor
  · rintro ⟨member, notRest⟩
    exact ⟨member, (by intro same; subst v; exact outside member), notRest⟩
  · rintro ⟨member, _, notRest⟩
    exact ⟨member, notRest⟩

theorem eliminate_disjoint_product (vertices : List V) (L R : Finset V) (disjoint : Disjoint L R)
    (f g : Assignment V → ℚ) («left» : DependsOn L f) («right» : DependsOn R g) :
    ∃ F G : Assignment V → ℚ,
      DependsOn (L \ vertices.toFinset) F ∧ DependsOn (R \ vertices.toFinset) G ∧
      eliminateVariables vertices (fun w => f w * g w) = fun w => F w * G w := by
  classical
  induction vertices generalizing L R f g with
  | nil =>
      exact ⟨f, g, by simpa using «left», by simpa using «right», rfl⟩
  | cons vertex rest ih =>
      by_cases inLeft : vertex ∈ L
      · have outsideRight : vertex ∉ R := fun member => Finset.disjoint_left.mp disjoint inLeft member
        have nextDisjoint : Disjoint (L.erase vertex) R := by
          apply Finset.disjoint_left.mpr
          intro v inL inR
          exact Finset.disjoint_left.mp disjoint (Finset.mem_erase.mp inL).2 inR
        obtain ⟨F, G, Fdepends, Gdepends, equation⟩ := ih (L.erase vertex) R nextDisjoint
          (sumAt vertex f) g (dependsOn_sumAt «left» vertex) «right»
        refine ⟨F, G, ?_, ?_, ?_⟩
        · simpa only [erase_sdiff_list] using Fdepends
        · simpa only [sdiff_list_of_outside R vertex outsideRight rest] using Gdepends
        · rw [eliminateVariables, sumAt_product_left «right» outsideRight]
          exact equation
      · have nextDisjoint : Disjoint L (R.erase vertex) := by
          apply Finset.disjoint_left.mpr
          intro v inL inR
          exact Finset.disjoint_left.mp disjoint inL (Finset.mem_erase.mp inR).2
        obtain ⟨F, G, Fdepends, Gdepends, equation⟩ := ih L (R.erase vertex) nextDisjoint
          f (sumAt vertex g) «left» (dependsOn_sumAt «right» vertex)
        refine ⟨F, G, ?_, ?_, ?_⟩
        · simpa only [sdiff_list_of_outside L vertex inLeft rest] using Fdepends
        · simpa only [erase_sdiff_list] using Gdepends
        · rw [eliminateVariables, sumAt_product_right «left» inLeft]
          exact equation

end RestrictedCausal.ProbabilitySource.BinaryCPT
