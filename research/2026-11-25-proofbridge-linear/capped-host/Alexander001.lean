import CappedConcretePad
import PresentedCappedHost
import FixedGender

namespace ResearchCommons.Alexander001
open BirthOrder PopulationCounting PopulationReindex
open ResearchCommons.CappedPresentedPadding ResearchCommons.CappedConcretePad
open ResearchCommons.CappedLabeledGrid ResearchCommons.CappedPaddingLanguage
open ResearchCommons.PresentedCappedHost

section Time
variable {V H Time : Type} [LE Time] [LT Time]
  [Std.IsLinearPreorder Time] [Std.LawfulOrderLT Time]
variable {birth : V → Time} {hostBirth : H → Time} {k : Nat}

private theorem higher (p : PresentedPopulation birth k k) (t : Time) :
    ∃ y, t < birth y := by
  obtain ⟨xs,cover⟩ := p.finite_sublevels t
  obtain ⟨y,hy⟩ := p.infinite xs
  have nle : ¬ birth y ≤ t := fun h => hy (cover y h)
  have le : t ≤ birth y := (Std.IsLinearPreorder.le_total _ _).resolve_right nle
  exact ⟨y,(Std.LawfulOrderLT.lt_iff _ _).mpr ⟨le,nle⟩⟩

noncomputable def stamps (p : PresentedPopulation birth k k) : Nat → Time
  | 0 => birth (Classical.choose (p.infinite []))
  | n+1 => birth (Classical.choose (higher p (stamps p n)))

theorem stamps_increase (p : PresentedPopulation birth k k) (a b : Nat) (h : a < b) :
    stamps p a < stamps p b := by
  have step (n : Nat) : stamps p n < stamps p (n+1) :=
    Classical.choose_spec (higher p (stamps p n))
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases e : a=b
    · subst a
      exact step b
    · exact Std.lt_trans (ih (by omega)) (step b)

omit [Std.IsLinearPreorder Time] [Std.LawfulOrderLT Time] in
private theorem joinedGrid {W : Type} (p : PresentedPopulation birth k k)
    (q : FinitePad W Time k k) {n : Nat} (grid : HasGrid q.edge n) :
    HasGrid (attach p q).edge n := by
  obtain ⟨f,inj,adj⟩ := grid
  refine ⟨fun c => Sum.inr (f c),fun a b h => inj a b (Sum.inr.inj h),?_⟩
  exact adj

private theorem labeledHasGrid (n k : Nat) : HasGrid (@ResearchCommons.CappedLabeledGrid.edge n k) n := by
  refine ⟨Sum.inr,fun _ _ h => Sum.inr.inj h,?_⟩
  intro a b h
  left
  rcases h with e | u
  · simp [grid_east_edge a b e]
  · simp [grid_north_edge a b u]

/-- No host in the original presentation is universal for the infinite-word class,
provided it is nonempty. Embedding ignores dates, edge labels and directions. -/
theorem labeled_nonuniversal (host : PresentedPopulation hostBirth k k) (base : PresentedPopulation birth k k) (hk : 2 ≤ k)
    (n : Nat) (large : k * fullRootCount (toNatPopulation host) + 1 < n) :
    ∃ (date : Sum V (Vertex n k) → Time)
      (candidate : PresentedPopulation date k k),
      (∀ word, Realizes candidate.edge word ↔ Realizes base.edge word) ∧
      ¬ Embeds candidate.edge host.edge := by
  let pad := labeledPad (stamps base) (stamps_increase base) n k hk
  refine ⟨_,attach base pad,?_,?_⟩
  · intro word
    exact preserves_words base.edge n k word
  · exact no_presented_grid_source_embedding host large (joinedGrid base pad (labeledHasGrid n k))

noncomputable def fixedPad (p : PresentedPopulation birth k k) (n : Nat) (hk : 2 ≤ k) :
    FinitePad (Vertex n k) Time k k where
  birth := fun w => stamps p (rank w)
  edge := @ResearchCommons.FixedGender.fixedEdge n k
  cover := vertices n k
  cover_all := allVertices
  ordered := by
    intro x y h
    cases e : ResearchCommons.FixedGender.fixedEdge x y with
    | none => simp [e] at h
    | some l =>
      exact stamps_increase p _ _ (ResearchCommons.FixedGender.fixed_rank_rises x y l e)
  label_valid := by
    intro x y l e
    rw [← ResearchCommons.FixedGender.fixedLabel x y l e]
    exact ResearchCommons.FixedGender.gender_lt hk x
  parent_of_label := by
    intro v h l hl
    cases v with
    | inl r => exact False.elim (h (fun x => ResearchCommons.FixedGender.no_edge_into_root x r))
    | inr c => exact ResearchCommons.FixedGender.everyLabel c ⟨l,hl⟩
  children := by
    intro x
    obtain ⟨xs,hx,cover⟩ := ResearchCommons.FixedGender.fixed_children_covered x
    refine ⟨xs,Nat.le_trans hx hk,?_⟩
    intro y h
    cases e : ResearchCommons.FixedGender.fixedEdge x y with
    | none => simp [e] at h
    | some l => exact cover y l e

private theorem fixedHasGrid (n k : Nat) : HasGrid (@ResearchCommons.FixedGender.fixedEdge n k) n := by
  refine ⟨Sum.inr,fun _ _ h => Sum.inr.inj h,?_⟩
  intro a b h
  left
  have e := ResearchCommons.FixedGender.grid_edge (k:=k) a b h
  simp [e]

/-- The source colors remain fixed, and the host need not preserve colors. -/
theorem fixed_nonuniversal (host : PresentedPopulation hostBirth k k) (base : PresentedPopulation birth k k) (hk : 2 ≤ k)
    (color : V → Nat) (bound : ∀ x, color x < k)
    (fixed : ∀ x y l, base.edge x y = some l → color x = l)
    (n : Nat) (large : k * fullRootCount (toNatPopulation host) + 1 < n) :
    ∃ (date : Sum V (Vertex n k) → Time)
      (candidate : PresentedPopulation date k k)
      (tint : Sum V (Vertex n k) → Nat),
      (∀ x, tint x < k) ∧
      (∀ x y l, candidate.edge x y = some l → tint x = l) ∧
      (∀ word, Realizes candidate.edge word ↔ Realizes base.edge word) ∧
      ¬ Embeds candidate.edge host.edge := by
  let pad := fixedPad base n hk
  refine ⟨_,attach base pad,Sum.elim color ResearchCommons.FixedGender.gender,?_,?_,?_,?_⟩
  · intro x
    cases x with
    | inl x => exact bound x
    | inr x => exact ResearchCommons.FixedGender.gender_lt hk x
  · intro x y l h
    cases x <;> cases y
    · exact fixed _ _ l h
    · change none = some l at h; simp at h
    · change none = some l at h; simp at h
    · exact ResearchCommons.FixedGender.fixedLabel _ _ l h
  · intro word
    exact ResearchCommons.FixedGender.fixed_preserves_words base.edge n k word
  · exact no_presented_grid_source_embedding host large (joinedGrid base pad (fixedHasGrid n k))

/-- For each proposed host, one eligible avoiding population defeats it. -/
theorem no_universal_labeled (host : PresentedPopulation hostBirth k k)
    (base : PresentedPopulation birth k k) (hk : 2 ≤ k) (word : Nat → Nat)
    (avoids : ¬ Realizes base.edge word) :
    ∃ (side : Nat) (date : Sum V (Vertex side k) → Time)
      (candidate : PresentedPopulation date k k),
      (¬ Realizes candidate.edge word) ∧ ¬ Embeds candidate.edge host.edge := by
  let n := k * fullRootCount (toNatPopulation host) + 2
  have h : k * fullRootCount (toNatPopulation host) + 1 < n := by dsimp [n]; omega
  obtain ⟨date,q,words,notEmb⟩ := labeled_nonuniversal host base hk n h
  exact ⟨n,date,q,fun real => avoids ((words word).mp real),notEmb⟩

/-- Counterexample source retains a fixed source color on every vertex. -/
theorem no_universal_fixed (host : PresentedPopulation hostBirth k k)
    (base : PresentedPopulation birth k k) (hk : 2 ≤ k)
    (color : V → Nat) (bound : ∀ x, color x < k)
    (fixed : ∀ x y l, base.edge x y = some l → color x = l)
    (word : Nat → Nat) (avoids : ¬ Realizes base.edge word) :
    ∃ (side : Nat) (date : Sum V (Vertex side k) → Time)
      (candidate : PresentedPopulation date k k) (tint : Sum V (Vertex side k) → Nat),
      (∀ x, tint x < k) ∧
      (∀ x y l, candidate.edge x y = some l → tint x = l) ∧
      (¬ Realizes candidate.edge word) ∧ ¬ Embeds candidate.edge host.edge := by
  let n := k * fullRootCount (toNatPopulation host) + 2
  have h : k * fullRootCount (toNatPopulation host) + 1 < n := by dsimp [n]; omega
  obtain ⟨date,q,tint,hb,hf,words,notEmb⟩ :=
    fixed_nonuniversal host base hk color bound fixed n h
  exact ⟨n,date,q,tint,hb,hf,fun real => avoids ((words word).mp real),notEmb⟩

end Time
#print axioms labeled_nonuniversal
#print axioms fixed_nonuniversal
#print axioms no_universal_labeled
#print axioms no_universal_fixed
end ResearchCommons.Alexander001
