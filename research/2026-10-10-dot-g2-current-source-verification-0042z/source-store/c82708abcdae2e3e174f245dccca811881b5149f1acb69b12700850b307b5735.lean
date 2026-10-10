import UnifiedLean.Source.SourceForestSilentPruning
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Faithful pair-age decorations of the original labelled genealogy

Contributor: dot (OpenAI), 2026-10-06. New reconstruction of the missing
consumer interface, not recovery of its historical source bytes.
The original Genealogy/WellLabelled/pruning providers are unchanged.
Real graft ages have their genuine recursive product measurable structure.
No global Nonempty Copy, chronology, source probability or decoder-correctness
premise is introduced. Existing preserved consumers remain unchanged.
-/

namespace GProgram.G2.FaithfulPairAgeDecoration
set_option backward.isDefEq.respectTransparency false
open MeasureTheory GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open scoped Classical

variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- A leaf has no internal graft age. Grafts retain the exact right-associated
root-age/left-decoration/right-decoration product used by old consumers. -/
noncomputable def Decoration : Genealogy Copy → Type
  | .leaf _ => PUnit
  | .graft a b => ℝ × Decoration a × Decoration b

/-- Canonical measurable spaces on real ages and recursive products. This is
not a discrete measurable structure on real-valued decorations. -/
noncomputable instance decorationMeasurable :
    (t : Genealogy Copy) → MeasurableSpace (Decoration t) :=
  fun t => Genealogy.rec (Copy := Copy)
    (motive := fun u => MeasurableSpace (Decoration u))
    (fun _ => inferInstanceAs (MeasurableSpace PUnit))
    (fun a b ha hb => by
      letI : MeasurableSpace (Decoration a) := ha
      letI : MeasurableSpace (Decoration b) := hb
      exact inferInstanceAs (MeasurableSpace (ℝ × Decoration a × Decoration b))) t

/-- Every supplied genealogy already contains a leaf. No arbitrary default
copy and no ambient Nonempty Copy instance is needed. -/
noncomputable def witness : Genealogy Copy → Copy
  | .leaf x => x
  | .graft a _ => witness a

theorem witness_mem (t : Genealogy Copy) : witness t ∈ t.leaves := by
  induction t with
  | leaf x => simp [witness,Genealogy.leaves]
  | graft a b ha _ =>
      simp only [witness,Genealogy.leaves]
      exact Finset.mem_union.mpr (Or.inl ha)

/-- Exact legacy reduction order, including queries outside the leaf set:
left pair first, then right pair, otherwise the current graft age. -/
noncomputable def pairAge (leafAge : Copy → ℝ) :
    (t : Genealogy Copy) → Decoration t → Copy → Copy → ℝ
  | .leaf z,_,_,_ => leafAge z
  | .graft a b,d,x,y =>
      if x ∈ a.leaves ∧ y ∈ a.leaves then pairAge leafAge a d.2.1 x y
      else if x ∈ b.leaves ∧ y ∈ b.leaves then pairAge leafAge b d.2.2 x y
      else d.1

lemma pairAge_left (leafAge : Copy → ℝ) (a b : Genealogy Copy)
    (d : Decoration (.graft a b)) {x y : Copy}
    (hx : x ∈ a.leaves) (hy : y ∈ a.leaves) :
    pairAge leafAge (.graft a b) d x y = pairAge leafAge a d.2.1 x y := by
  simp only [pairAge,if_pos (And.intro hx hy)]

lemma pairAge_right (leafAge : Copy → ℝ) (a b : Genealogy Copy)
    (d : Decoration (.graft a b)) (hab : Disjoint a.leaves b.leaves) {x y : Copy}
    (hx : x ∈ b.leaves) (hy : y ∈ b.leaves) :
    pairAge leafAge (.graft a b) d x y = pairAge leafAge b d.2.2 x y := by
  have hleft : ¬ (x ∈ a.leaves ∧ y ∈ a.leaves) :=
    fun h => (Finset.disjoint_left.mp hab) h.1 hx
  simp only [pairAge,if_neg hleft,if_pos (And.intro hx hy)]

lemma pairAge_cross (leafAge : Copy → ℝ) (a b : Genealogy Copy)
    (d : Decoration (.graft a b)) (hab : Disjoint a.leaves b.leaves) {x y : Copy}
    (hx : x ∈ a.leaves) (hy : y ∈ b.leaves) :
    pairAge leafAge (.graft a b) d x y = d.1 := by
  have hleft : ¬ (x ∈ a.leaves ∧ y ∈ a.leaves) :=
    fun h => (Finset.disjoint_left.mp hab) h.2 hy
  have hright : ¬ (x ∈ b.leaves ∧ y ∈ b.leaves) :=
    fun h => (Finset.disjoint_left.mp hab) hx h.1
  simp only [pairAge,if_neg hleft,if_neg hright]

/-- Decode the graft age from a genuine cross-child pair and recurse on the
SAME matrix. Well-labelledness is needed for the theorem, not the definition. -/
noncomputable def decode (M : Copy → Copy → ℝ) :
    (t : Genealogy Copy) → Decoration t
  | .leaf _ => PUnit.unit
  | .graft a b => (M (witness a) (witness b),decode M a,decode M b)

/-- Agreement only on the supplied tree's leaf pairs determines every graft
age. Correctness is proved by structural induction from child disjointness. -/
theorem decode_of_pair_agreement (leafAge : Copy → ℝ) :
    ∀ (t : Genealogy Copy) (ht : t.WellLabelled) (d : Decoration t)
      (M : Copy → Copy → ℝ),
      (∀ x ∈ t.leaves, ∀ y ∈ t.leaves, M x y = pairAge leafAge t d x y) →
      decode M t = d := by
  intro t
  induction t with
  | leaf z =>
      intro ht d M hM
      cases d
      rfl
  | graft a b ha hb =>
      intro ht d M hM
      have hroot : M (witness a) (witness b) = d.1 :=
        (hM (witness a) (Finset.mem_union.mpr (Or.inl (witness_mem a)))
          (witness b) (Finset.mem_union.mpr (Or.inr (witness_mem b)))).trans
          (pairAge_cross leafAge a b d ht.2.2 (witness_mem a) (witness_mem b))
      have hleft : ∀ x ∈ a.leaves, ∀ y ∈ a.leaves,
          M x y = pairAge leafAge a d.2.1 x y := by
        intro x hx y hy
        exact (hM x (Finset.mem_union.mpr (Or.inl hx))
          y (Finset.mem_union.mpr (Or.inl hy))).trans (pairAge_left leafAge a b d hx hy)
      have hright : ∀ x ∈ b.leaves, ∀ y ∈ b.leaves,
          M x y = pairAge leafAge b d.2.2 x y := by
        intro x hx y hy
        exact (hM x (Finset.mem_union.mpr (Or.inr hx))
          y (Finset.mem_union.mpr (Or.inr hy))).trans (pairAge_right leafAge a b d ht.2.2 hx hy)
      change (M (witness a) (witness b),decode M a,decode M b) = d
      rw [hroot,ha ht.1 d.2.1 M hleft,hb ht.2.1 d.2.2 M hright]
      exact Prod.ext rfl (Prod.ext rfl rfl)

theorem decode_pairAge (leafAge : Copy → ℝ) (t : Genealogy Copy)
    (ht : t.WellLabelled) (d : Decoration t) : decode (pairAge leafAge t d) t = d := by
  exact decode_of_pair_agreement leafAge t ht d _ (fun _ _ _ _ => rfl)

theorem pairAge_injective (leafAge : Copy → ℝ) (t : Genealogy Copy)
    (ht : t.WellLabelled) : Function.Injective (pairAge leafAge t) := by
  intro d e h
  have hd := congrArg (fun M => decode M t) h
  simpa only [decode_pairAge leafAge t ht] using hd

/-- Measurability uses the actual product Borel spaces on real graft ages. -/
theorem pairAge_measurable (leafAge : Copy → ℝ) (t : Genealogy Copy) (x y : Copy) :
    Measurable (fun d : Decoration t => pairAge leafAge t d x y) := by
  induction t with
  | leaf z => exact measurable_const
  | graft a b ha hb =>
      by_cases hl : x ∈ a.leaves ∧ y ∈ a.leaves
      · simpa only [pairAge,if_pos hl,Decoration,decorationMeasurable,Function.comp_def] using
          ha.comp (measurable_snd.fst : Measurable (fun d : ℝ × Decoration a × Decoration b => d.2.1))
      · by_cases hr : x ∈ b.leaves ∧ y ∈ b.leaves
        · simpa only [pairAge,if_neg hl,if_pos hr,Decoration,decorationMeasurable,Function.comp_def] using
            hb.comp (measurable_snd.snd : Measurable (fun d : ℝ × Decoration a × Decoration b => d.2.2))
        · simpa only [pairAge,if_neg hl,if_neg hr,Decoration,decorationMeasurable] using
            (measurable_fst : Measurable (fun d : ℝ × Decoration a × Decoration b => d.1))

/-- For a fixed original genealogy, every decoded age is a fixed coordinate
of the input matrix or a recursively decoded child coordinate. -/
theorem decode_measurable (t : Genealogy Copy) :
    Measurable (fun M : Copy → Copy → ℝ => decode M t) := by
  induction t with
  | leaf z => exact measurable_const
  | graft a b ha hb =>
      have hroot : Measurable (fun M : Copy → Copy → ℝ => M (witness a) (witness b)) :=
        (measurable_pi_apply (witness b)).comp (measurable_pi_apply (witness a))
      simpa only [decode,Decoration,decorationMeasurable] using hroot.prodMk (ha.prodMk hb)

#print axioms witness_mem
#print axioms pairAge_left
#print axioms pairAge_right
#print axioms pairAge_cross
#print axioms decode_of_pair_agreement
#print axioms decode_pairAge
#print axioms pairAge_injective
#print axioms pairAge_measurable
#print axioms decode_measurable

end GProgram.G2.FaithfulPairAgeDecoration
