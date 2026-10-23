import HardFamilyActionSignature
import EmptyInterventionTarget

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

L5 actual target preservation. With at least one available target, the
literal TCM contains exactly the baseline MAG's full marked observed
edges. Thus equality of WHOLE original-source classTarget outputs implies
baseline separation agreement. This is not replacing the target by a
skeleton. The nonempty-target hypothesis is essential; the separate
EmptyInterventionTarget source records the substantive k=0 correction.
-/

namespace RestrictedCausal.HardFamily

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation ProbabilitySource PartialQueries TranscriptDecoder
open FiniteTargetImage HPLTarget CommonObserved ProfileRegistry WeakInducing

universe v w z

theorem tcm_old_edge_iff {X : Type v} {S : Type w} {L : Type z}
    (D : SourceDAG X S L) (T : X → Prop) (available : ∃ t, T t)
    (x y : X) (ma mb : Mark) :
    (tcm D T).edge (.inl x) (.inl y) ma mb ↔ (mag D).edge x y ma mb := by
  constructor
  · rintro ⟨notOwn, t, a, b, atX, atY, edge⟩
    cases a with
    | none => cases atX
    | some a =>
        have sameA : a = x := Sum.inl.inj atX
        subst a
        cases b with
        | none => cases atY
        | some b =>
            have sameB : b = y := Sum.inl.inj atY
            subst b
            exact (old_mag_edge_iff D t.val x y ma mb).mp edge
  · intro edge
    obtain ⟨t, allowed⟩ := available
    refine ⟨?_, ⟨t, allowed⟩, some x, some y, rfl, rfl,
      (old_mag_edge_iff D t x y ma mb).mpr edge⟩
    rintro ⟨target, «first» | second⟩
    · cases «first».1
    · cases second.2

theorem mag_eq_of_tcm_eq {X : Type v} {S L S' L' : Type v}
    (D : SourceDAG X S L) (E : SourceDAG X S' L') (T : X → Prop)
    (available : ∃ t, T t) (same : tcm D T = tcm E T) : mag D = mag E := by
  apply markedGraph_eq
  intro x y ma mb
  rw [← tcm_old_edge_iff D T available x y ma mb,
    ← tcm_old_edge_iff E T available x y ma mb, same]

/-- A necessary consequence of equal FULL class outputs. The witness F
fits E's entire original baseline/indicator signature, not one queried row.
It has the actual marked TCM of D, so the old observed MAG is exactly equal. -/
theorem equal_classes_imply_baseline_agreement {X : Type v} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (available : ∃ t, T t) (D E : FiniteSource X)
    (same : classTarget T D = classTarget T E)
    (C : X → Prop) (x y : X) (different : x ≠ y) (xOutside : ¬ C x) (yOutside : ¬ C y) :
    ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition C) (Observed x) (Observed y) ↔
      ActiveConnection (arrowGraph E.dag.arrow) (SelectedCondition C) (Observed x) (Observed y) := by
  obtain ⟨code, member, decoded⟩ := (classTarget_image_exact T D (tcm D.dag T)).mpr
    ⟨D, (SameElementarySignature.refl T D).setwise, rfl⟩
  rw [same] at member
  obtain ⟨F, signature, target⟩ := (classTarget_image_exact T E (tcm D.dag T)).mp
    ⟨code, member, decoded⟩
  have sameMAG := mag_eq_of_tcm_eq F.dag D.dag T available target
  have fromDToF :
      ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition C) (Observed x) (Observed y) ↔
        ActiveConnection (arrowGraph F.dag.arrow) (SelectedCondition C) (Observed x) (Observed y) := by
    rw [selected_mag_connection_iff D.dag C x y xOutside yOutside,
      selected_mag_connection_iff F.dag C x y xOutside yOutside, sameMAG]
  exact fromDToF.trans (signature.elementary.baseline C x y different xOutside yOutside).symm

/-- The baseline and each rival have unequal original full marked-class
targets. The theorem requires k>0 explicitly, not merely in prose. -/
theorem baseline_class_ne_rival {k u : Nat} [LinearOrder (Labels k u)]
    (nonemptyTargets : 0 < k) (q : Index u) :
    classTarget Available (originalSource (k := k) none) ≠
      classTarget Available (originalSource (some q)) := by
  intro same
  have available : ∃ t : Labels k u, Available t := ⟨.inl ⟨0, nonemptyTargets⟩, True.intro⟩
  have firstOutside : ¬ exceptionalCondition (k := k) q (.inr q.first) := by
    change ¬ q.before q.first = true
    rw [q.before_first]
    decide
  have secondOutside : ¬ exceptionalCondition (k := k) q (.inr q.second) := by
    change ¬ q.before q.second = true
    rw [q.before_second]
    decide
  have agreement := equal_classes_imply_baseline_agreement Available available
    (originalSource (k := k) none) (originalSource (some q)) same
    (exceptionalCondition q) (.inr q.first) (.inr q.second)
    (fun h => q.distinct (Sum.inr.inj h)) firstOutside secondOutside
  rw [original_baseline_connection, original_baseline_connection] at agreement
  exact exceptional_pair_separated q (agreement.mp
    (baseline_untargeted_active (exceptionalCondition q) q.first q.second q.distinct))

end RestrictedCausal.HardFamily
