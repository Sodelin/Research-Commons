import EffectiveQueryEnumeration
import FiniteQueryPlan

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Exact G7 source/response/target/resource adapter. The target is the FULL
original-source marked-TCM equivalence-class image, represented injectively
by Boolean graph codes, not one TCM and not a product of indicator classes.
Original hidden and selection carrier sizes remain arbitrary finite sizes.
The finite registry supplies one common source for every named augmentation.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget ProfileRegistry FiniteTargetImage FiniteGraphDecision TranscriptDecoder
open ComputableCanonical QueryPlan

open GProgram.G7.ExactLawResourceGame

universe u v

/-- A specification, not the algorithm. Its original-source quantifier is
unbounded in both finite hidden-carrier sizes. The terminal algorithm is
the previously explicit finite `decodeHistory`, not this classical filter. -/
noncomputable def classTarget {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X) : Finset (TargetCode X T) := by
  classical
  exact Finset.univ.filter (fun b => ∃ E : FiniteSource X,
    SameSetwiseSignature T D E ∧ tcm E.dag T = decodeTarget b)

theorem classTarget_mem {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X) (b : TargetCode X T) :
    b ∈ classTarget T D ↔ ∃ E : FiniteSource X,
      SameSetwiseSignature T D E ∧ tcm E.dag T = decodeTarget b := by
  classical
  simp only [classTarget, Finset.mem_filter, Finset.mem_univ, true_and]

theorem classTarget_preserved {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {D E : FiniteSource X}
    (same : SameElementarySignature T D E) : classTarget T D = classTarget T E := by
  apply Finset.ext
  intro b
  rw [classTarget_mem, classTarget_mem]
  exact ⟨fun ⟨F, signature, graph⟩ => ⟨F, (same.symm.trans signature.elementary).setwise, graph⟩,
    fun ⟨F, signature, graph⟩ => ⟨F, (same.trans signature.elementary).setwise, graph⟩⟩

theorem classTarget_image_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X)
    (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ classTarget T D, decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G := by
  constructor
  · rintro ⟨b, member, graph⟩
    obtain ⟨E, signature, same⟩ := (classTarget_mem T D b).mp member
    exact ⟨E, signature, same.trans graph⟩
  · rintro ⟨E, signature, graph⟩
    let c := encode (originalProfile E.dag)
    have decoded : decodeTarget (codeTarget T c) = tcm E.dag T :=
      (codeTarget_correct T c).trans (codeSource_original_target T E).symm
    exact ⟨codeTarget T c,
      (classTarget_mem T D _).mpr ⟨E, signature, decoded.symm⟩, decoded.trans graph⟩

/-- Equality of graph-code sets is justified by injective decoding, not by
replacing the marked target with a weaker observational summary. -/
theorem decoder_equals_classTarget {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X)
    (m : X → X → Bool) (h : TranscriptDecoder.History X T)
    (recorded : MarginalsRecorded m h) (covered : RestrictedCoverage T m h)
    (honest : SourceConsistent D h) : decodeHistory T h = classTarget T D := by
  apply Finset.ext
  intro b
  rw [classTarget_mem]
  have exactGraph := restricted_history_target_exact T D m h recorded covered honest (decodeTarget b)
  constructor
  · intro member
    exact exactGraph.mp ⟨b, member, rfl⟩
  · intro witness
    obtain ⟨other, member, equal⟩ := exactGraph.mpr witness
    exact decodeTarget_injective equal ▸ member

/-- The source presentation may be the complete finite registry or the
original unbounded-size finite-source class. The response function remains
an explicit argument; its exact graphical contract is proved separately. -/
noncomputable def sourceGame {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool) :
    Experiment S (ElementaryAction X T) Bool (Finset (TargetCode X T)) Nat :=
  budgetExperiment (fun _ => True) (fun s => classTarget T (source s)) response (LegalAction T)

def ExactResponse {X : Type u} [DecidableEq X] {T : X → Prop} {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool) : Prop :=
  ∀ s a, PositiveAnswer (source s) a ↔ response s a = true

theorem game_consistent_iff {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] {S : Type v}
    (source : S → FiniteSource X) (response : S → ElementaryAction X T → Bool)
    (exactResponse : ExactResponse source response) (h : TranscriptDecoder.History X T) (s : S) :
    Consistent (sourceGame T source response) h s ↔ SourceConsistent (source s) h := by
  constructor
  · rintro ⟨_, answers⟩ row member
    exact (exactResponse s row.1).trans
      ((bool_eq_iff_truth_iff _ _).mp (answers row member))
  · intro honest
    refine ⟨True.intro, ?_⟩
    intro row member
    exact (bool_eq_iff_truth_iff _ _).mpr
      ((exactResponse s row.1).symm.trans (honest row member))

noncomputable def originalGame {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    Experiment (FiniteSource X) (ElementaryAction X T) Bool (Finset (TargetCode X T)) Nat :=
  sourceGame T id (fun D a => graphicalReply D a)

theorem original_response_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) : ExactResponse (id : FiniteSource X → FiniteSource X)
      (fun D (a : ElementaryAction X T) => graphicalReply D a) :=
  fun D a => graphical_reply_correct D a

noncomputable def registryGame {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    Experiment (RegistryCode X) (ElementaryAction X T) Bool (Finset (TargetCode X T)) Nat :=
  sourceGame T codeSource (fun c a => codeAnswer c a)

theorem registry_response_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) : ExactResponse (codeSource : RegistryCode X → FiniteSource X)
      (fun c (a : ElementaryAction X T) => codeAnswer c a) :=
  fun c a => (codeAnswer_correct c a).symm

/-- Completeness is for one code/source fitting ALL actions simultaneously,
including every named available indicator. It is not independent per-query
or per-indicator realizability. Full marked-class targets are equal too. -/
theorem registry_whole_source_coverage {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X) :
    ∃ c : RegistryCode X,
      (∀ a : ElementaryAction X T, (originalGame T).response D a = (registryGame T).response c a) ∧
      (originalGame T).target D = (registryGame T).target c := by
  let c := encode (originalProfile D.dag)
  have signature := codeSource_original_signature T D
  refine ⟨c, ?_, classTarget_preserved T signature⟩
  intro a
  apply (bool_eq_iff_truth_iff _ _).mpr
  exact (graphical_reply_correct D a).symm.trans
    ((answer_preserved signature a).trans (codeAnswer_correct c a).symm)

/-- Converse coverage is literal: every code denotes a valid common original
source. No source-size assumption or separate MAG realization oracle enters. -/
theorem registry_source_sound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (c : RegistryCode X) :
    (∀ a : ElementaryAction X T,
      (registryGame T).response c a = (originalGame T).response (codeSource c) a) ∧
      (registryGame T).target c = (originalGame T).target (codeSource c) := by
  refine ⟨?_, rfl⟩
  intro a
  apply (bool_eq_iff_truth_iff _ _).mpr
  exact (codeAnswer_correct c a).trans (graphical_reply_correct (codeSource c) a)

end RestrictedCausal.PartialQueries
