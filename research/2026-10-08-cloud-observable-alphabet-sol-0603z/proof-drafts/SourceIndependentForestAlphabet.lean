import UnifiedLean.Source.FiniteGenealogyEncoding
import UnifiedLean.Source.UnrankedGenealogyObservation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
EXPERIMENTAL SOURCE/HAND; all new bodies compiler UNCHECKED/outside179.
Finite observed alphabet depends only on external Copy and finite Tag.
The actual provider CONSTRUCTS bounded TreeCode, proves its decode inverse and
derives Fintype WellLabelledTree. No tree enumeration/injection is a premise.
No hidden population/register coordinate is encoded in this observer.
-/
namespace CloudG6.SourceIndependentForestAlphabet

open GProgram.SourceForest
open UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical

variable {Copy Tag : Type*} [DecidableEq Copy] [Fintype Copy] [Fintype Tag]

/-- Image of the source provider's CONSTRUCTED finite bounded tree carrier. -/
noncomputable def wellTreeAlphabet (Copy : Type*) [DecidableEq Copy] [Fintype Copy] :
    Finset (UnrankedTree Copy) :=
  Finset.univ.image (fun t : WellLabelledTree Copy => toUnranked t.val)

theorem mem_wellTreeAlphabet (q : UnrankedTree Copy) :
    q ∈ wellTreeAlphabet Copy ↔ treeWellLabelled q := by
  refine Quotient.inductionOn q ?_
  intro tree
  change toUnranked tree ∈ wellTreeAlphabet Copy ↔ tree.WellLabelled
  constructor
  · intro h
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
    exact (unordered_wellLabelled ((toUnranked_eq_iff t.val tree).mp ht)).mp t.property
  · intro h
    exact Finset.mem_image.mpr ⟨⟨tree, h⟩, Finset.mem_univ _, rfl⟩

/-- Proper forests partition the fixed external Copy labels. Equal tags do
not contract tree nodes; no ancestor, population or register is observed. -/
def ProperForest (F : Finset (UnrankedTree Copy)) : Prop :=
  (∀ q ∈ F, treeWellLabelled q) ∧
  (∀ q ∈ F, ∀ r ∈ F, q ≠ r → Disjoint (treeLeaves q) (treeLeaves r)) ∧
  (∀ x : Copy, ∃ q ∈ F, x ∈ treeLeaves q)

noncomputable def properForestAlphabet (Copy : Type*) [DecidableEq Copy] [Fintype Copy] :
    Finset (Finset (UnrankedTree Copy)) :=
  (wellTreeAlphabet Copy).powerset.filter (fun F => ProperForest F)

theorem mem_properForestAlphabet (F : Finset (UnrankedTree Copy)) :
    F ∈ properForestAlphabet Copy ↔ ProperForest F := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, h⟩
    intro q hq
    exact (mem_wellTreeAlphabet q).mpr (h.1 q hq)

abbrev ProperForestCode (Copy : Type*) [DecidableEq Copy] [Fintype Copy] :=
  {F : Finset (UnrankedTree Copy) // ProperForest F}

noncomputable instance properForestCodeFintype : Fintype (ProperForestCode Copy) :=
  Fintype.subtype (properForestAlphabet Copy) mem_properForestAlphabet

/-- The actual source's no-duplicate-leaf and ancestry-fibre proofs supply
membership, for ANY finite hidden graph/population/register carrier. -/
theorem actual_source_full_forest_proper {V E : Type*} (s : State V E Copy) (hs : Valid s) :
    ProperForest (sourceUnrankedForest s Finset.univ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact source_unranked_forest_wellLabelled s hs Finset.univ hq
  · intro q hq r hr hqr
    exact source_unranked_forest_disjoint s hs Finset.univ hq hr hqr
  · intro x
    exact (source_unranked_forest_covers s hs Finset.univ x).mpr (Finset.mem_univ x)

abbrev RawObservedRecord (Copy Tag : Type*) [DecidableEq Copy] :=
  Finset (UnrankedTree Copy) × (Copy → Copy → Tag)

abbrev FiniteObservedRecord (Copy Tag : Type*) [DecidableEq Copy] [Fintype Copy] :=
  ProperForestCode Copy × (Copy → Copy → Tag)

/-- Source-independent finite record, including the COMPLETE Copy-pair tags.
Finiteness of the matrix is derived from finite Copy and Tag by Pi instances. -/
noncomputable instance finiteObservedRecordFintype : Fintype (FiniteObservedRecord Copy Tag) :=
  inferInstanceAs (Fintype (ProperForestCode Copy × (Copy → Copy → Tag)))

def forgetFiniteRecord (a : FiniteObservedRecord Copy Tag) : RawObservedRecord Copy Tag :=
  (a.1.val, a.2)

theorem forgetFiniteRecord_injective :
    Function.Injective (forgetFiniteRecord (Copy := Copy) (Tag := Tag)) := by
  intro a b h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- A TOTAL observable-only reader on the unrestricted payload. The invalid
case is not a source event: membership is derived for every actual Code. -/
noncomputable def finiteRecordReader (a : RawObservedRecord Copy Tag) :
    Option (FiniteObservedRecord Copy Tag) :=
  if h : ProperForest a.1 then some (⟨a.1, h⟩, a.2) else none

theorem finiteRecordReader_forget (a : FiniteObservedRecord Copy Tag) :
    finiteRecordReader (forgetFiniteRecord a) = some a := by
  rcases a with ⟨⟨F, hF⟩, B⟩
  simp only [forgetFiniteRecord, finiteRecordReader, dif_pos hF]

/-- Exact finite reader of an ACTUAL whole source forest and arbitrary typed
finite tag matrix. No finite-reader injection witness is supplied. -/
theorem finiteRecordReader_actual {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (B : Copy → Copy → Tag) :
    finiteRecordReader (sourceUnrankedForest s Finset.univ, B) =
      some (⟨sourceUnrankedForest s Finset.univ, actual_source_full_forest_proper s hs⟩, B) := by
  simp only [finiteRecordReader, dif_pos (actual_source_full_forest_proper s hs)]

end CloudG6.SourceIndependentForestAlphabet
