import UnifiedLean.Source.E8PaperGammaAdmission
import E8SCFG2ProviderBoundaryContract
import Mathlib.Data.List.OfFn

/-!
# Bounded parent-event decoding from the pinned SCFG2 child schemas

This module uses ALL57 literal normalized-child schemas already checked in
E8SCFG2ProviderBoundaryContract. Local family/split/helper/valid-key premises
prove descendant right endpoints bounded by the original root. Normalized
1-based integer coordinates then construct Gamma's Fin n source events.

A SchemaTree is finite syntax for the child-schema relation, not a complete
admission of a generated production, an executed C++ tree or a legal RNA.
Generated-list/execution/continuation-fuel, BE fixed ownership, Gamma geometry,
physical weights, rendering and classifier refinement remain separate. In
particular no old span-first schedule DAG or probability law is inferred here.
-/
noncomputable section
open scoped Classical
namespace UnifiedLean.Source.E8SCFG2RootEventDecoder
open E8SCFG2RuntimeChildAdapter E8SCFG2ProviderBoundaryContract
open UnifiedLean.Source.E8PaperGammaAdmission

/-- Local schema certificates. Children are indexed by SLOT, preserving
independence of distinct occurrences even if two child keys happen to agree.
The relation is weaker than actual full candidate-generation admissibility. -/
inductive SchemaTree (partner : ℤ → ℤ) : ItemKey → Type where
  | node {key : ItemKey} (rule : RuleId) (split : RuleSplit)
      (valid : ValidItemKey key)
      (family : RuleFamily rule key.nonterminal)
      (guard : SourceGuard partner key rule split)
      (children : (idx : Fin (normalizedChildren partner key rule split).length) →
        SchemaTree partner ((normalizedChildren partner key rule split).get idx)) :
      SchemaTree partner key

/-- Actual 1-based-to-zero-based position conversion; the lower/upper domain
facts are supplied before conversion, not obtained by clipping/wrapping. -/
def positionIndex (n : ℕ) (x : ℤ) (hpositive : 1 ≤ x) (hupper : x ≤ (n : ℤ)) : Fin n :=
  ⟨(x - 1).toNat, by omega⟩

theorem positionIndex_roundtrip (n : ℕ) (x : ℤ)
    (hpositive : 1 ≤ x) (hupper : x ≤ (n : ℤ)) :
    ((positionIndex n x hpositive hupper).val : ℤ) + 1 = x := by
  simp only [positionIndex]
  omega

/-- Domain conversion of a formal source parent. The family is unchanged;
canonical pairing/strict orientation are later Gamma/source-admission gates. -/
def eventFromKey (n : ℕ) (key : ItemKey) (hv : ValidItemKey key)
    (hupper : key.j ≤ (n : ℤ)) : SourceEvent n where
  family := key.nonterminal
  pair := (positionIndex n key.i hv.1 (le_trans hv.2.1 hupper),
    positionIndex n key.j (le_trans hv.1 hv.2.1) hupper)

theorem eventFromKey_exact_coordinates (n : ℕ) (key : ItemKey)
    (hv : ValidItemKey key) (hupper : key.j ≤ (n : ℤ)) :
    (eventFromKey n key hv hupper).family = key.nonterminal ∧
    ((eventFromKey n key hv hupper).pair.1.val : ℤ) + 1 = key.i ∧
    ((eventFromKey n key hv hupper).pair.2.val : ℤ) + 1 = key.j := by
  exact ⟨rfl,
    positionIndex_roundtrip n key.i hv.1 (le_trans hv.2.1 hupper),
    positionIndex_roundtrip n key.j (le_trans hv.1 hv.2.1) hupper⟩

/-- The full source-schema child bound is reused to propagate the root
interval bound. No all-descendant bound is a constructor field. -/
theorem child_upper_from_local_guard (partner : ℤ → ℤ) (n : ℕ) (key : ItemKey)
    (rule : RuleId) (split : RuleSplit) (hf : RuleFamily rule key.nonterminal)
    (hg : SourceGuard partner key rule split) (hupper : key.j ≤ (n : ℤ))
    (idx : Fin (normalizedChildren partner key rule split).length) :
    ((normalizedChildren partner key rule split).get idx).j ≤ (n : ℤ) := by
  exact le_trans (source_normalized_child_right_bound partner key rule split hf hg
    ((normalizedChildren partner key rule split).get idx) (List.get_mem _ idx)) hupper

/-- Recursive construction of all parent events from locally certified
schemas. Existing source child-boundary theorem supplies each recursive bound. -/
def boundedEvents (partner : ℤ → ℤ) (n : ℕ) {key : ItemKey}
    (tree : SchemaTree partner key) : key.j ≤ (n : ℤ) → List (SourceEvent n) := by
  induction tree with
  | @node key rule split hv hf hg children ih =>
    intro hupper
    exact eventFromKey n key hv hupper ::
      (List.ofFn (fun idx => ih idx
        (child_upper_from_local_guard partner n key rule split hf hg hupper idx))).flatten

/-- Independent source ROOT literal, not a renamed paper carrier. -/
def rootKey (n : ℕ) : ItemKey := ⟨.W, 1, (n : ℤ), -1, -1⟩

def rootEvents (partner : ℤ → ℤ) (n : ℕ) (tree : SchemaTree partner (rootKey n)) :
    List (SourceEvent n) := boundedEvents partner n tree (by rfl)

/-- Once an actual supported finite trace is decoded to this schema syntax,
its Gamma event stream is constructed. The decoder itself is still DATA whose
executed/generated-list correctness must be established, not a probability
identity or an actual C++ extraction proof. -/
def eventsFromDecodedRoot {Trace : Type*} (partner : ℤ → ℤ) (n : ℕ)
    (decoder : Trace → SchemaTree partner (rootKey n)) : Trace → List (SourceEvent n) :=
  fun t => rootEvents partner n (decoder t)

#print axioms positionIndex_roundtrip
#print axioms eventFromKey_exact_coordinates
#print axioms child_upper_from_local_guard
#print axioms boundedEvents
#print axioms rootEvents
end UnifiedLean.Source.E8SCFG2RootEventDecoder
