import G7FiniteReachability
import UnifiedLean.Source.SourceFiniteProjection
import Mathlib.Data.FinEnum

/-!
Executable enumeration of the actual finite original-source snapshots and
full selected views. Contributor: dot, 2026-10-10, continuing the accepted
G7 compiler formalization and the existing finite genealogy encoding.

The input carriers have explicit FinEnum instances; the numbered original
Fin carriers supply these without a source-size assumption. Tree enumeration
uses the proved original-copy height cap. Source validity is decided from
finite forest predicates and the proved vertex-count reachability algorithm.
No validity oracle, arbitrary finite-state replacement, or choice of a source
representative is an input. This is the executable state/index layer for the
population-split coefficient compiler, not its complete coefficient theorem.
-/
namespace GProgram.G7.EffectiveSourceEnumeration
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteGenealogyEncoding UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

instance boolEnumeration : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro b; cases b <;> simp)

instance optionEnumeration {A : Type*} [FinEnum A] : FinEnum (Option A) :=
  FinEnum.ofList (none :: (FinEnum.toList A).map some) (by
    intro a; cases a <;> simp)

instance treeCodeEnumeration : (n : Nat) → FinEnum (TreeCode Copy n)
  | 0 => inferInstanceAs (FinEnum Copy)
  | n+1 => by
      letI := treeCodeEnumeration n
      exact inferInstanceAs (FinEnum (Copy ⊕ (TreeCode Copy n × TreeCode Copy n)))

instance wellLabelledDecidable : (t : Genealogy Copy) → Decidable t.WellLabelled
  | .leaf _ => isTrue trivial
  | .graft a b => by
      letI := wellLabelledDecidable a
      letI := wellLabelledDecidable b
      exact inferInstanceAs (Decidable (a.WellLabelled ∧ b.WellLabelled ∧
        Disjoint a.leaves b.leaves))

abbrev AdmissibleTreeCode (Copy : Type*) [DecidableEq Copy] [Fintype Copy] :=
  {c : TreeCode Copy (Fintype.card Copy) // (decodeTree _ c).WellLabelled}

def decodeAdmissibleTree (c : AdmissibleTreeCode Copy) : WellLabelledTree Copy :=
  ⟨decodeTree _ c.val, c.property⟩

theorem decodeAdmissibleTree_surjective :
    Function.Surjective (decodeAdmissibleTree (Copy := Copy)) := by
  intro t
  let h := (wellLabelled_height_below_copy_cap t.val t.property).le
  let c := encodeTree (Fintype.card Copy) t.val h
  have hc : (decodeTree (Fintype.card Copy) c).WellLabelled := by
    simpa only [c, decode_encode] using t.property
  exact ⟨⟨c,hc⟩, Subtype.ext (decode_encode _ _ _)⟩

/-- Exhaustive, deduplicated bounded-code enumeration of the existing trees. -/
instance treeEnumeration : FinEnum (WellLabelledTree Copy) :=
  FinEnum.ofSurjective decodeAdmissibleTree decodeAdmissibleTree_surjective

instance locationEnumeration : FinEnum (Location V E) :=
  FinEnum.ofEquiv (V ⊕ (E ⊕ V)) locationEquiv

def snapshotEncoding : Snapshot V E Copy ≃
    (Finset Copy × (Copy → Copy) × (Copy → Option (WellLabelledTree Copy)) ×
      (Copy → Option (Location V E)) × (V → Bool)) where
  toFun s := (s.live,s.ancestor,s.genealogy,s.population,s.register)
  invFun s := ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equality is fieldwise; it does not search the large snapshot enumeration. -/
instance snapshotDecidableEq : DecidableEq (Snapshot V E Copy) := fun a b =>
  decidable_of_iff (a.live = b.live ∧ a.ancestor = b.ancestor ∧
    a.genealogy = b.genealogy ∧ a.population = b.population ∧ a.register = b.register)
    ⟨fun h => Snapshot.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2,
     fun h => by cases h; exact ⟨rfl,rfl,rfl,rfl,rfl⟩⟩

instance snapshotEnumeration : FinEnum (Snapshot V E Copy) :=
  FinEnum.ofEquiv _ snapshotEncoding

/-- Same inherited decoder, with an executable body rather than a
noncomputable declaration marker. -/
def decode (root : V) (s : Snapshot V E Copy) : State V E Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy l := match s.genealogy l with
    | some t => t.val
    | none => .leaf l
  location l := match s.population l with
    | some p => p
    | none => .node root
  register := s.register
  history := []

theorem decode_eq (root : V) (s : Snapshot V E Copy) :
    decode root s = decodeSnapshot root s := rfl

def forestValidDecidable (s : State V E Copy) : Decidable (Valid s) :=
  decidable_of_iff
    ((∀ x, s.ancestor x ∈ s.live) ∧
     (∀ l ∈ s.live, s.ancestor l = l) ∧
     (∀ l ∈ s.live, ∀ x, x ∈ (s.genealogy l).leaves ↔ s.ancestor x = l) ∧
     (∀ l ∈ s.live, (s.genealogy l).WellLabelled))
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,
     fun h => ⟨h.ancestor_live,h.representative,h.leaf_fiber,h.wellLabelled⟩⟩

def directedReachDecidable (G : EdgeGraph V E) (a b : V) : Decidable (G.DReach a b) := by
  letI : DecidableRel G.DStep := fun x y =>
    inferInstanceAs (Decidable (∃ e, G.source e = x ∧ G.target e = y))
  exact GProgram.G7.FiniteReachability.decideReach G.DStep a b

def descendsDecidable (N : RootedBinary V E X) (p : Location V E) (x : X) :
    Decidable (DescendsTo N p x) := by
  letI : DecidableRel N.graph.DReach := directedReachDecidable N.graph
  cases p with
  | node v => exact inferInstanceAs (Decidable (N.graph.DReach v (N.leaf x)))
  | edge e => exact inferInstanceAs
      (Decidable (N.graph.DReach (N.graph.target e) (N.leaf x)))
  | rootPopulation r => exact inferInstanceAs
      (Decidable (r = N.root ∧ N.graph.DReach r (N.leaf x)))

def sourceValidDecidable (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) : Decidable (SourceValid N sample s) := by
  letI := forestValidDecidable s
  letI : DecidablePred (fun x => DescendsTo N (copyLocation s x) (sample x)) :=
    fun x => descendsDecidable N (copyLocation s x) (sample x)
  exact decidable_of_iff
    (Valid s ∧ ∀ x, DescendsTo N (copyLocation s x) (sample x))
    ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.forest,h.original_descendant⟩⟩

/-- The original admitted snapshot subtype is enumerated, with its exact
SourceValid predicate decided by the explicit bounded graph algorithm. -/
instance codeEnumeration (N : RootedBinary V E X) (sample : Copy → X) :
    FinEnum (Code N sample) := by
  letI : DecidablePred (fun s : Snapshot V E Copy =>
      SourceValid N sample (decodeSnapshot N.root s)) :=
    fun s => sourceValidDecidable N sample (decode N.root s)
  exact inferInstanceAs (FinEnum {s : Snapshot V E Copy //
    SourceValid N sample (decodeSnapshot N.root s)})

def view (root : V) (s : Snapshot V E Copy) (keep : Finset Copy) :
    SelectedView V E Copy where
  genealogy x := if x ∈ keep then ((decode root s).genealogy (s.ancestor x)).prune keep
    else none
  population x := if x ∈ keep then some (copyLocation (decode root s) x) else none
  register := s.register

theorem view_eq (root : V) (s : Snapshot V E Copy) (keep : Finset Copy) :
    view root s keep = selectedView (decodeSnapshot root s) keep := rfl

instance viewDecidableEq : DecidableEq (SelectedView V E Copy) := fun a b =>
  decidable_of_iff (a.genealogy = b.genealogy ∧ a.population = b.population ∧
    a.register = b.register)
    ⟨fun h => SelectedView.ext h.1 h.2.1 h.2.2,
     fun h => by cases h; exact ⟨rfl,rfl,rfl⟩⟩

def project (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : SelectedIndex N sample keep :=
  ⟨view N.root s.val keep, ⟨s,rfl⟩⟩

instance selectedEnumeration (N : RootedBinary V E X) (sample : Copy → X)
    (keep : Finset Copy) : FinEnum (SelectedIndex N sample keep) :=
  FinEnum.ofSurjective (project N keep) (by
    intro v
    obtain ⟨s,hs⟩ := v.property
    exact ⟨s,Subtype.ext hs⟩)

/-- Finite existential search uses the executable enumeration rather than
the legacy noncomputable Fintype instance for source snapshots. -/
def enumeratedExistsDecidable {A : Type*} [FinEnum A] (p : A → Prop)
    [DecidablePred p] : Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ FinEnum.toList A, p a)
    ⟨fun ⟨a,_,h⟩ => ⟨a,h⟩,fun ⟨a,h⟩ => ⟨a,FinEnum.mem_toList a,h⟩⟩

/-- List.choose performs the first successful finite test. Its proof argument
only certifies that the explicit exhaustive search cannot fail. -/
def findRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) : Code N sample :=
  List.choose (fun s => view N.root s.val keep = v.val)
    (FinEnum.toList (Code N sample)) (by
      obtain ⟨s,hs⟩ := v.property
      exact ⟨s,FinEnum.mem_toList s,hs⟩)

theorem findRepresentative_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    selectedView (state (findRepresentative N keep v)) keep = v.val :=
  List.choose_property _ _ _

theorem project_findRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    projection N keep (findRepresentative N keep v) = v :=
  Subtype.ext (findRepresentative_view N keep v)

end GProgram.G7.EffectiveSourceEnumeration
