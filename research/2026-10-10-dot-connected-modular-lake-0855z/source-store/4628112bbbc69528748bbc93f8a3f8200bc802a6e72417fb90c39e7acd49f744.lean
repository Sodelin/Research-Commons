import UnifiedLean.Source.FiniteGenealogyEncoding
import UnifiedLean.Source.SourceForestSilentPruning

/-!
# Finite snapshot of the existing original labelled source state

Contributor: dot, 2026-10-02. Encodes actual live genealogies, ancestry, original
population IDs and shared registers. Only dead-representative garbage and event
history are omitted; full unranked-output genealogy is retained (with the old
internal ordered encoding). Decoding preserves the inherited source invariant
and the exact selected internal view. This is for a GIVEN finite original graph
and copy cap, not a graph-size budget, G3 recognition decision, or a stochastic
kernel/biological-law completion.
-/
namespace UnifiedLean.Source.FiniteSourceSnapshot
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.FiniteGenealogyEncoding
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

/-- Separate constructor tags keep original edge IDs and ancestral root IDs. -/
def locationEquiv : Location V E ≃ V ⊕ (E ⊕ V) where
  toFun
    | .node v => .inl v
    | .edge e => .inr (.inl e)
    | .rootPopulation v => .inr (.inr v)
  invFun
    | .inl v => .node v
    | .inr (.inl e) => .edge e
    | .inr (.inr v) => .rootPopulation v
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with v | (e | v) <;> rfl

noncomputable instance locationFintype : Fintype (Location V E) :=
  Fintype.ofEquiv (V ⊕ (E ⊕ V)) locationEquiv.symm

@[ext] structure Snapshot (V E Copy : Type*) [DecidableEq Copy] where
  live : Finset Copy
  ancestor : Copy → Copy
  genealogy : Copy → Option (WellLabelledTree Copy)
  population : Copy → Option (Location V E)
  register : V → Bool

noncomputable def snapshotEquiv : Snapshot V E Copy ≃
    (Finset Copy × (Copy → Copy) × (Copy → Option (WellLabelledTree Copy)) ×
      (Copy → Option (Location V E)) × (V → Bool)) where
  toFun s := (s.live,s.ancestor,s.genealogy,s.population,s.register)
  invFun s := ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2⟩
  left_inv s := rfl
  right_inv s := rfl

noncomputable instance snapshotFintype : Fintype (Snapshot V E Copy) :=
  Fintype.ofEquiv _ snapshotEquiv.symm

noncomputable def encodeSnapshot (s : State V E Copy) (hs : Valid s) : Snapshot V E Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy l := if h : l ∈ s.live then some ⟨s.genealogy l,hs.wellLabelled l h⟩ else none
  population l := if l ∈ s.live then some (s.location l) else none
  register := s.register

/-- The existing State representation is reconstructed on all live operands.
Dead garbage and ranked history are irrelevant to this snapshot interface. -/
noncomputable def decodeSnapshot (root : V) (s : Snapshot V E Copy) : State V E Copy where
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

lemma decode_encode_live_genealogy (root : V) (s : State V E Copy) (hs : Valid s)
    {l : Copy} (hl : l ∈ s.live) :
    (decodeSnapshot root (encodeSnapshot s hs)).genealogy l = s.genealogy l := by
  simp only [decodeSnapshot,encodeSnapshot,dif_pos hl]

lemma decode_encode_live_population (root : V) (s : State V E Copy) (hs : Valid s)
    {l : Copy} (hl : l ∈ s.live) :
    (decodeSnapshot root (encodeSnapshot s hs)).location l = s.location l := by
  simp only [decodeSnapshot,encodeSnapshot,if_pos hl]

/-- Every selected ORIGINAL copy still uses its actual current live ancestor. -/
lemma decode_encode_copyLocation (root : V) (s : State V E Copy) (hs : Valid s) (x : Copy) :
    copyLocation (decodeSnapshot root (encodeSnapshot s hs)) x = copyLocation s x := by
  change (decodeSnapshot root (encodeSnapshot s hs)).location (s.ancestor x) = _
  exact decode_encode_live_population root s hs (hs.ancestor_live x)

theorem decode_encode_valid (root : V) (s : State V E Copy) (hs : Valid s) :
    Valid (decodeSnapshot root (encodeSnapshot s hs)) := by
  constructor
  · exact hs.ancestor_live
  · exact hs.representative
  · intro l hl x
    change x ∈ ((decodeSnapshot root (encodeSnapshot s hs)).genealogy l).leaves ↔ s.ancestor x = l
    rw [decode_encode_live_genealogy root s hs hl]
    exact hs.leaf_fiber l hl x
  · intro l hl
    rw [decode_encode_live_genealogy root s hs hl]
    exact hs.wellLabelled l hl

/-- Same original graph, sample assignment and source populations. No source
validity/kernel equation is inserted as a new asserted contract field. -/
theorem decode_encode_sourceValid [Fintype X] (N : RootedBinary V E X)
    (sample : Copy → X) (s : State V E Copy) (hs : SourceValid N sample s) :
    SourceValid N sample (decodeSnapshot N.root (encodeSnapshot s hs.forest)) := by
  refine ⟨decode_encode_valid N.root s hs.forest,?_⟩
  intro x
  rw [decode_encode_copyLocation N.root s hs.forest x]
  exact hs.original_descendant x

/-- Snapshot encoding keeps the whole selected genealogy/population/register
interface exactly. It is not an observed-data sufficiency theorem. -/
theorem decode_encode_selectedView (root : V) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) :
    selectedView (decodeSnapshot root (encodeSnapshot s hs)) keep = selectedView s keep := by
  apply SelectedView.ext
  · funext x
    unfold selectedView selectedGenealogy
    change (if x ∈ keep then
      ((decodeSnapshot root (encodeSnapshot s hs)).genealogy (s.ancestor x)).prune keep
      else none) = _
    rw [decode_encode_live_genealogy root s hs (hs.ancestor_live x)]
  · funext x
    change (if x ∈ keep then some (copyLocation (decodeSnapshot root (encodeSnapshot s hs)) x)
      else none) = (if x ∈ keep then some (copyLocation s x) else none)
    rw [decode_encode_copyLocation root s hs x]
  · rfl

/-- Genuine finite original-source snapshot carrier, parameterized by the
unchanged original graph and SAME sample assignment. -/
abbrev AdmittedSnapshot [Fintype X] (N : RootedBinary V E X) (sample : Copy → X) :=
  {s : Snapshot V E Copy // SourceValid N sample (decodeSnapshot N.root s)}

noncomputable instance admittedSnapshotFintype [Fintype X]
    (N : RootedBinary V E X) (sample : Copy → X) : Fintype (AdmittedSnapshot N sample) := by
  unfold AdmittedSnapshot
  infer_instance

/-- Every existing actually source-valid state yields an admitted finite code. -/
noncomputable def admittedCode [Fintype X] (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) : AdmittedSnapshot N sample :=
  ⟨encodeSnapshot s hs.forest,decode_encode_sourceValid N sample s hs⟩

#print axioms decode_encode_valid
#print axioms decode_encode_sourceValid
#print axioms decode_encode_selectedView
#print axioms admittedSnapshotFintype
end UnifiedLean.Source.FiniteSourceSnapshot
