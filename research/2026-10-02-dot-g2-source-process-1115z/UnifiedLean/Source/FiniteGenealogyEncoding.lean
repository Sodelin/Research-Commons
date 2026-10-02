import UnifiedLean.Source.SourceForestSilentPruning
import Mathlib.Data.Fintype.Sum

/-!
# Constructed finite encoding of all well-labelled original-copy genealogies

Contributor: dot, 2026-10-02. The existing actual source genealogy datatype is
encoded, not replaced by a fitted finite-state model. A well-labelled tree's
height is strictly below its number of distinct original leaves, hence below
the finite original copy cap. The bounded code is constructed with a proved
left inverse. This supplies a genuine finite-state ingredient for the next
positive-rate source-kernel/semigroup construction; no stochastic closure is
claimed by this datatype lemma.
-/
namespace UnifiedLean.Source.FiniteGenealogyEncoding
open GProgram.SourceForest
open scoped Classical
variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy]

def genealogyHeight : Genealogy Copy → Nat
  | .leaf _ => 0
  | .graft a b => max (genealogyHeight a) (genealogyHeight b)+1

/-- Every binary shape up to bounded height, with its ORIGINAL copy labels. -/
def TreeCode (Copy : Type*) : Nat → Type _
  | 0 => Copy
  | n+1 => Copy ⊕ (TreeCode Copy n × TreeCode Copy n)

instance treeCodeFintype : ∀ n : Nat, Fintype (TreeCode Copy n)
  | 0 => inferInstanceAs (Fintype Copy)
  | n+1 => by
      letI := treeCodeFintype n
      change Fintype (Copy ⊕ (TreeCode Copy n × TreeCode Copy n))
      infer_instance

def decodeTree : (n : Nat) → TreeCode Copy n → Genealogy Copy
  | 0,x => .leaf x
  | n+1,.inl x => .leaf x
  | n+1,.inr (a,b) => .graft (decodeTree n a) (decodeTree n b)

def encodeTree : (n : Nat) → (t : Genealogy Copy) → genealogyHeight t ≤ n → TreeCode Copy n
  | 0,.leaf x,_ => x
  | 0,.graft a b,h => False.elim (by simp [genealogyHeight] at h)
  | n+1,.leaf x,_ => .inl x
  | n+1,.graft a b,h => .inr
      (encodeTree n a (by simp only [genealogyHeight] at h; omega),
       encodeTree n b (by simp only [genealogyHeight] at h; omega))

lemma decode_encode (n : Nat) (t : Genealogy Copy) (h : genealogyHeight t ≤ n) :
    decodeTree n (encodeTree n t h) = t := by
  induction n generalizing t with
  | zero =>
      cases t with
      | leaf x => rfl
      | graft a b => simp [genealogyHeight] at h
  | succ n ih =>
      cases t with
      | leaf x => rfl
      | graft a b =>
          simp only [encodeTree,decodeTree]
          rw [ih,ih]

abbrev HeightBoundedTree (Copy : Type*) (n : Nat) :=
  {t : Genealogy Copy // genealogyHeight t ≤ n}

noncomputable instance heightBoundedTreeFintype (n : Nat) :
    Fintype (HeightBoundedTree Copy n) :=
  Fintype.ofInjective (fun t : HeightBoundedTree Copy n => encodeTree n t.val t.property) (by
    intro a b h
    apply Subtype.ext
    have hh := congrArg (decodeTree n) h
    simpa only [decode_encode] using hh)

/-- Disjoint original labels, not a supplied shape/hidden graph budget, bound
the tree height. This covers every actually valid current source genealogy. -/
theorem wellLabelled_height_lt_leaves (t : Genealogy Copy) (ht : t.WellLabelled) :
    genealogyHeight t < t.leaves.card := by
  induction t with
  | leaf x => simp [genealogyHeight,Genealogy.leaves]
  | graft a b iha ihb =>
      obtain ⟨ha,hb,hd⟩ := ht
      have hA := iha ha
      have hB := ihb hb
      simp only [genealogyHeight,Genealogy.leaves,Finset.card_union_of_disjoint hd]
      omega

theorem wellLabelled_height_below_copy_cap (t : Genealogy Copy) (ht : t.WellLabelled) :
    genealogyHeight t < Fintype.card Copy :=
  (wellLabelled_height_lt_leaves t ht).trans_le (Finset.card_le_univ t.leaves)

abbrev WellLabelledTree (Copy : Type*) [DecidableEq Copy] := {t : Genealogy Copy // t.WellLabelled}

/-- Actual well-labelled genealogy space is finite by the constructed code. -/
noncomputable instance wellLabelledTreeFintype : Fintype (WellLabelledTree Copy) :=
  Fintype.ofInjective
    (fun t : WellLabelledTree Copy =>
      (⟨t.val,(wellLabelled_height_below_copy_cap t.val t.property).le⟩ :
        HeightBoundedTree Copy (Fintype.card Copy)))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun t : HeightBoundedTree Copy (Fintype.card Copy) => t.val) h)

/-- An ACTUAL existing live source genealogy supplies its own bounded code. -/
noncomputable def liveGenealogyCode {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (l : {l // l ∈ s.live}) : TreeCode Copy (Fintype.card Copy) :=
  encodeTree _ (s.genealogy l.val)
    (wellLabelled_height_below_copy_cap _ (hs.wellLabelled l.val l.property)).le

theorem liveGenealogyCode_decodes {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (l : {l // l ∈ s.live}) :
    decodeTree (Fintype.card Copy) (liveGenealogyCode s hs l) = s.genealogy l.val :=
  decode_encode _ _ _

#print axioms decode_encode
#print axioms wellLabelled_height_lt_leaves
#print axioms wellLabelled_height_below_copy_cap
#print axioms liveGenealogyCode_decodes
end UnifiedLean.Source.FiniteGenealogyEncoding
