import G2FaithfulPairAgeDecoration
import UnifiedLean.Source.UnrankedGenealogyObservation

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED derivative: no compiler has run on these new declarations.
The real-age provider and original unordered genealogy provider are imported
unchanged. Tags retain every binary graft, including repeated tags.
No Inhabited/Nonempty Copy, chronology sorting or source-law premise is added.
-/

namespace CloudG3.FiniteTagDecoder

universe u v

open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical

variable {Copy : Type u} [Fintype Copy] [DecidableEq Copy]
variable {Tag : Type v}

/-- A tag at every internal graft of the SUPPLIED actual binary genealogy. -/
noncomputable def TagDecoration (Tag : Type v) : Genealogy Copy → Type v
  | .leaf _ => PUnit
  | .graft a b => Tag × TagDecoration Tag a × TagDecoration Tag b

/-- Finite tags give finitely many decorations on each supplied finite tree. -/
noncomputable instance tagDecorationFintype [Fintype Tag] :
    (t : Genealogy Copy) → Fintype (TagDecoration Tag t) :=
  fun t => Genealogy.rec (Copy := Copy)
    (motive := fun u => Fintype (TagDecoration Tag u))
    (fun _ => inferInstanceAs (Fintype PUnit))
    (fun a b ha hb => by
      letI : Fintype (TagDecoration Tag a) := ha
      letI : Fintype (TagDecoration Tag b) := hb
      exact inferInstanceAs (Fintype (Tag × TagDecoration Tag a × TagDecoration Tag b))) t

/-- Pointwise age binning preserves the supplied tree's full graft structure. -/
noncomputable def mapBinDecoration (bin : ℝ → Tag) :
    (t : Genealogy Copy) → Decoration t → TagDecoration Tag t
  | .leaf _,_ => PUnit.unit
  | .graft a b,d =>
      (bin d.1,mapBinDecoration bin a d.2.1,mapBinDecoration bin b d.2.2)

/-- The very same genuine cross-child witnesses as the reviewed age decoder. -/
noncomputable def decodeTags (M : Copy → Copy → Tag) :
    (t : Genealogy Copy) → TagDecoration Tag t
  | .leaf _ => PUnit.unit
  | .graft a b =>
      (M (witness a) (witness b),decodeTags M a,decodeTags M b)

/-- Naturality holds for every matrix; actual-tree correctness is inherited
only in the following theorem through the proved real-age decoder inverse. -/
theorem decodeTags_map_decode (bin : ℝ → Tag) (M : Copy → Copy → ℝ)
    (t : Genealogy Copy) :
    decodeTags (fun x y => bin (M x y)) t = mapBinDecoration bin t (decode M t) := by
  induction t with
  | leaf z => rfl
  | graft a b ha hb =>
      change (bin (M (witness a) (witness b)),
        decodeTags (fun x y => bin (M x y)) a,
        decodeTags (fun x y => bin (M x y)) b) =
        (bin (M (witness a) (witness b)),
        mapBinDecoration bin a (decode M a),mapBinDecoration bin b (decode M b))
      rw [ha,hb]

/-- The source-faithful finite-tag decoder: topology is supplied, never inferred
by sorting or identifying equal numerical tags. -/
theorem decodeTags_bin_pairAge (bin : ℝ → Tag) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (ht : t.WellLabelled) (d : Decoration t) :
    decodeTags (fun x y => bin (pairAge leafAge t d x y)) t =
      mapBinDecoration bin t d := by
  rw [decodeTags_map_decode,decode_pairAge leafAge t ht d]

/-- An independently supplied matrix need agree only on actual leaf pairs. -/
theorem decodeTags_bin_of_pair_agreement (bin : ℝ → Tag) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (ht : t.WellLabelled) (d : Decoration t)
    (M : Copy → Copy → ℝ)
    (hM : ∀ x ∈ t.leaves, ∀ y ∈ t.leaves, M x y = pairAge leafAge t d x y) :
    decodeTags (fun x y => bin (M x y)) t = mapBinDecoration bin t d := by
  rw [decodeTags_map_decode,decode_of_pair_agreement leafAge t ht d M hM]

/-- Explicit tagged binary trees for the unordered readout. -/
inductive TaggedTree (Copy : Type*) (Tag : Type*)
  | leaf : Copy → TaggedTree Copy Tag
  | graft : Tag → TaggedTree Copy Tag → TaggedTree Copy Tag → TaggedTree Copy Tag

def underlying : TaggedTree Copy Tag → Genealogy Copy
  | .leaf x => .leaf x
  | .graft _ a b => .graft (underlying a) (underlying b)

noncomputable def toTaggedTree :
    (t : Genealogy Copy) → TagDecoration Tag t → TaggedTree Copy Tag
  | .leaf x,_ => .leaf x
  | .graft a b,d => .graft d.1 (toTaggedTree a d.2.1) (toTaggedTree b d.2.2)

noncomputable def toAgeTree :
    (t : Genealogy Copy) → Decoration t → TaggedTree Copy ℝ
  | .leaf x,_ => .leaf x
  | .graft a b,d => .graft d.1 (toAgeTree a d.2.1) (toAgeTree b d.2.2)

def mapTags {Other : Type*} (f : Tag → Other) : TaggedTree Copy Tag → TaggedTree Copy Other
  | .leaf x => .leaf x
  | .graft v a b => .graft (f v) (mapTags f a) (mapTags f b)

theorem underlying_toTaggedTree (t : Genealogy Copy) (d : TagDecoration Tag t) :
    underlying (toTaggedTree t d) = t := by
  induction t with
  | leaf z => rfl
  | graft a b ha hb =>
      change Genealogy.graft (underlying (toTaggedTree a d.2.1))
        (underlying (toTaggedTree b d.2.2)) = .graft a b
      rw [ha,hb]

theorem underlying_mapTags {Other : Type*} (f : Tag → Other) (t : TaggedTree Copy Tag) :
    underlying (mapTags f t) = underlying t := by
  induction t with
  | leaf x => rfl
  | graft v a b ha hb =>
      change Genealogy.graft (underlying (mapTags f a))
        (underlying (mapTags f b)) = .graft (underlying a) (underlying b)
      rw [ha,hb]

theorem toTaggedTree_mapBinDecoration (bin : ℝ → Tag) (t : Genealogy Copy)
    (d : Decoration t) :
    toTaggedTree t (mapBinDecoration bin t d) = mapTags bin (toAgeTree t d) := by
  induction t with
  | leaf x => rfl
  | graft a b ha hb =>
      change TaggedTree.graft (bin d.1)
        (toTaggedTree a (mapBinDecoration bin a d.2.1))
        (toTaggedTree b (mapBinDecoration bin b d.2.2)) =
        TaggedTree.graft (bin d.1) (mapTags bin (toAgeTree a d.2.1))
          (mapTags bin (toAgeTree b d.2.2))
      rw [ha,hb]

/-- Exactly recursive child swaps, retaining the graft's tag and leaf labels.
No associativity or contraction of equal-tag adjacent nodes is allowed. -/
inductive TaggedEquiv : TaggedTree Copy Tag → TaggedTree Copy Tag → Prop
  | refl (a) : TaggedEquiv a a
  | symm {a b} : TaggedEquiv a b → TaggedEquiv b a
  | trans {a b c} : TaggedEquiv a b → TaggedEquiv b c → TaggedEquiv a c
  | graft (v) {a b c d} : TaggedEquiv a c → TaggedEquiv b d →
      TaggedEquiv (.graft v a b) (.graft v c d)
  | swap (v a b) : TaggedEquiv (.graft v a b) (.graft v b a)

/-- Erasing tags transports only along the original unordered relation. -/
theorem taggedEquiv_underlying {a b : TaggedTree Copy Tag} (h : TaggedEquiv a b) :
    UnorderedEquiv (underlying a) (underlying b) := by
  induction h with
  | refl a => exact UnorderedEquiv.refl _
  | symm _ ih => exact UnorderedEquiv.symm ih
  | trans _ _ ih1 ih2 => exact UnorderedEquiv.trans ih1 ih2
  | graft v _ _ ih1 ih2 => exact UnorderedEquiv.graft ih1 ih2
  | swap v a b => exact UnorderedEquiv.swap _ _

/-- Binning commutes with every recursively generated decorated child swap. -/
theorem mapTags_respects {Other : Type*} (f : Tag → Other)
    {a b : TaggedTree Copy Tag} (h : TaggedEquiv a b) :
    TaggedEquiv (mapTags f a) (mapTags f b) := by
  induction h with
  | refl a => exact TaggedEquiv.refl _
  | symm _ ih => exact TaggedEquiv.symm ih
  | trans _ _ ih1 ih2 => exact TaggedEquiv.trans ih1 ih2
  | graft v _ _ ih1 ih2 => exact TaggedEquiv.graft (f v) ih1 ih2
  | swap v a b => exact TaggedEquiv.swap (f v) _ _

noncomputable def decodedTaggedTree (M : Copy → Copy → Tag) (t : Genealogy Copy) :
    TaggedTree Copy Tag := toTaggedTree t (decodeTags M t)

/-- One graft's swap uses only symmetry of its exact two chosen entries. -/
theorem decodedTaggedTree_graft_swap (M : Copy → Copy → Tag) (a b : Genealogy Copy)
    (hcross : M (witness a) (witness b) = M (witness b) (witness a)) :
    TaggedEquiv (decodedTaggedTree M (.graft a b))
      (decodedTaggedTree M (.graft b a)) := by
  change TaggedEquiv
    (.graft (M (witness a) (witness b)) (decodedTaggedTree M a) (decodedTaggedTree M b))
    (.graft (M (witness b) (witness a)) (decodedTaggedTree M b) (decodedTaggedTree M a))
  rw [hcross]
  exact TaggedEquiv.swap _ _ _

/-- Actual pair-age decoding yields the binned actual decorated tree. -/
theorem decodedTaggedTree_actual (bin : ℝ → Tag) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (ht : t.WellLabelled) (d : Decoration t) :
    decodedTaggedTree (fun x y => bin (pairAge leafAge t d x y)) t =
      mapTags bin (toAgeTree t d) := by
  unfold decodedTaggedTree
  rw [decodeTags_bin_pairAge bin leafAge t ht d,toTaggedTree_mapBinDecoration]

/-- Full unordered transport is for ACTUAL decorated representatives.
An arbitrary symmetric matrix alone is insufficient under nested swaps. -/
theorem actual_decoder_unordered (bin : ℝ → Tag) (leafAge : Copy → ℝ)
    (t u : Genealogy Copy) (ht : t.WellLabelled) (hu : u.WellLabelled)
    (d : Decoration t) (e : Decoration u)
    (h : TaggedEquiv (toAgeTree t d) (toAgeTree u e)) :
    TaggedEquiv
      (decodedTaggedTree (fun x y => bin (pairAge leafAge t d x y)) t)
      (decodedTaggedTree (fun x y => bin (pairAge leafAge u e x y)) u) := by
  rw [decodedTaggedTree_actual bin leafAge t ht d,
    decodedTaggedTree_actual bin leafAge u hu e]
  exact mapTags_respects bin h

#print axioms decodeTags_map_decode
#print axioms decodeTags_bin_pairAge
#print axioms decodeTags_bin_of_pair_agreement
#print axioms underlying_toTaggedTree
#print axioms underlying_mapTags
#print axioms toTaggedTree_mapBinDecoration
#print axioms taggedEquiv_underlying
#print axioms mapTags_respects
#print axioms decodedTaggedTree_graft_swap
#print axioms decodedTaggedTree_actual
#print axioms actual_decoder_unordered

end CloudG3.FiniteTagDecoder
