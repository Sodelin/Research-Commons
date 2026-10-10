import UnifiedLean.Source.SourceNaturalCompletedLimit

/-!
# Canonical original-copy restriction carrier and source initialization

Contributor: dot, 2026-10-02. Begins the independently initialized smaller-copy
source comparison using the ACTUAL subtype of selected original IDs, the SAME
original graph/sample map/registry/parameters, and faithful genealogy label
transport. It does not replace that source by the earlier same-copy view range.
-/
namespace UnifiedLean.Source.SourceCopyCarrierTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCompletedUnrankedTree
open scoped Classical BigOperators
variable {A B : Type*}

/-- Labels change only by the supplied original-copy injection; original
binary genealogy shape and child order are preserved exactly. -/
def mapLabels (f : A → B) : Genealogy A → Genealogy B
  | .leaf x => .leaf (f x)
  | .graft a b => .graft (mapLabels f a) (mapLabels f b)

lemma mapLabels_leaves [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
    (f : A → B) (t : Genealogy A) : (mapLabels f t).leaves = t.leaves.image f := by
  induction t with
  | leaf x => simp [mapLabels,Genealogy.leaves]
  | graft a b iha ihb => simp [mapLabels,Genealogy.leaves,iha,ihb,Finset.image_union]

lemma mapLabels_injective (f : A → B) (hf : Function.Injective f) :
    Function.Injective (mapLabels f) := by
  intro a
  induction a with
  | leaf x =>
      intro b h
      cases b with
      | leaf y => exact congrArg Genealogy.leaf (hf (Genealogy.leaf.inj h))
      | graft b c => cases h
  | graft a b iha ihb =>
      intro c h
      cases c with
      | leaf x => cases h
      | graft c d =>
          have hh := Genealogy.graft.inj h
          exact congrArg₂ Genealogy.graft (iha hh.1) (ihb hh.2)

lemma mapLabels_wellLabelled [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (t : Genealogy A) (ht : t.WellLabelled) :
    (mapLabels f t).WellLabelled := by
  induction t with
  | leaf x => trivial
  | graft a b iha ihb =>
      refine ⟨iha ht.1,ihb ht.2.1,?_⟩
      rw [mapLabels_leaves,mapLabels_leaves]
      apply Finset.disjoint_left.mpr
      intro z hza hzb
      obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hza
      obtain ⟨y,hy,hyz⟩ := Finset.mem_image.mp hzb
      have hxy := hf (hxz.trans hyz.symm)
      exact Finset.disjoint_left.mp ht.2.2 hx (hxy ▸ hy)

lemma mapLabels_joinPruned (f : A → B) (a b : Option (Genealogy A)) :
    (Genealogy.joinPruned a b).map (mapLabels f) =
      Genealogy.joinPruned (a.map (mapLabels f)) (b.map (mapLabels f)) := by
  cases a <;> cases b <;> rfl

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev SelectedCopy (keep : Finset Copy) := { x : Copy // x ∈ keep }

/-- Actual independently initialized source sample assignment retains the
original taxon of EACH selected ORIGINAL copy, including repeated taxa. -/
def selectedSample (sample : Copy → X) (keep : Finset Copy) : SelectedCopy keep → X :=
  fun x => sample x.val

noncomputable def liftView (keep : Finset Copy) (v : SelectedView V E (SelectedCopy keep)) :
    SelectedView V E Copy where
  genealogy x := if hx : x ∈ keep then (v.genealogy ⟨x,hx⟩).map (mapLabels Subtype.val) else none
  population x := if hx : x ∈ keep then v.population ⟨x,hx⟩ else none
  register := v.register

lemma liftView_genealogy (keep : Finset Copy) (v : SelectedView V E (SelectedCopy keep))
    (x : SelectedCopy keep) : (liftView keep v).genealogy x.val =
      (v.genealogy x).map (mapLabels Subtype.val) := by
  simp only [liftView,dif_pos x.property]

lemma liftView_population (keep : Finset Copy) (v : SelectedView V E (SelectedCopy keep))
    (x : SelectedCopy keep) : (liftView keep v).population x.val = v.population x := by
  simp only [liftView,dif_pos x.property]

lemma lifted_original_genealogy (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (x : SelectedCopy keep) :
    (liftView keep (selectedView s Finset.univ)).genealogy x.val =
      some (mapLabels Subtype.val (s.genealogy (s.ancestor x))) := by
  rw [liftView_genealogy]
  simp only [selectedView,selectedGenealogy,Finset.mem_univ,if_true,full_prune,Option.map_some]

lemma lifted_original_population (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (x : SelectedCopy keep) :
    (liftView keep (selectedView s Finset.univ)).population x.val = some (copyLocation s x) := by
  rw [liftView_population]
  simp only [selectedView,selectedLocation,Finset.mem_univ,if_true]

/-- Actual independent small-carrier tip initialization agrees with pruning
the full original initialization, after only the original-ID subtype lift.
This diagram is proved from the actual source constructors, not a contract. -/
theorem actual_initial_copy_carrier_diagram (N : RootedBinary V E X) (sample : Copy → X)
    (keep : Finset Copy) (register : V → Bool) :
    liftView keep (selectedView (state (initialCode N (selectedSample sample keep) register)) Finset.univ) =
      selectedView (state (initialCode N sample register)) keep := by
  have hfull := decode_encode_selectedView N.root (initial N sample register)
    (initial_valid N sample register) keep
  have hsmall := decode_encode_selectedView N.root (initial N (selectedSample sample keep) register)
    (initial_valid N (selectedSample sample keep) register) Finset.univ
  change liftView keep (selectedView (decodeSnapshot N.root
      (encodeSnapshot (initial N (selectedSample sample keep) register)
        (initial_valid N (selectedSample sample keep) register))) Finset.univ) =
    selectedView (decodeSnapshot N.root (encodeSnapshot (initial N sample register) (initial_valid N sample register))) keep
  rw [hfull,hsmall]
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · simp [liftView,selectedView,selectedGenealogy,initial,Genealogy.prune,mapLabels,hx]
    · simp [liftView,selectedView,selectedGenealogy,hx]
  · funext x
    by_cases hx : x ∈ keep
    · simp [liftView,selectedView,selectedLocation,initial,copyLocation,selectedSample,hx]
    · simp [liftView,selectedView,selectedLocation,hx]
  · rfl

#print axioms mapLabels_wellLabelled
#print axioms actual_initial_copy_carrier_diagram
end UnifiedLean.Source.SourceCopyCarrierTransport
