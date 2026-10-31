import ResearchCommons.MSCI.JC69CurrentPartition
import UnifiedLean.Source.SourceMergerClockCatalogue

/-! Independent deterministic source adapter. UNCOMPILED, 31 October 2026.
Contributor: dot (OpenAI). Depends only on accepted occupation-v1 partition
and pinned actual source providers, not the four pending renewal joins.
No quotient Markov law, boundary/register admission, or likelihood expansion
is assumed or concluded. All original labelled copies are retained. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69SourceRootQuotient
open Nanuq.Source GProgram.SourceForest GProgram.G2.FaithfulPairAgeDecoration
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.SourceForestKingmanPopulationProjection
open ResearchCommons.MSCI.JC69CurrentPartition
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev LiveRoot (s : State V E Copy) := {a : Copy // a ∈ s.live}

lemma matching_root_exists (s t : State V E Copy)
    (hB : currentBlocks s = currentBlocks t) (a : LiveRoot s) :
    ∃ b : Copy, b ∈ t.live ∧ (t.genealogy b).leaves = (s.genealogy a.val).leaves := by
  have ha : (s.genealogy a.val).leaves ∈ currentBlocks s :=
    Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩
  rw [hB] at ha
  exact Finset.mem_image.mp ha

/-- The matching representative is selected from the actual destination
state, not an arbitrary new representative or synthetic source state. -/
def matchingRoot (s t : State V E Copy)
    (hB : currentBlocks s = currentBlocks t) (a : LiveRoot s) : LiveRoot t :=
  ⟨Classical.choose (matching_root_exists s t hB a),
    (Classical.choose_spec (matching_root_exists s t hB a)).1⟩

lemma matchingRoot_block (s t : State V E Copy)
    (hB : currentBlocks s = currentBlocks t) (a : LiveRoot s) :
    (t.genealogy (matchingRoot s t hB a).val).leaves = (s.genealogy a.val).leaves :=
  (Classical.choose_spec (matching_root_exists s t hB a)).2

lemma matchingRoot_bijective (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (hB : currentBlocks s = currentBlocks t) : Function.Bijective (matchingRoot s t hB) := by
  constructor
  · intro a b he
    apply Subtype.ext
    apply live_leaves_injective s hs a.property b.property
    calc
      (s.genealogy a.val).leaves = (t.genealogy (matchingRoot s t hB a).val).leaves :=
        (matchingRoot_block s t hB a).symm
      _ = (t.genealogy (matchingRoot s t hB b).val).leaves := by rw [he]
      _ = (s.genealogy b.val).leaves := matchingRoot_block s t hB b
  · intro b
    let a := matchingRoot t s hB.symm b
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply live_leaves_injective t ht (matchingRoot s t hB a).property b.property
    exact (matchingRoot_block s t hB a).trans (matchingRoot_block t s hB.symm b)

/-- Actual live representatives may differ, but their complete labelled
blocks give a genuine bijection, not an assumed quotient sufficient statistic. -/
def liveRootEquiv (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (hB : currentBlocks s = currentBlocks t) : LiveRoot s ≃ LiveRoot t :=
  Equiv.ofBijective (matchingRoot s t hB) (matchingRoot_bijective s t hs ht hB)

lemma location_eq_of_same_block (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (hLoc : ∀ x, copyLocation s x = copyLocation t x)
    (a : LiveRoot s) (b : LiveRoot t)
    (hB : (s.genealogy a.val).leaves = (t.genealogy b.val).leaves) :
    s.location a.val = t.location b.val := by
  let x := witness (s.genealogy a.val)
  have hx : x ∈ (s.genealogy a.val).leaves := witness_mem _
  have hy : x ∈ (t.genealogy b.val).leaves := by rw [← hB]; exact hx
  have hxa := (hs.leaf_fiber a.val a.property x).mp hx
  have hxb := (ht.leaf_fiber b.val b.property x).mp hy
  calc
    s.location a.val = copyLocation s x := by simp only [copyLocation,hxa]
    _ = copyLocation t x := hLoc x
    _ = t.location b.val := by simp only [copyLocation,hxb]

lemma matchingRoot_location (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (hB : currentBlocks s = currentBlocks t)
    (hLoc : ∀ x, copyLocation s x = copyLocation t x) (a : LiveRoot s) :
    t.location (matchingRoot s t hB a).val = s.location a.val :=
  (location_eq_of_same_block s t hs ht hLoc a (matchingRoot s t hB a)
    (matchingRoot_block s t hB a).symm).symm

/-- A reformulation of the original ordered pair catalogue, retaining its
actual population and both orientations. -/
abbrev LivePopulationPair (s : State V E Copy) (place : Location V E) :=
  {p : LiveRoot s × LiveRoot s //
    s.location p.1.val = place ∧ s.location p.2.val = place ∧ p.1 ≠ p.2}

def rawPopulationPairEquiv (s : State V E Copy) (place : Location V E) :
    {p : Copy × Copy // p ∈ (populationRoots s place).offDiag} ≃
      LivePopulationPair s place where
  toFun p := by
    obtain ⟨ha,hb,hne⟩ := Finset.mem_offDiag.mp p.property
    obtain ⟨hal,haloc⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbl,hbloc⟩ := Finset.mem_filter.mp hb
    exact ⟨(⟨p.val.1,hal⟩,⟨p.val.2,hbl⟩),haloc,hbloc,
      fun he => hne (congrArg Subtype.val he)⟩
  invFun p := ⟨(p.val.1.val,p.val.2.val),Finset.mem_offDiag.mpr
    ⟨Finset.mem_filter.mpr ⟨p.val.1.property,p.property.1⟩,
      Finset.mem_filter.mpr ⟨p.val.2.property,p.property.2.1⟩,
      fun he => p.property.2.2 (Subtype.ext he)⟩⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

def livePopulationPairEquiv (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (hB : currentBlocks s = currentBlocks t)
    (hLoc : ∀ x, copyLocation s x = copyLocation t x) (place : Location V E) :
    LivePopulationPair s place ≃ LivePopulationPair t place := by
  let e := liveRootEquiv s t hs ht hB
  apply (e.prodCongr e).subtypeEquiv
  intro p
  have h1 := matchingRoot_location s t hs ht hB hLoc p.1
  have h2 := matchingRoot_location s t hs ht hB hLoc p.2
  change (s.location p.1.val = place ∧ s.location p.2.val = place ∧ p.1 ≠ p.2) ↔
    (t.location (e p.1).val = place ∧ t.location (e p.2).val = place ∧ e p.1 ≠ e p.2)
  change t.location (e p.1).val = s.location p.1.val at h1
  change t.location (e p.2).val = s.location p.2.val at h2
  rw [h1,h2]
  simp only [e.injective.eq_iff]

/-- Genuine equivalence of the ACTUAL original Choice types. It preserves
the original Option E population index, rather than inventing a P-code. -/
def actualChoiceEquiv (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) :
    Choice N s ≃ Choice N t :=
  Equiv.sigmaCongrRight (fun i =>
    (rawPopulationPairEquiv (state s) (originalPlace N i)).trans
      ((livePopulationPairEquiv (state s) (state t) s.property.forest t.property.forest
        hB hLoc (originalPlace N i)).trans
          (rawPopulationPairEquiv (state t) (originalPlace N i)).symm))

lemma actualChoiceEquiv_population (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x)
    (p : Choice N s) : (actualChoiceEquiv N s t hB hLoc p).1 = p.1 := rfl

lemma actualChoiceEquiv_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x)
    (p : Choice N s) :
    choiceRate N r t (actualChoiceEquiv N s t hB hLoc p) = choiceRate N r s p := rfl

lemma actual_totalRate_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) :
    totalRate N r t = totalRate N r s := by
  unfold totalRate
  rw [← (actualChoiceEquiv N s t hB hLoc).sum_comp (fun p => choiceRate N r t p)]
  apply Finset.sum_congr rfl
  intro p _
  exact actualChoiceEquiv_rate N r s t hB hLoc p

/-- Re-encoding an actual valid source preserves precisely its live descendant
blocks. The original decode/encode theorem already preserves each live tree. -/
lemma decode_encode_blocks (root : V) (s : State V E Copy) (hs : Valid s) :
    currentBlocks (decodeSnapshot root (encodeSnapshot s hs)) = currentBlocks s := by
  unfold currentBlocks
  apply Finset.image_congr
  intro a ha
  rw [decode_encode_live_genealogy root s hs ha]

lemma actual_coded_merge_blocks (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    currentBlocks (state (stepDestination N s (some p))) =
      currentBlocks (merge (state s) p.2.val.1 p.2.val.2) := by
  unfold state stepDestination admittedCode
  exact decode_encode_blocks _ _ _

lemma actual_coded_merge_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (x : Copy) :
    copyLocation (state (stepDestination N s (some p))) x = copyLocation (state s) x := by
  unfold state stepDestination admittedCode
  rw [decode_encode_copyLocation]
  exact merge_population_preserved _
    (population_pair_is_source_legal _ (originalPlace N p.1)
      (originalPlace_not_node N p.1) p.2.property) x

#print axioms actual_totalRate_eq
#print axioms actualChoiceEquiv_population
#print axioms actualChoiceEquiv_rate
#print axioms matching_root_exists
#print axioms matchingRoot_bijective
#print axioms location_eq_of_same_block
#print axioms matchingRoot_location
#print axioms decode_encode_blocks
#print axioms actual_coded_merge_blocks
#print axioms actual_coded_merge_copyLocation
end ResearchCommons.MSCI.JC69SourceRootQuotient
