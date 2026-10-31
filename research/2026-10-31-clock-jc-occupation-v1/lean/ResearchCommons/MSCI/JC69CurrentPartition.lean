import ResearchCommons.MSCI.KilledClocks
import G2FaithfulPairAgeDecoration
import Mathlib.Order.Partition.Finpartition

/-! Actual current descendant partition and the exact Bell-count state envelope.
Contributor: dot (OpenAI), 30 October 2026. UNCOMPILED.
BellCount is definitionally the number of set partitions, not a larger bound.
This does NOT yet prove killed-generator/routing lumpability or register admission.
-/
noncomputable section
namespace ResearchCommons.MSCI.JC69CurrentPartition
open GProgram.SourceForest GProgram.G2.FaithfulPairAgeDecoration
open scoped Classical BigOperators
variable {Copy V E : Type*} [Fintype Copy] [DecidableEq Copy]

def currentBlocks (s : State V E Copy) : Finset (Finset Copy) :=
  s.live.image (fun l => (s.genealogy l).leaves)

lemma live_leaves_injective (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (ha : a ∈ s.live) (hb : b ∈ s.live)
    (he : (s.genealogy a).leaves = (s.genealogy b).leaves) : a = b := by
  let x := witness (s.genealogy a)
  have hx : x ∈ (s.genealogy a).leaves := witness_mem _
  have hy : x ∈ (s.genealogy b).leaves := by rw [← he]; exact hx
  exact ((hs.leaf_fiber a ha x).mp hx).symm.trans ((hs.leaf_fiber b hb x).mp hy)

lemma unique_current_block (s : State V E Copy) (hs : Valid s) (x : Copy) :
    ∃! B ∈ currentBlocks s, x ∈ B := by
  refine ⟨(s.genealogy (s.ancestor x)).leaves,⟨?_,?_⟩,?_⟩
  · exact Finset.mem_image.mpr ⟨s.ancestor x,hs.ancestor_live x,rfl⟩
  · exact (hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl
  · intro B hB
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hB.1
    have he : s.ancestor x = l := (hs.leaf_fiber l hl x).mp hB.2
    rw [he]

lemma empty_not_current_block (s : State V E Copy) : ∅ ∉ currentBlocks s := by
  intro h
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp h
  have hm := witness_mem (s.genealogy l)
  rw [he] at hm
  exact Finset.notMem_empty _ hm

/-- Actual original descendant blocks, forgetting genealogy shape, survivor
IDs, population history and registers, but not a single sampled label. -/
def currentPartition (s : State V E Copy) (hs : Valid s) :
    Finpartition (Finset.univ : Finset Copy) :=
  Finpartition.ofExistsUnique (currentBlocks s)
    (fun _ _ => Finset.subset_univ _) (fun x _ => unique_current_block s hs x)
    (empty_not_current_block s)

/-- The actual current-block charge count depends only on this partition.
All finite site families retain their exact original label assignments. -/
theorem active_charge_factors_through_partition {Site G : Type*} [Fintype Site]
    [AddCommMonoid G] [DecidableEq G] (s : State V E Copy) (hs : Valid s)
    (q : Copy → Site → G) :
    activeChargeCount s q =
      ∑ B ∈ (currentPartition s hs).parts,
        ∑ j : Site, nonzeroCharge (∑ x ∈ B, q x j) := by
  change activeChargeCount s q = ∑ B ∈ currentBlocks s, _
  rw [currentBlocks,Finset.sum_image]
  · rfl
  · intro a ha b hb he
    exact live_leaves_injective s hs ha hb he

/-- A genuine source merger replaces precisely its two current descendant
blocks by their union. Genealogy ordering and the surviving representative
are forgotten only after this identity has been proved. -/
theorem actual_merge_blocks (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) :
    currentBlocks (merge s a b) =
      insert ((s.genealogy a).leaves ∪ (s.genealogy b).leaves)
        (((currentBlocks s).erase (s.genealogy a).leaves).erase (s.genealogy b).leaves) := by
  classical
  ext B
  constructor
  · intro h
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
    have hl' : l ≠ b ∧ l ∈ s.live := Finset.mem_erase.mp hl
    by_cases hla : l = a
    · subst l
      simp [merge,Genealogy.leaves]
    · simp only [merge,if_neg hla]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_erase.mpr ⟨?_,?_⟩⟩
      · intro he
        exact hl'.1 (live_leaves_injective s hs hl'.2 hm.second_live he)
      · intro he
        exact hla (live_leaves_injective s hs hl'.2 hm.first_live he)
      · exact Finset.mem_image.mpr ⟨l,hl'.2,rfl⟩
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · subst B
      refine Finset.mem_image.mpr ⟨a,?_,?_⟩
      · exact Finset.mem_erase.mpr ⟨hm.different,hm.first_live⟩
      · simp [merge,Genealogy.leaves]
    · obtain ⟨hneB,h⟩ := Finset.mem_erase.mp h
      obtain ⟨hneA,h⟩ := Finset.mem_erase.mp h
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
      have hla : l ≠ a := by intro h; subst l; exact hneA rfl
      have hlb : l ≠ b := by intro h; subst l; exact hneB rfl
      refine Finset.mem_image.mpr ⟨l,Finset.mem_erase.mpr ⟨hlb,hl⟩,?_⟩
      simp [merge,hla]

lemma legal_merge_reverse (s : State V E Copy) {a b : Copy}
    (hm : LegalMerge s a b) : LegalMerge s b a :=
  ⟨hm.second_live,hm.first_live,hm.different.symm,hm.same_population.symm,
    fun v h => hm.population_not_node v (hm.same_population.trans h)⟩

/-- The two ordered Kingman choices have the same exact partition endpoint.
This is required before aggregating their half-rates; it does not assert
that their raw history, survivor ID or ordered genealogy are equal. -/
theorem actual_merge_orientation_blocks (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) :
    currentBlocks (merge s a b) = currentBlocks (merge s b a) := by
  rw [actual_merge_blocks s hs hm,actual_merge_blocks s hs (legal_merge_reverse s hm)]
  exact congrArg₂ (fun (block : Finset Copy) (blocks : Finset (Finset Copy)) => insert block blocks)
    (Finset.union_comm _ _) (by
      ext block
      simp only [Finset.mem_erase]
      tauto)

/-- Both orientations also retain every original copy's actual population. -/
theorem actual_merge_orientation_locations (s : State V E Copy)
    {a b : Copy} (hm : LegalMerge s a b) (x : Copy) :
    copyLocation (merge s a b) x = copyLocation (merge s b a) x := by
  have preserve : ∀ {u v : Copy}, LegalMerge s u v →
      copyLocation (merge s u v) x = copyLocation s x := by
    intro u v legal
    by_cases h : s.ancestor x = v
    · simp only [copyLocation, merge, if_pos h]
      simpa only [h] using legal.same_population
    · simp only [copyLocation, merge, if_neg h]
  exact (preserve hm).trans (preserve (legal_merge_reverse s hm)).symm

theorem actual_transport_blocks (s : State V E Copy)
    (location : Copy → Location V E) (event : SourceEvent V E Copy) :
    currentBlocks (transport s location event) = currentBlocks s := rfl

/-- The Bell number by its defining combinatorial meaning. Equality with the
separate Mathlib Nat.bell sequence is a future interoperability lemma, not
an assumption or an alteration of the manuscript's number of partitions. -/
def BellCount (n : ℕ) : ℕ :=
  Fintype.card (Finpartition (Finset.univ : Finset (Fin n)))

/-- An overcount: a set partition plus a population color per original copy.
Valid current states are constant-colored on each block. We need not enlarge
the bound by retaining old genealogy trees, survivor choices or registers. -/
abbrev StateEnvelope (n P : ℕ) :=
  Finpartition (Finset.univ : Finset (Fin n)) × (Fin n → Fin P)

theorem state_envelope_card (n P : ℕ) :
    Fintype.card (StateEnvelope n P) = BellCount n * P^n := by
  simp [StateEnvelope,BellCount]

/-- Exact receiver for a source's current labelled panel and supplied
population indexing. No claim yet that every compiler step factors through
it: population/rate-bank coherence and routing admission are separate. -/
def sourceEnvelope {n P : ℕ} (s : State V E (Fin n)) (hs : Valid s)
    (populationIndex : Location V E → Fin P) : StateEnvelope n P :=
  (currentPartition s hs,fun x => populationIndex (s.location (s.ancestor x)))

#print axioms active_charge_factors_through_partition
#print axioms actual_merge_blocks
#print axioms actual_merge_orientation_blocks
#print axioms actual_merge_orientation_locations
#print axioms state_envelope_card
end ResearchCommons.MSCI.JC69CurrentPartition
