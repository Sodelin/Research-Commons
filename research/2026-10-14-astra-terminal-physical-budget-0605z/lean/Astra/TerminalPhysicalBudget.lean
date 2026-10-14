import Astra.ActualCellSupportBudget
import Astra.ProtectedBlobIncidence
import Astra.BridgeCutClassBudget
import Astra.TwoPortExceptionCount
import Mathlib.Data.Fintype.EquivFin

/-! Source-only terminal physical budget. The fixed-mask grid cover is an
intermediate interface, to be derived from supplied mixed certificates by a
separate composition. No desired representative or hybrid bound is a premise.
The accepted h specialization has no free marked vertex domain. -/
namespace Astra.TerminalPhysicalBudget

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.OriginalFixedIDControls
open G1CutChildPorts G1ReducedCoreCounts
open DotG4.WeightedOrdinaryTreeLaw DotG4.WholeProfileDetermination
open Astra.PhysicalCommonStep Astra.ProtectedPhysicalIteration
open Astra.ProtectedBlobIncidence Astra.ActualCellSupportBudget
open Astra.PhysicalSpliceExternalMasks Astra.BridgeCutClassBudget
open Astra.TwoPortExceptionCount
open scoped Classical BigOperators

universe u v w a b c
variable {X : Type w} [Fintype X] [DecidableEq X]
variable {PV : Type a} {PE : Type b} {PH : Type c}
variable [Fintype PV] [Fintype PE] [Fintype PH]

noncomputable instance cellFintype (S : PhysicalSource.{u,v,w} X) : Fintype (Cell S) := by
  unfold Cell
  infer_instance

noncomputable def unblockedCells (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    Finset (Cell S.physical) :=
  Finset.univ.filter (fun c => c.val ∉ blockerBlobs S)

lemma unblocked_unequal (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (hr : Reduced S) (c : Cell S.physical) (hc : c ∈ unblockedCells S) :
    ¬ EqualArmExposure S.physical c.val c.property.1 c.property.2 := by
  intro heq
  have hn := (Finset.mem_filter.mp hc).2
  obtain ⟨hv, he, hh⟩ := local_avoidance_of_not_mem S c.val c.property.1 c.property.2 hn
  exact hr ⟨⟨c.val, c.property.1, c.property.2, heq, hv, he, hh⟩⟩

lemma unblocked_unforced (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (table : PH → Option Bool) (c : Cell S.physical) (hc : c ∈ unblockedCells S) :
    labelMask S.hybrids table (cellHybrid S.physical c) = none := by
  have hn := (Finset.mem_filter.mp hc).2
  apply labelMask_off_labels
  rintro ⟨z, hz⟩
  exact hybrid_avoid_of_not_mem S c.val (cellBigon S.physical c) hn z hz

/-- Count one actual cut fibre by enumerating its actual finite cells. The
same original mask is natural at every counted site by incidence avoidance. -/
theorem unblocked_cut_fibre_bound (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (hr : Reduced S) (table : PH → Option Bool)
    (grids : X × X → Finset ℝ) (cap : Nat)
    (grid_card : ∀ ij, (grids ij).card ≤ cap)
    (cover : ∀ coin i j,
      directedSurvival (maskedNormalizedTree S.physical.source.network
        S.physical.source.calendar S.physical.registry S.physical.rates
        (labelMask S.hybrids table) coin) i j ∈ grids (i,j)) (D : Finset X) :
    ((unblockedCells S).filter (fun c => cellCut S.physical c = D)).card ≤ cap - 1 := by
  let F := (unblockedCells S).filter (fun c => cellCut S.physical c = D)
  by_cases hf : F.Nonempty
  · obtain ⟨anchor, ha⟩ := hf
    let e : Fin F.card ≃ F := F.equivFin.symm
    let cells : Fin F.card → Cell S.physical := fun k => (e k).val
    have hinj : Function.Injective cells := by
      intro k l h
      exact e.injective (Subtype.ext h)
    have hmem (k : Fin F.card) : cells k ∈ unblockedCells S :=
      (Finset.mem_filter.mp (e k).property).1
    have hsame (k : Fin F.card) : cellCut S.physical (cells k) = cellCut S.physical anchor :=
      (Finset.mem_filter.mp (e k).property).2.trans (Finset.mem_filter.mp ha).2.symm
    obtain ⟨i, j, hi, hj, _⟩ := Astra.BridgeTaxonCuts.bridgeTaxa_separating_pair
      S.physical.source.network
      ⟨(cellBigon S.physical anchor).child, (cellBigon S.physical anchor).child_bridge⟩
    have hb := same_cut_masked_cover_bound S.physical anchor cells hinj hsame
      (fun k => unblocked_unequal S hr (cells k) (hmem k))
      (labelMask S.hybrids table)
      (fun k => unblocked_unforced S table (cells k) (hmem k))
      i j hi hj (grids (i,j)) (fun coin => cover coin i j)
    have hg := grid_card (i,j)
    change F.card ≤ cap - 1
    omega
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    change F.card ≤ cap - 1
    simp only [he, Finset.card_empty, Nat.zero_le]

/-- The actual child bridges put every counted cut in the previously proved
set of distinct original bridge cuts. No quotient chain is supplied. -/
lemma unblocked_cut_image_subset (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    (unblockedCells S).image (cellCut S.physical) ⊆
      bridgeCutClasses S.physical.source.network := by
  intro D hD
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hD
  exact Finset.mem_image.mpr
    ⟨⟨(cellBigon S.physical c).child, (cellBigon S.physical c).child_bridge⟩,
      Finset.mem_univ _, rfl⟩

theorem all_unblocked_cells_bound (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (hr : Reduced S) (table : PH → Option Bool)
    (grids : X × X → Finset ℝ) (cap : Nat)
    (grid_card : ∀ ij, (grids ij).card ≤ cap)
    (cover : ∀ coin i j,
      directedSurvival (maskedNormalizedTree S.physical.source.network
        S.physical.source.calendar S.physical.registry S.physical.rates
        (labelMask S.hybrids table) coin) i j ∈ grids (i,j)) :
    (unblockedCells S).card ≤ (2 * Fintype.card X - 2) * (cap - 1) := by
  let cuts := (unblockedCells S).image (cellCut S.physical)
  have hc : (unblockedCells S).card ≤ cuts.card * (cap - 1) := by
    rw [Finset.card_eq_sum_card_image (cellCut S.physical)]
    calc
      _ ≤ ∑ _D ∈ cuts, cap - 1 := Finset.sum_le_sum
        (fun D _ => unblocked_cut_fibre_bound S hr table grids cap grid_card cover D)
      _ = _ := by simp only [Finset.sum_const, smul_eq_mul]
  have hs := Finset.card_le_card (unblocked_cut_image_subset S)
  have hb := actual_bridge_cut_class_budget S.physical.source.network S.physical.source.calendar
    (GProgram.G5.AttainedChronology.commonSwitching S.physical.source.network
      S.physical.registry (fun _ => false))
  have hcuts : cuts.card ≤ 2 * Fintype.card X - 2 := by omega
  exact hc.trans (Nat.mul_le_mul_right (cap - 1) hcuts)

/-- Every actual nonroot two-port exception is either incident with a marked
primitive or the image of an unblocked actual cell. -/
theorem two_port_cells_partition_bound (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    (twoPortBlobs S.physical.source.network).card ≤
      (blockerBlobs S).card + (unblockedCells S).card := by
  have hs : twoPortBlobs S.physical.source.network ⊆
      blockerBlobs S ∪ (unblockedCells S).image (fun c => c.val) := by
    intro b hb
    have hp := (Finset.mem_filter.mp hb).2
    have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.1
    by_cases hm : b ∈ blockerBlobs S
    · exact Finset.mem_union_left _ hm
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⟨b, hn, hp⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
  exact (Finset.card_le_card hs).trans
    (Finset.card_union_le.trans (Nat.add_le_add_left Finset.card_image_le _))

/-- Faithful numerical h specialization: no extra PV labels, and the caller
fixes PE/PH and their budget before any possible realizer. Their semantic
expanded-dependency adequacy is the original input contract, not proved by
an ID count. The actual reduced source's hybrid bound is a conclusion. -/
theorem reduced_physical_hybrid_bound [IsEmpty PV]
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (hr : Reduced S)
    (h : Nat) (hlabels : Fintype.card PE + Fintype.card PH ≤ h)
    (table : PH → Option Bool) (grids : X × X → Finset ℝ) (cap : Nat)
    (grid_card : ∀ ij, (grids ij).card ≤ cap)
    (cover : ∀ coin i j,
      directedSurvival (maskedNormalizedTree S.physical.source.network
        S.physical.source.calendar S.physical.registry S.physical.rates
        (labelMask S.hybrids table) coin) i j ∈ grids (i,j)) :
    Fintype.card (Hybrid S.physical.source.network) ≤
      (2 * Fintype.card X - 2 + 2*h) +
        (8 * Fintype.card X - 8 + 6*h) * (cap - 1) := by
  have hu := all_unblocked_cells_bound S hr table grids cap grid_card cover
  have ht := two_port_cells_partition_bound S
  have hm := blockerBlobs_card_le S
  simp only [Fintype.card_of_isEmpty, zero_add] at hm
  have hmarked : (blockerBlobs S).card ≤ 2*h := by omega
  have hh := actual_hybrid_exception_budget S.physical.source.network S.physical.source.cutChild
  have hcard : Fintype.card (Hybrid S.physical.source.network) =
      (hybrids S.physical.source.network).card := by
    simp only [Hybrid, hybrids, Fintype.card_subtype]
  rw [← hcard] at hh
  have hn := S.physical.source.network.at_least_two_taxa
  have hsmall : Fintype.card (Hybrid S.physical.source.network) ≤
      (2 * Fintype.card X - 2 + 2*h) + (2 * Fintype.card X - 2) * (cap - 1) := by omega
  have hcoef : 2 * Fintype.card X - 2 ≤ 8 * Fintype.card X - 8 + 6*h := by omega
  exact hsmall.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (cap - 1) hcoef) _)

#print axioms unblocked_unequal
#print axioms unblocked_unforced
#print axioms unblocked_cut_fibre_bound
#print axioms all_unblocked_cells_bound
#print axioms two_port_cells_partition_bound
#print axioms reduced_physical_hybrid_bound

end Astra.TerminalPhysicalBudget
