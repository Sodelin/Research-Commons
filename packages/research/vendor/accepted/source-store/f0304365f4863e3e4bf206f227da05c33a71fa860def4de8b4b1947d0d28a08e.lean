import G5SourcePairPersistence
import G5EnumeratedTripleRow

namespace GProgram.G5.TwoCutPartitionDecoder
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.G6.BinHistory
open GProgram.G5.SourcePairPersistence GProgram.G5.TriplePartitionReadout
open GProgram.G5.EnumeratedTripleRow
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def binPartition (i : Fin 3 → Copy) (cut : Fin 3)
    (B : Copy → Copy → Fin 3) : Fin 5 :=
  if B (i 0) (i 1) ≤ cut then (if B (i 0) (i 2) ≤ cut then 4 else 1)
  else if B (i 0) (i 2) ≤ cut then 2
  else if B (i 1) (i 2) ≤ cut then 3 else 0

/-- The two finite-bin partitions recover the actual two cut partitions
on a monotone completed source branch. Old pair-book entries cannot affect
an off-diagonal pair's first-birth bin. -/
theorem three_phase_partition_decoder (N : RootedBinary V E X) {sample : Copy → X}
    (s d e g : Code N sample) (B : Copy → Copy → Fin 3)
    (i : Fin 3 → Copy) (hi : Function.Injective i)
    (hs : Function.Injective (state s).ancestor) (hde : RelationMonotone N d e)
    (hg : ∀ x y, (state g).ancestor x = (state g).ancestor y) :
    let book := tagUpdate N e g (2 : Fin 3)
      (tagUpdate N d e (1 : Fin 3) (tagUpdate N s d (0 : Fin 3) B))
    (binPartition i 0 book, binPartition i 1 book) =
      (ancestorPartition ((state d).ancestor ∘ i),ancestorPartition ((state e).ancestor ∘ i)) := by
  let book := tagUpdate N e g (2 : Fin 3)
    (tagUpdate N d e (1 : Fin 3) (tagUpdate N s d (0 : Fin 3) B))
  have hp (x y : Fin 3) (hxy : x ≠ y) :
      book (i x) (i y) = if (state d).ancestor (i x) = (state d).ancestor (i y) then 0
        else if (state e).ancestor (i x) = (state e).ancestor (i y) then 1 else 2 :=
    three_phase_pair_tag N s d e g B (i x) (i y) (hs.ne (hi.ne hxy)) hde (hg _ _)
  have h0 (x y : Fin 3) (hxy : x ≠ y) :
      book (i x) (i y) ≤ 0 ↔ (state d).ancestor (i x) = (state d).ancestor (i y) := by
    rw [hp x y hxy]
    by_cases hd : (state d).ancestor (i x) = (state d).ancestor (i y) <;>
      by_cases he : (state e).ancestor (i x) = (state e).ancestor (i y) <;> simp [hd,he]
  have h1 (x y : Fin 3) (hxy : x ≠ y) :
      book (i x) (i y) ≤ 1 ↔ (state e).ancestor (i x) = (state e).ancestor (i y) := by
    rw [hp x y hxy]
    have hh := hde (i x) (i y)
    by_cases hd : (state d).ancestor (i x) = (state d).ancestor (i y) <;>
      by_cases he : (state e).ancestor (i x) = (state e).ancestor (i y) <;> simp_all
  change (binPartition i 0 book,binPartition i 1 book) = _
  simp only [binPartition,ancestorPartition,Function.comp_apply,
    h0 0 1 (by decide),h0 0 2 (by decide),h0 1 2 (by decide),
    h1 0 1 (by decide),h1 0 2 (by decide),h1 1 2 (by decide)]

#print axioms three_phase_partition_decoder
end GProgram.G5.TwoCutPartitionDecoder
