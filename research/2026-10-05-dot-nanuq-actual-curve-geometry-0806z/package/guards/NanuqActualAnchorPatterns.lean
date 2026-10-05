import guards.NanuqActualPortPairQuartet

set_option debug.skipKernelTC false

/-! Actual-source anchor entries on projected four-tuples. These equality-
pattern calculations retain the source's repeated-label masks. -/
namespace Nanuq.PortPatterns
open scoped Classical
variable {P : Type*} [DecidableEq P]

def tupleAnchor (f : Fin 4 → P) (rho : ℚ) : ℚ :=
  if f 2 = f 3 ∨ f 0 = f 1 then 0
  else if (f 0 = f 2 ∨ f 0 = f 3) ∧ (f 1 = f 2 ∨ f 1 = f 3) then 0
  else if (f 0 = f 2 ∨ f 0 = f 3) ∨ (f 1 = f 2 ∨ f 1 = f 3) then 1
  else 2 * rho

theorem tupleAnchor_injective (f : Fin 4 → P) (rho : ℚ) (hi : Function.Injective f) :
    tupleAnchor f rho = 2 * rho := by
  have hn (i j : Fin 4) (h : i ≠ j) : f i ≠ f j := fun he => h (hi he)
  simp [tupleAnchor,hn 2 3 (by decide),hn 0 1 (by decide),hn 0 2 (by decide),
    hn 0 3 (by decide),hn 1 2 (by decide),hn 1 3 (by decide)]

theorem tupleAnchor_at_most_two (f : Fin 4 → P) (rho : ℚ) (hc : portCount f ≤ 2) :
    tupleAnchor f rho = 0 := by
  rw [portCount_explicit] at hc
  by_cases h01 : f 0 = f 1 <;> by_cases h02 : f 0 = f 2 <;>
    by_cases h03 : f 0 = f 3 <;> by_cases h12 : f 1 = f 2 <;>
    by_cases h13 : f 1 = f 3 <;> by_cases h23 : f 2 = f 3
  all_goals simp_all [tupleAnchor]

theorem portCount_le_four (f : Fin 4 → P) : portCount f ≤ 4 := by
  simpa [portCount] using (Finset.card_image_le (s := Finset.univ) (f := f))

theorem portCount_four_iff_injective (f : Fin 4 → P) : portCount f = 4 ↔ Function.Injective f := by
  rw [portCount]
  have hc : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  simpa only [hc,Finset.coe_univ,Set.injOn_univ] using
    (Finset.card_image_iff (s := (Finset.univ : Finset (Fin 4))) (f := f))
end Nanuq.PortPatterns

namespace Nanuq.Source.RootedBinary
open scoped Classical
open Nanuq.PortPatterns
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_three_port_anchor_value (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b) (rho : ℚ)
    (hc : portCount (fun i => N.blobProjection b hb (q i)) = 3) :
    tupleAnchor (fun i => N.blobProjection b hb (q i)) rho = N.rawQuartetMean q := by
  let f := fun i => N.blobProjection b hb (q i)
  change portCount f = 3 at hc
  change tupleAnchor f rho = N.rawQuartetMean q
  rw [portCount_explicit] at hc
  have r01 := N.actual_repeated_port_pair_raw_mean q b hb
  have r02 := N.actual_repeated_cross_port_raw_mean q b hb
  have r03 := N.actual_repeated_port_03_raw_mean q b hb
  have r12 := N.actual_repeated_port_12_raw_mean q b hb
  have r13 := N.actual_repeated_port_13_raw_mean q b hb
  have r23 := N.actual_repeated_port_23_raw_mean q b hb
  change f 0 = f 1 → f 2 ≠ f 0 → f 3 ≠ f 0 → _ at r01
  change f 0 = f 2 → f 1 ≠ f 0 → f 3 ≠ f 0 → _ at r02
  change f 0 = f 3 → f 1 ≠ f 0 → f 2 ≠ f 0 → _ at r03
  change f 1 = f 2 → f 0 ≠ f 1 → f 3 ≠ f 1 → _ at r12
  change f 1 = f 3 → f 0 ≠ f 1 → f 2 ≠ f 1 → _ at r13
  change f 2 = f 3 → f 0 ≠ f 2 → f 1 ≠ f 2 → _ at r23
  by_cases h01 : f 0 = f 1 <;> by_cases h02 : f 0 = f 2 <;>
    by_cases h03 : f 0 = f 3 <;> by_cases h12 : f 1 = f 2 <;>
    by_cases h13 : f 1 = f 3 <;> by_cases h23 : f 2 = f 3
  all_goals simp_all [tupleAnchor]
  all_goals first
    | exact (r01 (Ne.symm h12) (Ne.symm h13)).symm
    | exact (r02 (Ne.symm h23)).symm
    | exact (r12 (Ne.symm h23)).symm
end Nanuq.Source.RootedBinary
