import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Omega

/-! Local uncompiled finite-order part of the actual full-split integration.
The crossing prohibition below must be DERIVED from the original switching
resolution and same-rank finite receiver at the source-facing use site. -/
namespace Nanuq.ActualCutClusters

/-- A proper side oriented away from rank zero has no linear hole once actual
sorted crossing quartets have been excluded. Small sides need no quartet. -/
theorem convex_of_no_zero_crossing (S : Finset Nat) (hz : 0 ∉ S)
    (hcross : ∀ x y z : Nat, 0 < x → x < y → y < z →
      x ∈ S → y ∉ S → z ∈ S → False) :
    ∀ x y z : Nat, x ∈ S → z ∈ S → x ≤ y → y ≤ z → y ∈ S := by
  intro x y z hx hzs hxy hyz
  by_cases he : x = y
  · exact he ▸ hx
  by_cases he' : y = z
  · exact he'.symm ▸ hzs
  by_contra hy
  have hx0 : 0 < x := by
    by_contra hh
    have : x = 0 := by omega
    exact hz (this ▸ hx)
  exact hcross x y z hx0 (by omega) (by omega) hx hy hzs

/-- Nonempty finite convex sides are literal rank intervals. -/
theorem convex_side_interval (S : Finset Nat) (hne : S.Nonempty)
    (hz : 0 ∉ S)
    (hc : ∀ x y z : Nat, x ∈ S → z ∈ S → x ≤ y → y ≤ z → y ∈ S) :
    ∃ i j : Nat, i < j ∧ S = Finset.Ioc i j := by
  let lo := S.min' hne
  let hi := S.max' hne
  have hlo : lo ∈ S := Finset.min'_mem S hne
  have hhi : hi ∈ S := Finset.max'_mem S hne
  have hlo0 : 0 < lo := by
    by_contra hh
    have : lo = 0 := by omega
    exact hz (this ▸ hlo)
  have hle : lo ≤ hi := Finset.min'_le S hi hhi
  refine ⟨lo - 1, hi, by omega, ?_⟩
  ext x
  rw [Finset.mem_Ioc]
  constructor
  · intro hx
    have hl : lo ≤ x := Finset.min'_le S x hx
    have hh : x ≤ hi := Finset.le_max' S x hx
    omega
  · intro hx
    exact hc lo x hi hlo hhi (by omega) hx.2

/-- Exact adjacent-gap pinning. The upper wrap is represented by j+1=n,
so its omitted neighbour is rank0 rather than an out-of-range label. -/
theorem boundary_pins_convex_side (n i j : Nat) (hij : i < j) (hjn : j < n)
    (S : Finset Nat) (hbound : ∀ x ∈ S, x < n) (hz : 0 ∉ S)
    (hc : ∀ x y z : Nat, x ∈ S → z ∈ S → x ≤ y → y ≤ z → y ∈ S)
    (hin : i+1 ∈ S ∧ j ∈ S)
    (hout : i ∉ S ∧ (if j+1=n then 0 else j+1) ∉ S) :
    S = Finset.Ioc i j := by
  ext x
  rw [Finset.mem_Ioc]
  constructor
  · intro hx
    have hix : i < x := by
      by_contra hh
      exact hout.1 (hc x i (i+1) hx hin.1 (by omega) (by omega))
    have hxj : x ≤ j := by
      by_contra hh
      by_cases he : j+1=n
      · have hb := hbound x hx
        omega
      · have hnext : j+1 ∈ S := hc j (j+1) x hin.2 hx (by omega) (by omega)
        have hnot : j+1 ∉ S := by simpa [he] using hout.2
        exact hnot hnext
    exact ⟨hix,hxj⟩
  · intro hx
    exact hc (i+1) x j hin.1 hin.2 (by omega) hx.2

/-- The rank0-avoiding convex side cannot be the two OUTER boundary labels. -/
theorem boundary_outer_orientation_impossible (n i j : Nat) (hij : i < j)
    (S : Finset Nat) (hz : 0 ∉ S)
    (hc : ∀ x y z : Nat, x ∈ S → z ∈ S → x ≤ y → y ≤ z → y ∈ S)
    (hout : i ∈ S ∧ (if j+1=n then 0 else j+1) ∈ S)
    (hin : i+1 ∉ S) : False := by
  by_cases he : j+1=n
  · exact hz (by simpa [he] using hout.2)
  · have hnext : j+1 ∈ S := by simpa [he] using hout.2
    exact hin (hc i (i+1) (j+1) hout.1 hnext (by omega) (by omega))

end Nanuq.ActualCutClusters
