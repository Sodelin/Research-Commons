import AnchoredIntervals

/-! UNCOMPILED finite rank-convexity bookkeeping; source derivation remains
explicit at the final use site. -/
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V R : Type*} [LinearOrder R]

def RankConvex (ambient : List V) (rank : V → R) (side : List V) : Prop :=
  ∀ a∈side, ∀ c∈side, ∀ b∈ambient,
    rank a<rank b → rank b<rank c → b∈side

/-- Two disjoint nonempty convex occurrence sets cannot interleave. -/
theorem convex_sides_separated (ambient l r : List V) (rank : V → R)
    (hl : ∀ x∈l, x∈ambient) (hr : ∀ x∈r, x∈ambient)
    (hi : ∀ a∈ambient, ∀ b∈ambient, rank a=rank b → a=b)
    (hd : ∀ x∈l, x∉r) (hnl : l≠[]) (hnr : r≠[])
    (hcl : RankConvex ambient rank l) (hcr : RankConvex ambient rank r) :
    (∀ a∈l, ∀ c∈r, rank a<rank c) ∨
      (∀ c∈r, ∀ a∈l, rank c<rank a) := by
  have forward (l r : List V)
      (hl : ∀ x∈l, x∈ambient) (hr : ∀ x∈r, x∈ambient)
      (hd : ∀ x∈l, x∉r)
      (hcl : RankConvex ambient rank l) (hcr : RankConvex ambient rank r)
      (a c : V) (ha : a∈l) (hc : c∈r) (hac : rank a<rank c) :
      ∀ x∈l, ∀ y∈r, rank x<rank y := by
    intro x hx y hy
    have hxy : rank x≠rank y := by
      intro he
      exact hd x hx ((hi x (hl x hx) y (hr y hy) he).symm ▸ hy)
    by_contra hbad
    have hyx : rank y<rank x := lt_of_le_of_ne (le_of_not_gt hbad) (Ne.symm hxy)
    by_cases hay : rank a<rank y
    · exact hd y (hcl a ha x hx y (hr y hy) hay hyx) hy
    · have hya : rank y<rank a := by
        have hne : rank a≠rank y := by
          intro he
          exact hd a ha ((hi a (hl a ha) y (hr y hy) he).symm ▸ hy)
        exact lt_of_le_of_ne (le_of_not_gt hay) (Ne.symm hne)
      exact hd a ha (hcr y hy c hc a (hl a ha) hya hac)
  obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil l hnl
  obtain ⟨c,hc⟩ := List.exists_mem_of_ne_nil r hnr
  have hne : rank a≠rank c := by
    intro he
    exact hd a ha ((hi a (hl a ha) c (hr c hc) he).symm ▸ hc)
  rcases lt_or_gt_of_ne hne with hac | hca
  · exact Or.inl (forward l r hl hr hd hcl hcr a c ha hc hac)
  · exact Or.inr (forward r l hr hl (by intro x hx hxl; exact hd x hxl hx)
      hcr hcl c a hc ha hca)

theorem frontier_nonempty (t : BinarySyntax V) : t.frontier≠[] := by
  induction t with
  | tip v => simp [BinarySyntax.frontier]
  | fork v l r il ir =>
    intro he
    exact il (List.append_eq_nil_iff.mp he).1

#print axioms convex_sides_separated
end Nanuq.GraphReceiver
