import RotateGaps
import AdjacentBlocks
import Mathlib.Data.List.Count

/-! UNCOMPILED finite block factorization. Actual-source count and gap
hypotheses must be derived before use; this is not a new network certificate. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Restriction

theorem mem_blocks_iff (base : List Nat) (dup : Nat → Bool) (x : Nat) :
    x∈blocks base dup ↔ x∈base := by
  induction base with
  | nil => simp [blocks]
  | cons a as ih =>
    change x∈(if dup a then [a,a] else [a])++blocks as dup ↔ x∈a::as
    cases h : dup a <;> simp [h,ih]

theorem blocks_congr (base : List Nat) (d e : Nat → Bool)
    (h : ∀ x∈base, d x=e x) : blocks base d=blocks base e := by
  induction base with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y∈xs, d y=e y := by intro y hy; exact h y (by simp [hy])
    change (if d x then [x,x] else [x])++blocks xs d=
      (if e x then [x,x] else [x])++blocks xs e
    rw [hx,ih ht]

theorem linearGap_remove_head {x y : Nat} {xs : List Nat} (hne : x≠y)
    (h : LinearGap (x::xs) y y) : LinearGap xs y y := by
  obtain ⟨pre,post,he⟩ := h
  cases pre with
  | nil => exact False.elim (hne (by simpa using congrArg List.head? he))
  | cons z pre =>
    have ht : xs=pre++y::y::post := (List.cons.inj he).2
    exact ⟨pre,post,ht⟩

/-- If x begins the list, any linear double-x block must be its first two
positions; otherwise count<=2 would be violated. -/
theorem linear_double_at_head {x : Nat} {xs : List Nat}
    (hc : (x::xs).count x≤2) (h : LinearGap (x::xs) x x) :
    ∃ rest, xs=x::rest := by
  obtain ⟨pre,post,he⟩ := h
  cases pre with
  | nil => exact ⟨post,(List.cons.inj he).2⟩
  | cons z pre =>
    have hz : x=z := (List.cons.inj he).1
    subst z
    have hc' := hc
    rw [he] at hc'
    simp only [List.cons_append,List.count_cons_self,List.count_append] at hc'
    omega

/-- A list whose labels occur at most twice and whose repeated labels have a
LINEAR adjacent pair is exactly a singleton/double expansion of a Nodup base. -/
theorem linear_blocks_factor (xs : List Nat)
    (hcount : ∀ x, xs.count x≤2)
    (hpairs : ∀ x, xs.count x=2 → LinearGap xs x x) :
    ∃ base dup, base.Nodup ∧ xs=blocks base dup := by
  classical
  generalize hn : xs.length=n
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => exact ⟨[],fun _ => false,by simp,rfl⟩
    | cons x xs =>
      by_cases hx : xs.count x=0
      · have hnot : x∉xs := by
          intro hm
          have hpos := List.count_pos_iff.mpr hm
          omega
        have hc : ∀ y, xs.count y≤2 := by
          intro y
          have h := hcount y
          simp only [List.count_cons] at h
          omega
        have hp : ∀ y, xs.count y=2 → LinearGap xs y y := by
          intro y hy
          have hyx : x≠y := by intro he; subst y; omega
          apply linearGap_remove_head hyx
          apply hpairs y
          simpa [List.count_cons,hyx,Ne.symm hyx] using hy
        obtain ⟨base,dup,hnd,he⟩ := ih xs.length (by simp only [List.length_cons] at hn; omega)
          xs hc hp rfl
        have hnb : x∉base := by
          intro hm
          exact hnot (he.symm ▸ (mem_blocks_iff base dup x).mpr hm)
        let d : Nat → Bool := fun y => if y=x then false else dup y
        have hd : blocks base d=blocks base dup := blocks_congr base d dup (by
          intro y hy
          have hne : y≠x := by intro h; subst y; exact hnb hy
          simp [d,hne])
        refine ⟨x::base,d,List.nodup_cons.mpr ⟨hnb,hnd⟩,?_⟩
        change x::xs=(if d x then [x,x] else [x])++blocks base d
        have hdx : d x=false := by simp [d]
        rw [hdx]
        change x::xs=x::blocks base d
        rw [hd,← he]
      · have hcx : (x::xs).count x=2 := by
          have hc := hcount x
          simp only [List.count_cons_self] at hc ⊢
          omega
        obtain ⟨rest,rfl⟩ := linear_double_at_head (hcount x) (hpairs x hcx)
        have hrest0 : rest.count x=0 := by
          simp only [List.count_cons_self] at hcx
          omega
        have hnot : x∉rest := by intro hm; have hpos := List.count_pos_iff.mpr hm; omega
        have hc : ∀ y, rest.count y≤2 := by
          intro y
          have h := hcount y
          simp only [List.count_cons] at h
          omega
        have hp : ∀ y, rest.count y=2 → LinearGap rest y y := by
          intro y hy
          have hyx : x≠y := by intro he; subst y; omega
          apply linearGap_remove_head hyx
          apply linearGap_remove_head hyx
          apply hpairs y
          simpa [List.count_cons,hyx,Ne.symm hyx] using hy
        obtain ⟨base,dup,hnd,he⟩ := ih rest.length (by simp only [List.length_cons] at hn; omega)
          rest hc hp rfl
        have hnb : x∉base := by
          intro hm
          exact hnot (he.symm ▸ (mem_blocks_iff base dup x).mpr hm)
        let d : Nat → Bool := fun y => if y=x then true else dup y
        have hd : blocks base d=blocks base dup := blocks_congr base d dup (by
          intro y hy
          have hne : y≠x := by intro h; subst y; exact hnb hy
          simp [d,hne])
        refine ⟨x::base,d,List.nodup_cons.mpr ⟨hnb,hnd⟩,?_⟩
        change x::x::rest=(if d x then [x,x] else [x])++blocks base d
        have hdx : d x=true := by simp [d]
        rw [hdx]
        change x::x::rest=x::x::blocks base d
        rw [hd,← he]

#print axioms linear_blocks_factor
end Nanuq.Restriction
