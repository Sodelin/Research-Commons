import CyclicGaps
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Real.Basic

/-! UNCOMPILED independent finite receiver draft. It consumes the exact
empty-middle/empty-wrap property derived at the source use site, and does not
assume a new geometric or original-input order certificate. -/
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

/-- Strictly ordered ranks turn an empty parameter middle into successive
indices, or an empty parameter outside into the last-to-first wrap. -/
theorem rank_gap_cases {n : Nat} (θ : Fin n → ℝ) (hθ : StrictMono θ)
    (a c : Fin n) (hac : a<c)
    (hgap : (∀ w, ¬(θ a<θ w ∧ θ w<θ c)) ∨
      (∀ w, ¬(θ w<θ a ∨ θ c<θ w))) :
    c.val=a.val+1 ∨ (a.val=0 ∧ c.val+1=n) := by
  rcases hgap with hmiddle | houtside
  · left
    by_contra hnot
    have hac' : a.val<c.val := hac
    have hnext : a.val+1<c.val := by omega
    let w : Fin n := ⟨a.val+1,by omega⟩
    exact hmiddle w ⟨hθ (show a<w from by change a.val<a.val+1; omega),
      hθ (show w<c from hnext)⟩
  · right
    constructor
    · by_contra ha
      let w : Fin n := ⟨0,by omega⟩
      exact houtside w (Or.inl (hθ (show w<a from by change 0<a.val; omega)))
    · by_contra hc
      have hn : c.val+1<n := by omega
      let w : Fin n := ⟨c.val+1,hn⟩
      exact houtside w (Or.inr (hθ (show c<w from by change c.val<c.val+1; omega)))

/-- The existing finite restriction receiver's EXACT gap predicate, with the
orientation determined by the actual empty interval rather than chosen freely. -/
theorem rank_cyclic_gap {n : Nat} (θ : Fin n → ℝ) (hθ : StrictMono θ)
    (a c : Fin n) (hac : a<c)
    (hgap : (∀ w, ¬(θ a<θ w ∧ θ w<θ c)) ∨
      (∀ w, ¬(θ w<θ a ∨ θ c<θ w))) :
    CyclicGap (List.range n) a.val c.val ∨ CyclicGap (List.range n) c.val a.val := by
  have hn : 2≤n := by have ha := a.isLt; have hc := c.isLt; have hac' : a.val<c.val := hac; omega
  rcases rank_gap_cases θ hθ a c hac hgap with hnext | ⟨ha,hc⟩
  · left
    have h := range_gap n a.val hn a.isLt
    have hmod : (a.val+1)%n=c.val := by rw [← hnext,Nat.mod_eq_of_lt c.isLt]
    simpa only [hmod] using h
  · right
    have h := range_gap n c.val hn c.isLt
    simpa only [hc,Nat.mod_self,ha] using h

#print axioms rank_gap_cases
#print axioms rank_cyclic_gap
end Nanuq.Restriction
