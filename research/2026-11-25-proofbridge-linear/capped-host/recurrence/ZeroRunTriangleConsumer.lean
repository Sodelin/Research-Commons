import ZeroRunConsequences
import TriangleRun
set_option warningAsError true

namespace AlexanderZeroRun
open AlexanderOmnibus
open ResearchCommons.TriangleRun

private theorem slot_start_ge_four (m j : Nat) : 4 ≤ slotStart m j := by
  unfold slotStart startIndex
  have le : 2 ≤ pairCode m j+2 := by omega
  exact Nat.mul_le_mul le le

/-- Both preceding positions are switches, not just the maximality boundary. -/
theorem slot_before_two_ones (A : Nat → Prop) (m j d : Nat) (hd0 : 0 < d) (hd2 : d ≤ 2) :
    twist A (slotStart m j-d) = true := by
  apply (twist_true_iff _ _).2
  rintro ⟨p,q,_,hl,hh⟩
  have hp := slot_start_ge_four m j
  rcases Nat.lt_trichotomy (pairCode p q) (pairCode m j) with h|h|h
  · have hs := slot_spacing h
    omega
  · obtain ⟨rfl,rfl⟩ := pairCode_injective h
    omega
  · have hs := slot_spacing h
    omega

theorem selected_slot_actual_component (A : Nat → Prop)
    {m : Nat} (hm : A m) (j : Nat)
    (keep : ResearchCommons.TwoLiftTriangle.Vertex → Prop)
    (survives : ∀ v, slotStart m j ≤ v.1 → keep v) (b : Bool) :
    let lo := slotStart m j
    let vs := runVertices lo (lo+m) b
    vs.Nodup ∧ vs.length = m+3 ∧
      ∀ v, Reach (GraphTriangleEdge (twist A) keep) (lo,b) v ↔ v ∈ vs := by
  let lo := slotStart m j
  have hzero (n : Nat) (hl : lo ≤ n) (hr : n ≤ lo+m) : twist A n = false :=
    (twist_false_iff _ _).2 ⟨m,j,hm,hl,by omega⟩
  have hsep (n : Nat) (_ : 0 < n) (hl : lo ≤ n+2) (hr : n ≤ lo+m+2)
      (h : n < lo ∨ lo+m < n) : twist A n = true := by
    rcases h with h|h
    · let d := lo-n
      have hd0 : 0 < d := by omega
      have hd2 : d ≤ 2 := by omega
      have he : lo-d = n := by omega
      have ht := slot_before_two_ones A m j d hd0 hd2
      change twist A (lo-d) = true at ht
      rwa [he] at ht
    · let r := n-(lo+(m+1))
      have hr2 : r < 2 := by omega
      have he : lo+(m+1)+r = n := by omega
      have ht := slot_after_two_ones A m j r hr2
      change ¬Zero A (lo+(m+1)+r) at ht
      exact (twist_true_iff _ _).2 (by simpa only [he] using ht)
  simpa only [Nat.add_assoc] using
    (exact_component lo m (slotStart_positive m j) hzero hsep survives b)

/-- For each selected length there is an exact component in each sheet
arbitrarily far past any specified cutoff. The cutoff applies to the graph
vertices in the triangle, not merely its root. -/
theorem arbitrarily_late_exact_components (A : Nat → Prop) {m : Nat} (hm : A m)
    (keep : ResearchCommons.TwoLiftTriangle.Vertex → Prop)
    (cutoff bound : Nat) (after : ∀ v, cutoff ≤ v.1 → keep v) :
    ∃ lo, max cutoff bound ≤ lo ∧
      ∀ b : Bool,
        let vs := runVertices lo (lo+m) b
        vs.Nodup ∧ vs.length = m+3 ∧
          ∀ v, Reach (GraphTriangleEdge (twist A) keep) (lo,b) v ↔ v ∈ vs := by
  let j := max cutoff bound
  have h := slotStart_ge_index m j
  refine ⟨slotStart m j,h,fun b => selected_slot_actual_component A hm j keep ?_ b⟩
  intro v hv
  have hco : cutoff ≤ j := Nat.le_max_left _ _
  exact after v (Nat.le_trans hco (Nat.le_trans h hv))

#print axioms slot_before_two_ones
#print axioms selected_slot_actual_component
#print axioms arbitrarily_late_exact_components
end AlexanderZeroRun
