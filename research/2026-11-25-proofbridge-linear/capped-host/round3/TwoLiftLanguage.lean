import SamuelAlexanderResearch.BinaryAvoidance
import TwoLiftTriangle

set_option warningAsError true

namespace ResearchCommons.TwoLiftLanguage
open ResearchCommons.TwoLiftTriangle

def Edge (labels twist : Nat → Bool) (u v : Vertex) (b : Bool) : Prop :=
  BinaryAvoidance.Edge labels u.1 v.1 b ∧ Up twist u v

def lift (twist : Nat → Bool) (path : Nat → Nat) : Nat → Vertex
  | 0 => (path 0,false)
  | n+1 =>
    let u := lift twist path n
    let w := path (n+1)
    (w, if w = u.1+1 then u.2 else Bool.xor u.2 (twist u.1))

theorem lift_first (twist : Nat → Bool) (path : Nat → Nat) (n : Nat) :
    (lift twist path n).1 = path n := by cases n <;> rfl

theorem lifts_edge (labels twist : Nat → Bool) (path : Nat → Nat) (n : Nat) (b : Bool)
    (h : BinaryAvoidance.Edge labels (path n) (path (n+1)) b) :
    Edge labels twist (lift twist path n) (lift twist path (n+1)) b := by
  refine ⟨by simpa only [lift_first] using h, ?_⟩
  have hn := lift_first twist path n
  obtain ⟨lower, hstep | hstep⟩ := h
  · obtain ⟨short,_⟩ := hstep
    have hs : path (n+1) = (lift twist path n).1 + 1 := by omega
    exact Or.inl ⟨by omega,hs,by simp [lift, hs]⟩
  · obtain ⟨long,_⟩ := hstep
    have hl : path (n+1) = (lift twist path n).1 + 2 := by omega
    have notShort : path (n+1) ≠ (lift twist path n).1 + 1 := by omega
    exact Or.inr ⟨hl,by simp [lift,notShort]⟩

/-- Any switching pattern preserves the original ladder's whole infinite
edge-label language, not just its avoidance of the designated word. -/
theorem same_language (labels twist word : Nat → Bool) :
    (∃ p : Nat → Vertex, ∀ n, Edge labels twist (p n) (p (n+1)) (word n)) ↔
    (∃ p : Nat → Nat, ∀ n, BinaryAvoidance.Edge labels (p n) (p (n+1)) (word n)) := by
  constructor
  · rintro ⟨p,h⟩
    exact ⟨fun n => (p n).1,fun n => (h n).1⟩
  · rintro ⟨p,h⟩
    exact ⟨lift twist p,fun n => lifts_edge labels twist p n (word n) (h n)⟩

theorem aperiodic_target_avoided (s twist : Nat → Bool)
    (aperiodic : ¬ BinaryAvoidance.EventuallyPeriodic s) :
    ¬ ∃ p : Nat → Vertex, ∀ n, Edge s twist (p n) (p (n+1)) (s n) := by
  intro h
  exact BinaryAvoidance.aperiodic_target_avoided s aperiodic ((same_language s twist s).mp h)

#print axioms same_language
#print axioms aperiodic_target_avoided
end ResearchCommons.TwoLiftLanguage
