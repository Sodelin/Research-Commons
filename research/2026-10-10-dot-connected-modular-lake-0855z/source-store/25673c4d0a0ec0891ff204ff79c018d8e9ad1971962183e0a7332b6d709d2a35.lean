import SourceNetwork
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
Bounded executable reachability used by the original edge-ID admission tests.
Contributor: dot, 2026-10-09. Ordinary finite saturation, without a decision
oracle. The bound is the actual finite vertex count.
-/
namespace GProgram.G7.FiniteReachability
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop) [DecidableRel R]

def grow (s : Finset V) : Finset V :=
  s ∪ Finset.univ.filter (fun b => ∃ a ∈ s, R a b)

def reached (a : V) : ℕ → Finset V
  | 0 => {a}
  | n+1 => grow R (reached a n)

theorem subset_grow (s : Finset V) : s ⊆ grow R s := Finset.subset_union_left

theorem grow_mono {s t : Finset V} (h : s ⊆ t) : grow R s ⊆ grow R t := by
  intro b hb
  rcases Finset.mem_union.mp hb with hb | hb
  · exact Finset.mem_union_left _ (h hb)
  · obtain ⟨a,ha,hr⟩ := (Finset.mem_filter.mp hb).2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,h ha,hr⟩)

theorem reached_step (a : V) (n : ℕ) : reached R a n ⊆ reached R a (n+1) := subset_grow R _

theorem reached_mono (a : V) {m n : ℕ} (h : m ≤ n) : reached R a m ⊆ reached R a n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @step n h ih => exact Finset.Subset.trans ih (reached_step R a n)

theorem self_mem (a : V) (n : ℕ) : a ∈ reached R a n :=
  reached_mono R a (Nat.zero_le n) (by simp [reached])

theorem reached_sound (a : V) (n : ℕ) {b : V} (h : b ∈ reached R a n) :
    Relation.ReflTransGen R a b := by
  induction n generalizing b with
  | zero => have he : b = a := by simpa [reached] using h
            subst b; exact .refl
  | succ n ih =>
    rcases Finset.mem_union.mp h with hb | hb
    · exact ih hb
    · obtain ⟨c,hc,hr⟩ := (Finset.mem_filter.mp hb).2
      exact (ih hc).tail hr

theorem stable_later (a : V) {k : ℕ} (h : reached R a k = reached R a (k+1))
    (j : ℕ) : reached R a (k+j) = reached R a k := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      reached R a (k+(j+1)) = grow R (reached R a (k+j)) := by rw [Nat.add_succ, reached]
      _ = grow R (reached R a k) := congrArg (grow R) ih
      _ = reached R a k := h.symm

theorem exists_stable (a : V) : ∃ k ≤ Fintype.card V,
    reached R a k = reached R a (k+1) := by
  by_contra hn
  have hneq : ∀ k ≤ Fintype.card V, reached R a k ≠ reached R a (k+1) := by
    intro k hk he
    exact hn ⟨k,hk,he⟩
  have hc : ∀ k ≤ Fintype.card V, k+1 ≤ (reached R a k).card := by
    intro k
    induction k with
    | zero => intro _; simp [reached]
    | succ k ih =>
      intro hk
      have ht : (reached R a k).card < (reached R a (k+1)).card :=
        Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr
          ⟨reached_step R a k, hneq k (by omega)⟩)
      have hi := ih (by omega)
      omega
  have hi := hc (Fintype.card V) (by omega)
  have hb := Finset.card_le_univ (reached R a (Fintype.card V))
  omega

theorem reached_complete (a b : V) (h : Relation.ReflTransGen R a b) :
    b ∈ reached R a (Fintype.card V) := by
  obtain ⟨k,hk,hs⟩ := exists_stable R a
  have hc : ∀ x y, x ∈ reached R a k → R x y → y ∈ reached R a k := by
    intro x y hx hr
    rw [hs]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx,hr⟩)
  have hm : b ∈ reached R a k := by
    induction h with
    | refl => exact self_mem R a k
    | tail _ hr ih => exact hc _ _ ih hr
  exact reached_mono R a hk hm

theorem reached_iff (a b : V) : b ∈ reached R a (Fintype.card V) ↔
    Relation.ReflTransGen R a b := ⟨reached_sound R a _, reached_complete R a b⟩

def decideReach (a b : V) : Decidable (Relation.ReflTransGen R a b) :=
  decidable_of_iff _ (reached_iff R a b)

#print axioms reached_iff
#print axioms decideReach
end GProgram.G7.FiniteReachability
