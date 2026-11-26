import CappedPaddingLanguage

namespace ResearchCommons.CappedLabeledGrid
open ResearchCommons.CappedPaddingLanguage

abbrev Cell (n : Nat) := Fin n × Fin n
abbrev Vertex (n k : Nat) := Sum (Cell n × Fin k) (Cell n)

def east {n : Nat} (a b : Cell n) : Prop :=
  a.1 = b.1 ∧ a.2.val + 1 = b.2.val
def north {n : Nat} (a b : Cell n) : Prop :=
  a.1.val + 1 = b.1.val ∧ a.2 = b.2

def missing {n : Nat} (b : Cell n) (l : Nat) : Prop :=
  ¬ (0 < b.2.val ∧ l = 0) ∧ ¬ (0 < b.1.val ∧ l = 1)

instance {n : Nat} (a b : Cell n) : Decidable (east a b) := by unfold east; infer_instance
instance {n : Nat} (a b : Cell n) : Decidable (north a b) := by unfold north; infer_instance
instance {n : Nat} (b : Cell n) (l : Nat) : Decidable (missing b l) := by unfold missing; infer_instance

def edge {n k : Nat} : Vertex n k → Vertex n k → Option Nat
  | .inl (owner,l), .inr dst =>
      if owner = dst ∧ missing dst l.val then some l.val else none
  | .inr a, .inr b =>
      if east a b then some 0 else if north a b then some 1 else none
  | _, _ => none

def rank {n k : Nat} : Vertex n k → Nat
  | .inl _ => 0
  | .inr (r,c) => r.val + c.val + 1

theorem rank_bounded {n k : Nat} (v : Vertex n k) : rank v ≤ 2*n := by
  cases v with
  | inl x => simp [rank]
  | inr x =>
    obtain ⟨r,c⟩ := x
    have hr := r.isLt
    have hc := c.isLt
    simp only [rank]
    omega

theorem rank_rises {n k : Nat} (a b : Vertex n k) (l : Nat)
    (h : edge a b = some l) : rank a < rank b := by
  cases b with
  | inl v => cases a <;> simp [edge] at h
  | inr b =>
    obtain ⟨br,bc⟩ := b
    cases a with
    | inl a => simp [rank]
    | inr a =>
      obtain ⟨ar,ac⟩ := a
      by_cases e : east (ar,ac) (br,bc)
      · obtain ⟨hr,hc⟩ := e
        change ar = br at hr
        change ac.val + 1 = bc.val at hc
        simp only [rank]
        rw [hr]
        omega
      · by_cases q : north (ar,ac) (br,bc)
        · obtain ⟨hr,hc⟩ := q
          change ac = bc at hc
          change ar.val + 1 = br.val at hr
          simp only [rank]
          rw [hc]
          omega
        · simp [edge,e,q] at h

theorem every_cell_label {n k : Nat} (b : Cell n) (l : Fin k) :
    ∃ v : Vertex n k, edge v (Sum.inr b) = some l.val := by
  obtain ⟨r,c⟩ := b
  by_cases w : 0 < c.val ∧ l.val = 0
  · let prev : Fin n := ⟨c.val-1, by have h := c.isLt; omega⟩
    have e : east (r,prev) (r,c) := ⟨rfl,by dsimp [prev]; omega⟩
    exact ⟨Sum.inr (r,prev),by simp [edge,e,w.2]⟩
  by_cases s : 0 < r.val ∧ l.val = 1
  · let prev : Fin n := ⟨r.val-1, by have h := r.isLt; omega⟩
    have q : north (prev,c) (r,c) := ⟨by dsimp [prev]; omega,rfl⟩
    have ne : ¬ east (prev,c) (r,c) := by
      intro he
      have hc : c.val + 1 = c.val := he.2
      omega
    exact ⟨Sum.inr (prev,c),by simp [edge,ne,q,s.2]⟩
  · exact ⟨Sum.inl ((r,c),l),by simp [edge,missing,w,s]⟩

/-- Edge-labelled grid padding changes no word of any base graph. -/
theorem preserves_words {V : Type} (base : V → V → Option Nat)
    (n k : Nat) (word : Nat → Nat) :
    Realizes (joined base (@edge n k)) word ↔ Realizes base word :=
  padding_preserves base (@edge n k) rank (2*n) rank_bounded rank_rises word

def eastCandidates {n k : Nat} (a : Cell n) : List (Vertex n k) :=
  if h : a.2.val + 1 < n then [Sum.inr (a.1,⟨a.2.val+1,h⟩)] else []
def northCandidates {n k : Nat} (a : Cell n) : List (Vertex n k) :=
  if h : a.1.val + 1 < n then [Sum.inr (⟨a.1.val+1,h⟩,a.2)] else []

/-- Every actual child is in a list of length at most two. -/
theorem children_covered {n k : Nat} (v : Vertex n k) :
    ∃ xs : List (Vertex n k), xs.length ≤ 2 ∧
      ∀ w l, edge v w = some l → w ∈ xs := by
  cases v with
  | inl slot =>
    obtain ⟨owner,label⟩ := slot
    refine ⟨[Sum.inr owner],by simp,?_⟩
    intro w l h
    cases w with
    | inl _ => simp [edge] at h
    | inr dst =>
      by_cases hd : owner = dst ∧ missing dst label.val
      · simp [hd.1]
      · simp [edge,hd] at h
  | inr a =>
    have eLen : (@eastCandidates n k a).length ≤ 1 := by
      unfold eastCandidates
      split <;> simp
    have nLen : (@northCandidates n k a).length ≤ 1 := by
      unfold northCandidates
      split <;> simp
    refine ⟨eastCandidates a ++ northCandidates a,by simp only [List.length_append]; omega,?_⟩
    intro w l h
    cases w with
    | inl _ => simp [edge] at h
    | inr b =>
      by_cases e : east a b
      · apply List.mem_append.mpr
        left
        have hb : a.2.val + 1 < n := e.2 ▸ b.2.isLt
        have same : b = (a.1,⟨a.2.val+1,hb⟩) :=
          Prod.ext e.1.symm (Fin.ext e.2.symm)
        simp [eastCandidates,hb]
        exact same
      · by_cases q : north a b
        · apply List.mem_append.mpr
          right
          have hb : a.1.val + 1 < n := q.1 ▸ b.1.isLt
          have same : b = (⟨a.1.val+1,hb⟩,a.2) :=
            Prod.ext (Fin.ext q.1.symm) q.2.symm
          simp [northCandidates,hb]
          exact same
        · simp [edge,e,q] at h

theorem grid_east_edge {n k : Nat} (a b : Cell n) (h : east a b) :
    @edge n k (.inr a) (.inr b) = some 0 := by simp [edge,h]
theorem grid_north_edge {n k : Nat} (a b : Cell n) (h : north a b) :
    @edge n k (.inr a) (.inr b) = some 1 := by
  have ne : ¬ east a b := by
    intro e
    have h1 : a.1.val + 1 = b.1.val := h.1
    rw [e.1] at h1
    omega
  simp [edge,ne,h]

theorem edges_use_labels {n k : Nat} (hk : 2 ≤ k)
    (v w : Vertex n k) (l : Nat) (h : edge v w = some l) : l < k := by
  cases w with
  | inl _ => cases v <;> simp [edge] at h
  | inr b =>
    cases v with
    | inl a =>
      obtain ⟨owner,label⟩ := a
      by_cases hd : owner = b ∧ missing b label.val
      · have eq : label.val = l := by simpa [edge,hd] using h
        exact eq ▸ label.isLt
      · simp [edge,hd] at h
    | inr a =>
      by_cases e : east a b
      · have eq : 0 = l := by simpa [edge,e] using h
        omega
      · by_cases q : north a b
        · have eq : 1 = l := by simpa [edge,e,q] using h
          omega
        · simp [edge,e,q] at h

theorem no_edge_into_private_root {n k : Nat} (v : Vertex n k) (r : Cell n × Fin k) :
    edge v (Sum.inl r) = none := by cases v <;> rfl

#print axioms edges_use_labels
#print axioms every_cell_label
#print axioms children_covered
#print axioms grid_east_edge
#print axioms grid_north_edge
#print axioms preserves_words
end ResearchCommons.CappedLabeledGrid
