import CappedLabeledGrid

namespace ResearchCommons.FixedGender
open ResearchCommons.CappedPaddingLanguage ResearchCommons.CappedLabeledGrid

def gender {n k : Nat} : Vertex n k → Nat
  | .inl (_, l) => l.val
  | .inr a => a.1.val % 2

def unserved {n : Nat} (b : Cell n) (l : Nat) : Prop :=
  ¬ (0 < b.2.val ∧ l = b.1.val % 2) ∧
  ¬ (0 < b.1.val ∧ l = (b.1.val - 1) % 2)

instance {n : Nat} (b : Cell n) (l : Nat) : Decidable (unserved b l) := by
  unfold unserved; infer_instance

def fixedEdge {n k : Nat} (a b : Vertex n k) : Option Nat :=
  match a, b with
  | .inl (owner,l), .inr dst =>
      if owner = dst ∧ unserved dst l.val then some l.val else none
  | .inr u, .inr v =>
      if east u v ∨ north u v then some (gender (Sum.inr u : Vertex n k)) else none
  | _, _ => none

theorem fixedLabel {n k : Nat} (a b : Vertex n k) (l : Nat)
    (h : fixedEdge a b = some l) : gender a = l := by
  cases a with
  | inl x =>
    obtain ⟨o,g⟩ := x
    cases b with
    | inl _ => simp [fixedEdge] at h
    | inr b => simp only [fixedEdge] at h; split at h <;> simp_all [gender]
  | inr a =>
    cases b with
    | inl _ => simp [fixedEdge] at h
    | inr b => simp only [fixedEdge] at h; split at h <;> simp_all

theorem grid_edge {n k : Nat} (a b : Cell n) (h : east a b ∨ north a b) :
    @fixedEdge n k (.inr a) (.inr b) = some (gender (.inr a : Vertex n k)) := by
  simp [fixedEdge,h]

theorem everyLabel {n k : Nat} (b : Cell n) (l : Fin k) :
    ∃ v : Vertex n k, fixedEdge v (.inr b) = some l.val := by
  obtain ⟨r,c⟩ := b
  by_cases w : 0 < c.val ∧ l.val = r.val % 2
  · let p : Fin n := ⟨c.val-1, by have h := c.isLt; omega⟩
    have e : east (r,p) (r,c) := ⟨rfl,by dsimp [p]; omega⟩
    exact ⟨.inr (r,p),by rw [grid_edge _ _ (.inl e)]; simp [gender,w.2]⟩
  by_cases s : 0 < r.val ∧ l.val = (r.val-1) % 2
  · let p : Fin n := ⟨r.val-1, by have h := r.isLt; omega⟩
    have q : north (p,c) (r,c) := ⟨by dsimp [p]; omega,rfl⟩
    exact ⟨.inr (p,c),by rw [grid_edge _ _ (.inr q)]; simp [gender,p,s.2]⟩
  · exact ⟨.inl ((r,c),l),by simp [fixedEdge,unserved,w,s]⟩

theorem grid_original {n k : Nat} (a b : Cell n) (l : Nat)
    (h : @fixedEdge n k (.inr a) (.inr b) = some l) :
    ∃ m, @CappedLabeledGrid.edge n k (.inr a) (.inr b) = some m := by
  by_cases e : east a b
  · exact ⟨0, grid_east_edge a b e⟩
  by_cases q : north a b
  · exact ⟨1, grid_north_edge a b q⟩
  simp [fixedEdge,e,q] at h

theorem gender_lt {n k : Nat} (hk : 2 ≤ k) (v : Vertex n k) : gender v < k := by
  cases v with
  | inl p => exact p.2.isLt
  | inr c => change c.1.val % 2 < k; omega

theorem fixed_rank_rises {n k : Nat} (a b : Vertex n k) (l : Nat)
    (h : fixedEdge a b = some l) : rank a < rank b := by
  cases b with
  | inl _ => cases a <;> simp [fixedEdge] at h
  | inr b =>
    cases a with
    | inl a => obtain ⟨r,c⟩ := b; simp [rank]
    | inr a =>
      obtain ⟨m,hm⟩ := grid_original a b l h
      exact rank_rises (.inr a : Vertex n k) (.inr b) m hm

theorem fixed_children_covered {n k : Nat} (v : Vertex n k) :
    ∃ xs : List (Vertex n k), xs.length ≤ 2 ∧
      ∀ w l, fixedEdge v w = some l → w ∈ xs := by
  cases v with
  | inl slot =>
    obtain ⟨owner,label⟩ := slot
    refine ⟨[.inr owner], by simp, ?_⟩
    intro w l h
    cases w with
    | inl _ => simp [fixedEdge] at h
    | inr dst =>
      by_cases hd : owner = dst
      · simp [hd]
      · simp [fixedEdge,hd] at h
  | inr a =>
    obtain ⟨xs,hs,cover⟩ := children_covered (.inr a : Vertex n k)
    refine ⟨xs,hs,?_⟩
    intro w l h
    cases w with
    | inl _ => simp [fixedEdge] at h
    | inr b =>
      obtain ⟨m,hm⟩ := grid_original a b l h
      exact cover _ m hm

theorem fixed_preserves_words {V : Type} (base : V → V → Option Nat)
    (n k : Nat) (word : Nat → Nat) :
    Realizes (joined base (@fixedEdge n k)) word ↔ Realizes base word :=
  padding_preserves base (@fixedEdge n k) rank (2*n) rank_bounded fixed_rank_rises word

def cellCode {n : Nat} (a : Cell n) : Nat := a.1.val*n + a.2.val

def time {n k : Nat} : Vertex n k → Nat
  | .inl (a,l) => cellCode a * k + l.val
  | .inr a => n*n*k + cellCode a

private theorem cell_lt {n : Nat} (a : Cell n) : cellCode a < n*n := by
  unfold cellCode
  have h := Nat.mul_le_mul_right n a.1.isLt
  rw [Nat.succ_mul] at h
  have h2 := a.2.isLt
  omega

private theorem slot_lt {n k : Nat} (a : Cell n) (l : Fin k) :
    cellCode a * k + l.val < n*n*k := by
  have h := Nat.mul_le_mul_right k (cell_lt a)
  rw [Nat.succ_mul] at h
  have h2 := l.isLt
  omega

private theorem row_inj {n a b c d : Nat} (hc : c < n) (hd : d < n)
    (h : a*n+c = b*n+d) : a = b ∧ c = d := by
  have eq : a = b := by
    apply Classical.byContradiction; intro neq
    rcases Nat.lt_or_gt_of_ne neq with hlt | hgt
    · have hh := Nat.mul_le_mul_right n hlt
      rw [Nat.succ_mul] at hh
      omega
    · have hh := Nat.mul_le_mul_right n hgt
      rw [Nat.succ_mul] at hh
      omega
  exact ⟨eq, by rw [eq] at h; omega⟩

theorem time_injective {n k : Nat} {v w : Vertex n k} (h : time v = time w) : v = w := by
  have cellInj (a b : Cell n) (h : cellCode a = cellCode b) : a = b := by
    obtain ⟨r,c⟩ := row_inj a.2.isLt b.2.isLt h
    exact Prod.ext (Fin.ext r) (Fin.ext c)
  cases v with
  | inl v =>
    obtain ⟨a,l⟩ := v
    cases w with
    | inl w =>
      obtain ⟨b,m⟩ := w
      obtain ⟨x,y⟩ := row_inj l.isLt m.isLt h
      rw [cellInj a b x, (Fin.ext y : l = m)]
    | inr b =>
      simp only [time] at h
      have h := slot_lt a l
      omega
  | inr a =>
    cases w with
    | inl w =>
      obtain ⟨b,m⟩ := w
      simp only [time] at h
      have h := slot_lt b m
      omega
    | inr b =>
      simp only [time] at h
      rw [cellInj a b (by omega)]

theorem time_rises {n k : Nat} (v w : Vertex n k) (l : Nat)
    (h : fixedEdge v w = some l) : time v < time w := by
  cases w with
  | inl _ => cases v <;> simp [fixedEdge] at h
  | inr b =>
    cases v with
    | inl v =>
      obtain ⟨a,g⟩ := v
      simp only [time]
      have h := slot_lt a g
      omega
    | inr a =>
      simp only [time,cellCode]
      by_cases e : east a b
      · rw [e.1]
        have p := e.2
        omega
      by_cases q : north a b
      · rw [q.2]
        have p := congrArg (· * n) q.1
        rw [Nat.add_mul] at p
        simp only [Nat.one_mul] at p
        have hn := a.1.isLt
        omega
      simp [fixedEdge,e,q] at h

theorem time_lt {n k : Nat} (v : Vertex n k) : time v < n*n*k+n*n := by
  cases v with
  | inl p =>
    have hh := slot_lt p.1 p.2
    change cellCode p.1*k+p.2.val < _
    omega
  | inr a =>
    have hh := cell_lt a
    change n*n*k + cellCode a < _
    omega

theorem no_edge_into_root {n k : Nat} (v : Vertex n k) (r : Cell n × Fin k) :
    fixedEdge v (.inl r) = none := by cases v <;> rfl

#print axioms time_injective
#print axioms time_rises
#print axioms time_lt
#print axioms fixedLabel
#print axioms grid_edge
#print axioms everyLabel
#print axioms gender_lt
#print axioms fixed_rank_rises
#print axioms fixed_children_covered
#print axioms fixed_preserves_words
end ResearchCommons.FixedGender
