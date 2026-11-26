import Std

namespace ResearchCommons.FiniteBallDiagonal

/-- Adjacency lists are finite. Repeating the current vertices gives closed
balls, including for graphs without loops. -/
def ball (N : Nat → List Nat) (root : Nat) : Nat → List Nat
  | 0 => [root]
  | r+1 => (ball N root r) ++ (ball N root r).flatMap N

def envelope (N : Nat → Nat → List Nat) (stage radius : Nat) : List Nat :=
  (List.range (stage+1)).flatMap (fun j =>
    (List.range (stage+1)).flatMap (fun root => ball (N j) root radius))

theorem ball_mem_envelope {N : Nat → Nat → List Nat} {j root stage r x : Nat}
    (hj : j ≤ stage) (hr : root ≤ stage) (hx : x ∈ ball (N j) root r) :
    x ∈ envelope N stage r :=
  List.mem_flatMap.mpr ⟨j,List.mem_range.mpr (by omega),
    List.mem_flatMap.mpr ⟨root,List.mem_range.mpr (by omega),hx⟩⟩

private theorem length_le_of_nodup_subset (a b : List Nat)
    (ha : a.Nodup) (sub : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons u us ih =>
    obtain ⟨hmiss,hnd⟩ := List.nodup_cons.mp ha
    have hb : u ∈ b := sub u (by simp)
    have rest := ih (b.erase u) hnd (by
      intro v hv
      have ne : v ≠ u := by rintro rfl; exact hmiss hv
      exact (List.mem_erase_of_ne ne).mpr (sub v (List.mem_cons_of_mem _ hv)))
    rw [List.length_erase_of_mem hb] at rest
    have pos : 0 < b.length := by
      cases b with
      | nil => simp at hb
      | cons _ _ => simp
    simp only [List.length_cons]
    omega

/-- At equal finite degree, an injective adjacency-preserving map cannot
omit any host neighbor. This is the local step in cofinite tail saturation. -/
theorem saturation_of_equal_neighbor_count (N H : Nat → List Nat)
    (map : Nat → Nat) (inj : ∀ a b, map a = map b → a = b)
    (u : Nat) (src : (N u).Nodup)
    (adj : ∀ v ∈ N u, map v ∈ H (map u))
    (same : (N u).length = (H (map u)).length) :
    ∀ w ∈ H (map u), ∃ v ∈ N u, map v = w := by
  classical
  intro w hw
  apply Classical.byContradiction
  intro h
  have nd : ((N u).map map).Nodup :=
    List.Pairwise.map map (fun _ _ neq e => neq (inj _ _ e)) src
  have le := length_le_of_nodup_subset ((N u).map map) ((H (map u)).erase w) nd (by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    have hn : map v ≠ w := fun he => h ⟨v,hv,he⟩
    exact (List.mem_erase_of_ne hn).mpr (adj v hv))
  rw [List.length_erase_of_mem hw] at le
  simp only [List.length_map] at le
  have pos : 0 < (H (map u)).length := by
    cases hl : H (map u) with
    | nil => simp [hl] at hw
    | cons _ _ => simp
  omega

private theorem reject_stage {V : Type} (f : V → Nat)
    (inj : ∀ a b, f a = f b → a = b) (tips : List V) (nd : tips.Nodup)
    (target : List Nat) (large : target.length < tips.length)
    (capture : ∀ x ∈ tips, f x ∈ target) : False := by
  have mapnd : (tips.map f).Nodup :=
    List.Pairwise.map f (fun _ _ h eq => h (inj _ _ eq)) nd
  have bound := length_le_of_nodup_subset (tips.map f) target mapnd (by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact capture v hv)
  simp at bound
  omega

/-- For every candidate host, every image of the common anchor, and every
uniform integer stretch, there is one finite witness stage that defeats it.
The caller provides the source radius and the path-to-ball transfer. -/
theorem no_uniform_stretch_into_portfolio {V : Type}
    (N : Nat → Nat → List Nat) (sourceRadius : Nat → Nat) (tips : Nat → List V)
    (nd : ∀ stage, (tips stage).Nodup)
    (large : ∀ stage,
      (envelope N stage (stage * sourceRadius stage)).length < (tips stage).length)
    (f : V → Nat) (inj : ∀ a b, f a = f b → a = b)
    (host root stretch : Nat)
    (capture : ∀ stage, stretch ≤ stage → ∀ v ∈ tips stage,
      f v ∈ ball (N host) root (stage * sourceRadius stage)) : False := by
  let stage := max host (max root stretch)
  have hh : host ≤ stage := Nat.le_max_left _ _
  have hr : root ≤ stage := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hs : stretch ≤ stage := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact reject_stage f inj (tips stage) (nd stage) _ (large stage)
    (fun x hx => ball_mem_envelope hh hr (capture stage hs x hx))

theorem ball_append {N : Nat → List Nat} {u v w a b : Nat}
    (hv : v ∈ ball N u a) (hw : w ∈ ball N v b) :
    w ∈ ball N u (a+b) := by
  induction b generalizing w with
  | zero =>
    have e : w = v := List.mem_singleton.mp hw
    simpa only [e, Nat.add_zero] using hv
  | succ b ih =>
    change w ∈ ball N v b ++ (ball N v b).flatMap N at hw
    change w ∈ ball N u (a+b) ++ (ball N u (a+b)).flatMap N
    rcases List.mem_append.mp hw with h | h
    · exact List.mem_append.mpr (Or.inl (ih h))
    · obtain ⟨x,hx,he⟩ := List.mem_flatMap.mp h
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨x,ih hx,he⟩))

theorem ball_mono {N : Nat → List Nat} {u w a b : Nat} (le : a ≤ b)
    (h : w ∈ ball N u a) : w ∈ ball N u b := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction c with
  | zero => simpa using h
  | succ c ih => exact List.mem_append.mpr (Or.inl ih)

theorem map_ball {source target : Nat → List Nat} {f : Nat → Nat}
    {L : Nat} (edge : ∀ u v, v ∈ source u → f v ∈ ball target (f u) L)
    {u v d : Nat} (h : v ∈ ball source u d) :
    f v ∈ ball target (f u) (L*d) := by
  induction d generalizing v with
  | zero =>
    have e : v = u := List.mem_singleton.mp h
    simp [e,ball]
  | succ d ih =>
    rw [Nat.mul_succ]
    change v ∈ ball source u d ++ (ball source u d).flatMap source at h
    rcases List.mem_append.mp h with ha | ha
    · exact ball_mono (Nat.le_add_right _ _) (ih ha)
    · obtain ⟨x,hx,hstep⟩ := List.mem_flatMap.mp ha
      exact ball_append (ih hx) (edge _ _ hstep)

/-- This form consumes source reachability and local stretch, not a supplied
whole-map ball capture premise. The countable addition construction is separate. -/
theorem no_portfolio_map_of_large_source_balls
    (source : Nat → List Nat) (anchor : Nat) (N : Nat → Nat → List Nat)
    (radius : Nat → Nat) (tips : Nat → List Nat)
    (nd : ∀ n, (tips n).Nodup)
    (contained : ∀ n v, v ∈ tips n → v ∈ ball source anchor (radius n))
    (large : ∀ n, (envelope N n (n * radius n)).length < (tips n).length)
    (f : Nat → Nat) (inj : ∀ a b, f a = f b → a = b) (host L : Nat)
    (edge : ∀ u v, v ∈ source u → f v ∈ ball (N host) (f u) L) :
    False := by
  apply no_uniform_stretch_into_portfolio N radius tips nd large f inj host (f anchor) L
  intro stage hle v hv
  exact ball_mono (Nat.mul_le_mul_right (radius stage) hle)
    (map_ball edge (contained stage v hv))

#print axioms saturation_of_equal_neighbor_count
#print axioms no_uniform_stretch_into_portfolio
#print axioms no_portfolio_map_of_large_source_balls
end ResearchCommons.FiniteBallDiagonal
