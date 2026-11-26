import TwoLiftTriangle
set_option warningAsError true

namespace ResearchCommons.TriangleRun
open TwoLiftTriangle

def InTriple (n : Nat) (sheet : Bool) (v : Vertex) : Prop :=
  v.2 = sheet ∧ n ≤ v.1 ∧ v.1 ≤ n+2

def At (twist : Nat → Bool) (keep : Vertex → Prop) (u v : Vertex) : Prop :=
  u ≠ v ∧ ∃ n sheet, 0 < n ∧ twist n = false ∧
    InTriple n sheet u ∧ InTriple n sheet v ∧
    keep (n,sheet) ∧ keep (n+1,sheet) ∧ keep (n+2,sheet)

def InBand (lo hi : Nat) (sheet : Bool) (v : Vertex) : Prop :=
  v.2 = sheet ∧ lo ≤ v.1 ∧ v.1 ≤ hi

inductive Reach (E : Vertex → Vertex → Prop) (s : Vertex) : Vertex → Prop
  | here : Reach E s s
  | next {u v} : Reach E s u → E u v → Reach E s v

/-- Pin the interval model to the actual sorted triangles of the two-sheet graph. -/
theorem triple_iff (twist : Nat → Bool) (n : Nat) (b : Bool) :
    (Up twist (n,b) (n+1,b) ∧ Up twist (n+1,b) (n+2,b) ∧
      Up twist (n,b) (n+2,b)) ↔ 0 < n ∧ twist n = false := by
  simpa using TwoLiftTriangle.triangle_iff twist (n,b) (n+1,b) (n+2,b)

def GraphTriangleEdge (twist : Nat → Bool) (keep : Vertex → Prop)
    (u v : Vertex) : Prop :=
  u ≠ v ∧ ∃ a c d : Vertex,
    Up twist a c ∧ Up twist c d ∧ Up twist a d ∧
    u ∈ [a,c,d] ∧ v ∈ [a,c,d] ∧ keep a ∧ keep c ∧ keep d

private theorem inTriple_iff_mem (n : Nat) (b : Bool) (u : Vertex) :
    InTriple n b u ↔ u ∈ [(n,b),(n+1,b),(n+2,b)] := by
  rcases u with ⟨m,c⟩
  simp only [InTriple, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl,h1,h2⟩
    have : m = n ∨ m = n+1 ∨ m = n+2 := by omega
    rcases this with rfl | rfl | rfl <;> simp
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp <;> omega

theorem at_iff_actual (twist : Nat → Bool) (keep : Vertex → Prop) (u v : Vertex) :
    At twist keep u v ↔ GraphTriangleEdge twist keep u v := by
  constructor
  · rintro ⟨ne,n,b,h,z,hu,hv,h0,h1,h2⟩
    obtain ⟨ac,cd,ad⟩ := (triple_iff twist n b).mpr ⟨h,z⟩
    exact ⟨ne,(n,b),(n+1,b),(n+2,b),ac,cd,ad,
      (inTriple_iff_mem _ _ _).mp hu,(inTriple_iff_mem _ _ _).mp hv,h0,h1,h2⟩
  · rintro ⟨ne,a,c,d,ac,cd,ad,hu,hv,ha,hc,hd⟩
    obtain ⟨h,c1,d1,c2,d2,z⟩ := (TwoLiftTriangle.triangle_iff twist a c d).mp ⟨ac,cd,ad⟩
    have ec : c = (a.1+1,a.2) := Prod.ext c1 c2
    have ed : d = (a.1+2,a.2) := Prod.ext (by omega) (d2.trans c2)
    subst c; subst d
    exact ⟨ne,a.1,a.2,h,z,(inTriple_iff_mem _ _ _).mpr hu,
      (inTriple_iff_mem _ _ _).mpr hv,ha,hc,hd⟩

theorem local_survival {twist : Nat → Bool} {keep : Vertex → Prop} {D : Nat}
    (after : ∀ v : Vertex, D < v.1 → keep v)
    {u v : Vertex} (late : D+2 < u.1)
    (h : At twist (fun _ => True) u v) : At twist keep u v := by
  obtain ⟨ne,n,b,pos,z,hu,hv,_,_,_⟩ := h
  have hn : D < n := by have := hu.2.2; omega
  exact ⟨ne,n,b,pos,z,hu,hv,after _ hn,after _ (by change D < n+1; omega),
    after _ (by change D < n+2; omega)⟩

theorem reach_mono {E F : Vertex → Vertex → Prop} (h : ∀ u v, E u v → F u v)
    {s v : Vertex} (r : Reach E s v) : Reach F s v := by
  induction r with
  | here => exact .here
  | next _ e ih => exact .next ih (h _ _ e)

/-- A component wholly above the two-level margin did not acquire a new
boundary from deletion. No global theorem about finite edits is needed. -/
theorem late_component_iff {twist : Nat → Bool} {keep : Vertex → Prop} {D : Nat}
    (after : ∀ v : Vertex, D < v.1 → keep v) {s : Vertex}
    (late : ∀ v, Reach (At twist keep) s v → D+2 < v.1) (v : Vertex) :
    Reach (At twist keep) s v ↔ Reach (At twist (fun _ => True)) s v := by
  constructor
  · apply reach_mono
    intro u w h
    obtain ⟨ne,n,b,pos,z,hu,hw,_,_,_⟩ := h
    exact ⟨ne,n,b,pos,z,hu,hw,trivial,trivial,trivial⟩
  · intro h
    induction h with
    | here => exact .here
    | next _ e ih => exact .next ih (local_survival after (late _ ih) e)

/-- A run with two separating ones at either end has exactly its same-sheet
interval as a component; arbitrary deletions below the run do not affect it. -/
theorem run_component {twist : Nat → Bool} {keep : Vertex → Prop} {lo hi : Nat}
    (positive : 0 < lo) (order : lo ≤ hi)
    (zero : ∀ n, lo ≤ n → n ≤ hi → twist n = false)
    (separate : ∀ n, 0 < n → lo ≤ n+2 → n ≤ hi+2 →
        (n < lo ∨ hi < n) → twist n = true)
    (survives : ∀ v : Vertex, lo ≤ v.1 → keep v)
    (b : Bool) (v : Vertex) :
    Reach (At twist keep) (lo,b) v ↔ InBand lo (hi+2) b v := by
  constructor
  · intro reach
    induction reach with
    | here => exact ⟨rfl,Nat.le_refl _,by omega⟩
    | @next u w _ edge ih =>
      obtain ⟨_,n,c,hn,hz,hu,hw,_,_,_⟩ := edge
      obtain ⟨sb,ulo,uhi⟩ := ih
      have high : n ≤ hi+2 := Nat.le_trans hu.2.1 uhi
      have low : lo ≤ n+2 := Nat.le_trans ulo hu.2.2
      have inrange : lo ≤ n ∧ n ≤ hi := by
        by_cases h : n < lo ∨ hi < n
        · rw [separate n hn low high h] at hz
          cases hz
        · omega
      exact ⟨hw.1.trans (hu.1.symm.trans sb),Nat.le_trans inrange.1 hw.2.1,by have := hw.2.2; omega⟩
  · rintro ⟨same,hlo,hhi⟩
    have step (m : Nat) (hm : lo ≤ m) (hn : m+1 ≤ hi+2) :
        At twist keep (m,b) (m+1,b) := by
      let n := min m hi
      have a : lo ≤ n := Nat.le_min.mpr ⟨hm,order⟩
      have c : n ≤ hi := Nat.min_le_right _ _
      have nm : n ≤ m := Nat.min_le_left _ _
      have hclose : m+1 ≤ n+2 := by
        by_cases h : m ≤ hi
        · dsimp [n]; rw [Nat.min_eq_left h]; omega
        · dsimp [n]; rw [Nat.min_eq_right (by omega)]; omega
      exact ⟨by intro e; have := congrArg Prod.fst e; simp at this,n,b,by omega,zero n a c,
        ⟨rfl,nm,by omega⟩,⟨rfl,by omega,hclose⟩,
        survives _ a,survives _ (by change lo ≤ n+1; omega),
        survives _ (by change lo ≤ n+2; omega)⟩
    have every (m : Nat) (bound : lo+m ≤ hi+2) :
        Reach (At twist keep) (lo,b) (lo+m,b) := by
      induction m with
      | zero => exact .here
      | succ m ih => exact .next (ih (by omega)) (step _ (by omega) bound)
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hlo
    have ev : v = (lo+j,b) := Prod.ext hj same
    rw [ev]
    exact every j (by omega)

def runVertices (lo hi : Nat) (b : Bool) : List Vertex :=
  (List.range (hi+3-lo)).map fun j => (lo+j,b)

theorem run_vertices_exact (lo hi : Nat) (b : Bool) (v : Vertex) :
    v ∈ runVertices lo hi b ↔ InBand lo (hi+2) b v := by
  constructor
  · intro h
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    have hb := List.mem_range.mp hj
    exact ⟨rfl,by omega,by omega⟩
  · rintro ⟨hb,hl,hr⟩
    obtain ⟨j,e⟩ := Nat.exists_eq_add_of_le hl
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),Prod.ext e.symm hb.symm⟩

theorem run_size (lo hi : Nat) (b : Bool) : (runVertices lo hi b).length = hi+3-lo := by
  simp [runVertices]

theorem run_nodup (lo hi : Nat) (b : Bool) : (runVertices lo hi b).Nodup := by
  exact List.Pairwise.map _ (fun a c ne h => ne (by
    have eq := congrArg Prod.fst h
    simp only at eq
    omega)) List.nodup_range

/-- Actual triangle-edge component of a run of m+1 zeros: m+3 distinct
vertices. The retained graph may lose arbitrary vertices below the run. -/
theorem exact_component {twist : Nat → Bool} {keep : Vertex → Prop}
    (lo m : Nat) (positive : 0 < lo)
    (zero : ∀ n, lo ≤ n → n ≤ lo+m → twist n = false)
    (separate : ∀ n, 0 < n → lo ≤ n+2 → n ≤ lo+m+2 →
      (n < lo ∨ lo+m < n) → twist n = true)
    (survives : ∀ v : Vertex, lo ≤ v.1 → keep v)
    (b : Bool) :
    let vs := runVertices lo (lo+m) b
    vs.Nodup ∧ vs.length = (m+1)+2 ∧
      ∀ v, Reach (GraphTriangleEdge twist keep) (lo,b) v ↔ v ∈ vs := by
  refine ⟨run_nodup _ _ _, by rw [run_size]; omega, fun v => ?_⟩
  have eq : Reach (GraphTriangleEdge twist keep) (lo,b) v ↔
      Reach (At twist keep) (lo,b) v :=
    ⟨reach_mono (fun u w => (at_iff_actual twist keep u w).mpr),
      reach_mono (fun u w => (at_iff_actual twist keep u w).mp)⟩
  exact eq.trans ((run_component positive (by omega) zero separate survives b v).trans
    (run_vertices_exact _ _ _ _).symm)

private def oneGap (n : Nat) : Bool := !(n == 1 || n == 3)

/-- One intervening switch is not enough: the two triples share (3,false). -/
theorem one_gap_connects :
    Reach (GraphTriangleEdge oneGap (fun _ => True)) (1,false) (5,false) := by
  have e₁ : At oneGap (fun _ => True) (1,false) (3,false) :=
    ⟨by decide,1,false,by decide,by decide,by simp [InTriple],by simp [InTriple],trivial,trivial,trivial⟩
  have e₂ : At oneGap (fun _ => True) (3,false) (5,false) :=
    ⟨by decide,3,false,by decide,by decide,by simp [InTriple],by simp [InTriple],trivial,trivial,trivial⟩
  exact .next (.next .here ((at_iff_actual _ _ _ _).mp e₁)) ((at_iff_actual _ _ _ _).mp e₂)

#print axioms triple_iff
#print axioms at_iff_actual
#print axioms late_component_iff
#print axioms run_component
#print axioms run_vertices_exact
#print axioms run_nodup
#print axioms exact_component
#print axioms one_gap_connects
end ResearchCommons.TriangleRun
