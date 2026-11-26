import CappedConnectedBags

namespace ResearchCommons.GridMinorCross
open ResearchCommons.CappedConnectedBags

def Connected (A : Nat → Nat → Prop) (V : List Nat) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, WalkInside A V u v

def Linking (A : Nat → Nat → Prop) (U V : List Nat) : Prop :=
  ∃ u ∈ U, ∃ v ∈ V, A u v

private theorem appendWalk {A : Nat → Nat → Prop} {V : List Nat} {a b c : Nat}
    (w : WalkInside A V a b) (w' : WalkInside A V b c) : WalkInside A V a c := by
  induction w with
  | stay => exact w'
  | step ha e _ ih => exact .step ha e (ih w')

private theorem widen {A : Nat → Nat → Prop} {U V : List Nat} {a b : Nat}
    (sub : ∀ x ∈ U, x ∈ V) (w : WalkInside A U a b) : WalkInside A V a b := by
  induction w with
  | stay ha => exact .stay (sub _ ha)
  | step ha e _ ih => exact .step (sub _ ha) e ih

/-- A walk of branch sets can be lifted between arbitrary chosen end vertices. -/
theorem lift_walk {A G : Nat → Nat → Prop} {I : List Nat} {B : Nat → List Nat}
    {i j : Nat} (w : WalkInside G I i j) (conn : ∀ x ∈ I, Connected A (B x))
    (links : ∀ a b, G a b → Linking A (B a) (B b))
    (u v : Nat) (hu : u ∈ B i) (hv : v ∈ B j) :
    WalkInside A (I.flatMap B) u v := by
  induction w generalizing u with
  | stay hi =>
    exact widen (fun z hz => List.mem_flatMap.mpr ⟨_,hi,hz⟩) (conn _ hi u hu v hv)
  | @step a b c ha edge _ ih =>
    obtain ⟨x,hx,y,hy,e⟩ := links a b edge
    have localWalk := widen (V := I.flatMap B)
      (fun z hz => List.mem_flatMap.mpr ⟨a,ha,hz⟩) (conn a ha u hu x hx)
    exact appendWalk localWalk (.step (List.mem_flatMap.mpr ⟨a,ha,hx⟩) e (ih y hy hv))

/-- Vertices in the indexed union inherit connectivity of the index graph.
    Disjointness is not needed for this step. -/
theorem connected_union {A G : Nat → Nat → Prop} {I : List Nat} {B : Nat → List Nat}
    (connI : Connected G I) (connB : ∀ x ∈ I, Connected A (B x))
    (links : ∀ a b, G a b → Linking A (B a) (B b)) :
    Connected A (I.flatMap B) := by
  intro u hu v hv
  obtain ⟨i,hi,hu⟩ := List.mem_flatMap.mp hu
  obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hv
  exact lift_walk (connI i hi j hj) connB links u v hu hv

end ResearchCommons.GridMinorCross
#print axioms ResearchCommons.GridMinorCross.connected_union
