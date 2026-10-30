import OrderedCertificate

set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

structure Quartet where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq, Repr

def Quartet.labels (q : Quartet) : List Nat := [q.a,q.b,q.c,q.d]

def quartets (n : Nat) : List Quartet :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
  (List.range n).flatMap fun c => (List.range n).flatMap fun d =>
    if a < b ∧ b < c ∧ c < d then [⟨a,b,c,d⟩] else []

/-- Each mask bit duplicates its taxon in place, never interleaves labels. -/
def occurrenceLabels (n mask : Nat) : List Nat :=
  (List.range n).flatMap fun x => if mask.testBit x then [x,x] else [x]

def Quartet.side (q : Quartet) (r : Nat) (x : Nat) : Bool :=
  if r = 0 then x == q.a || x == q.b
  else if r = 1 then x == q.a || x == q.c
  else x == q.a || x == q.d

def Quartet.parts (q : Quartet) (r : Nat) : Nat × Nat × Nat × Nat :=
  if r = 0 then (q.a,q.b,q.c,q.d)
  else if r = 1 then (q.a,q.c,q.b,q.d)
  else (q.a,q.d,q.b,q.c)

def edgeWitness (tips : List Nat) (lo len : Nat) (q : Quartet) (r : Nat) : Bool :=
  let left := (tips.drop lo).take len
  let right := tips.take lo ++ tips.drop (lo+len)
  let (a,b,c,d) := q.parts r
  (left.contains a && left.contains b && right.contains c && right.contains d) ||
  (right.contains a && right.contains b && left.contains c && left.contains d)

/-- Exactly the OR of physical occurrence edge witnesses; all three
resolutions are retained here, rather than presupposing noncrossing. -/
def edgeContribution (tips : List Nat) (qs : List Quartet) (lo len : Nat) : Nat :=
  (qs.zipIdx).foldl (fun acc qi =>
    (List.range 3).foldl (fun acc r =>
      if edgeWitness tips lo len qi.1 r then acc ||| (1 <<< (3*qi.2+r)) else acc) acc) 0

def quartetIndex (qs : List Quartet) (x y p q : Nat) : Nat :=
  qs.findIdx (fun Q => [x,y,p,q].all (fun z => Q.labels.contains z))

def quartetAt (qs : List Quartet) (x y p q : Nat) : Quartet :=
  qs[quartetIndex qs x y p q]?.getD ⟨0,0,0,0⟩

def code (pattern qi : Nat) : Nat := (pattern >>> (3*qi)) % 8

def displayedPair (qs : List Quartet) (pattern x y p q : Nat) : Bool :=
  let qi := quartetIndex qs x y p q
  let Q := quartetAt qs x y p q
  (List.range 3).any (fun r => (code pattern qi).testBit r && (Q.side r x == Q.side r y))

/-- Twice the exact uniform DISTINCT-resolution separation mean.
The certificate separately proves codes are1,4,5, hence this integer
quotient loses no fractional part (two times a half-integer mean). -/
def twiceMean (qs : List Quartet) (pattern x y p q : Nat) : Nat :=
  let qi := quartetIndex qs x y p q
  let Q := quartetAt qs x y p q
  let present := (List.range 3).filter (fun r => (code pattern qi).testBit r)
  2 * (present.filter (fun r => Q.side r x != Q.side r y)).length / present.length

def anchor (qs : List Quartet) (pattern p q x y : Nat) : Int :=
  if x = y ∨ (x = p ∧ y = q) ∨ (x = q ∧ y = p) then 0
  else if x = p ∨ x = q ∨ y = p ∨ y = q then 1
  else Int.ofNat (twiceMean qs pattern x y p q)

def alpha (n : Nat) (qs : List Quartet) (pattern p q i j : Nat) : Int :=
  let a := i
  let b := (i+1)%n
  let c := j
  let d := (j+1)%n
  anchor qs pattern p q a c + anchor qs pattern p q b d -
    anchor qs pattern p q a d - anchor qs pattern p q b c

def checkPattern (n : Nat) (qs : List Quartet) (pattern : Nat) : Bool :=
  (List.range qs.length).all (fun qi => [1,4,5].contains (code pattern qi)) &&
  (List.range n).all (fun p => (List.range n).all (fun q => if p < q then
    (List.range n).all (fun i => (List.range n).all (fun j => if i < j then
      decide (0 ≤ alpha n qs pattern p q i j) &&
      (if i+1 < j ∧ ¬(i=0 ∧ j+1=n) then
        if displayedPair qs pattern ((i+1)%n) j i ((j+1)%n) then true
        else decide (alpha n qs pattern p q i j = 0)
      else true)
    else true))
  else true))

def tableFrom (m : Nat) (data : List (List Nat)) : Table :=
  fun lo len => data[lo*(m+1)+len]?.getD []

end Nanuq.AdjacentCertificate

namespace Nanuq.AdjacentCertificate

theorem nonneg_of_check (n : Nat) (qs : List Quartet) (pattern : Nat)
    (h : checkPattern n qs pattern = true) (p q i j : Nat)
    (hp : p < n) (hq : q < n) (hi : i < n) (hj : j < n)
    (hpq : p < q) (hij : i < j) : 0 ≤ alpha n qs pattern p q i j := by
  simp only [checkPattern, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.2 p (List.mem_range.mpr hp) q (List.mem_range.mpr hq)
  simp only [if_pos hpq, List.all_eq_true] at h1
  have h2 := h1 i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
  simp only [if_pos hij, Bool.and_eq_true] at h2
  exact of_decide_eq_true h2.1

theorem absent_zero_of_check (n : Nat) (qs : List Quartet) (pattern : Nat)
    (h : checkPattern n qs pattern = true) (p q i j : Nat)
    (hp : p < n) (hq : q < n) (hi : i < n) (hj : j < n)
    (hpq : p < q) (hij : i < j)
    (nonadj : i+1 < j ∧ ¬(i=0 ∧ j+1=n))
    (absent : displayedPair qs pattern ((i+1)%n) j i ((j+1)%n) = false) :
    alpha n qs pattern p q i j = 0 := by
  simp only [checkPattern, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.2 p (List.mem_range.mpr hp) q (List.mem_range.mpr hq)
  simp only [if_pos hpq, List.all_eq_true] at h1
  have h2 := h1 i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
  simp only [if_pos hij, Bool.and_eq_true] at h2
  have hz := h2.2
  simp only [if_pos nonadj, absent, Bool.false_eq_true, if_false] at hz
  exact of_decide_eq_true hz

theorem code_valid_of_check (n : Nat) (qs : List Quartet) (pattern : Nat)
    (h : checkPattern n qs pattern = true) (qi : Nat) (hqi : qi < qs.length) :
    code pattern qi ∈ ([1,4,5] : List Nat) := by
  simp only [checkPattern, Bool.and_eq_true] at h
  have hh := List.all_eq_true.mp h.1 qi (List.mem_range.mpr hqi)
  exact of_decide_eq_true (by simpa only [List.contains_eq_mem] using hh)

#print axioms nonneg_of_check
#print axioms absent_zero_of_check
#print axioms code_valid_of_check
end Nanuq.AdjacentCertificate
