import Std

set_option warningAsError true

namespace ResearchCommons.NanuqOmnibusFixture

inductive Taxon | a | b | c | d | x
deriving DecidableEq, Repr
open Taxon

def taxa : List Taxon := [a,b,c,d,x]

/-- Physical tips sit on a five-vertex, unit-edge backbone. All pendant edges
also have unit length. The three copies of x attach at backbone positions 0,2,4. -/
def pos (xpos : Nat) : Taxon → Nat
  | a => 0 | b => 4 | c => 1 | d => 3 | x => xpos

def dist (xpos : Nat) (i j : Taxon) : Nat :=
  let u := pos xpos i
  let v := pos xpos j
  max u v - min u v + 2

abbrev Quartet := Taxon × Taxon × Taxon × Taxon

def quartets : List Quartet :=
  [(a,b,c,d),(a,b,c,x),(a,b,d,x),(a,c,d,x),(b,c,d,x)]

/-- The minimum four-point sum is the pairing on a resolved quartet.
Indices 0,1,2 mean ab|cd, ac|bd, ad|bc in the supplied tuple. -/
def quartetType (xpos : Nat) : Quartet → Option Nat
  | (i,j,k,l) =>
    let s0 := dist xpos i j + dist xpos k l
    let s1 := dist xpos i k + dist xpos j l
    let s2 := dist xpos i l + dist xpos j k
    if s0 < s1 && s0 < s2 then some 0
    else if s1 < s0 && s1 < s2 then some 1
    else if s2 < s0 && s2 < s1 then some 2 else none

def support (positions : List Nat) (q : Quartet) : List Nat :=
  [0,1,2].filter fun i => positions.any fun s => quartetType s q == some i

def observable (positions : List Nat) : List (List Nat) :=
  quartets.map (support positions)

def bit : Taxon → Nat
  | a => 1 | b => 2 | c => 4 | d => 8 | x => 16

/-- Compute each nontrivial split by cutting one physical backbone edge.
Pendant cuts are trivial. Complement identifies the two sides of a split. -/
def splitAt (xpos cut : Nat) : Option Nat :=
  let left := taxa.filter (fun t => pos xpos t ≤ cut)
  let mask := (left.map bit).sum
  if 2 ≤ left.length && left.length ≤ 3 then some (min mask (31 - mask)) else none

def splits (xpos : Nat) : List Nat := ((List.range 4).filterMap (splitAt xpos)).eraseDups

def original : List Nat := [0,2,4]
def reduced : List Nat := [0,4]

/-- 5 = ac|bdx and 10 = acx|bd, both in the same displayed tree. -/
def joint (positions : List Nat) : Bool :=
  positions.any fun t => (splits t).contains 5 && (splits t).contains 10

theorem exact_observable :
    observable original = [[1],[1,2],[1,2],[0,2],[1,2]] ∧
    observable reduced = observable original := by decide

theorem exact_nontrivial_splits :
    splits 0 = [14,10] ∧ splits 2 = [5,10] ∧ splits 4 = [5,13] := by decide

theorem same_obs_different_joint :
    observable original = observable reduced ∧ joint original = true ∧ joint reduced = false := by decide

theorem copy_uniform_counts_differ :
    (original.filter (fun t => quartetType t (a,b,c,x) == some 1)).length = 2 ∧
    (reduced.filter (fun t => quartetType t (a,b,c,x) == some 1)).length = 1 := by decide

#print axioms same_obs_different_joint
#print axioms copy_uniform_counts_differ
end ResearchCommons.NanuqOmnibusFixture
