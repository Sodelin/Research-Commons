import PresentedCappedHost
open ResearchCommons.PresentedCappedHost

private def forward (a b : Bool) : Option Nat :=
  if !a && b then some 0 else none
private def reverseRelabel (a b : Bool) : Option Nat :=
  if a && !b then some 7 else none

/-- Identity keeps undirected adjacency even though the only edge flips and relabels. -/
theorem permits_reversal_and_relabeling : Embeds forward reverseRelabel := by
  refine ⟨id,fun a b h => h,?_⟩
  intro a b h
  cases a <;> cases b <;> simp_all [forward,reverseRelabel]

example : forward false true = some 0 ∧ reverseRelabel false true = none ∧
    reverseRelabel true false = some 7 := by decide

#print axioms permits_reversal_and_relabeling
