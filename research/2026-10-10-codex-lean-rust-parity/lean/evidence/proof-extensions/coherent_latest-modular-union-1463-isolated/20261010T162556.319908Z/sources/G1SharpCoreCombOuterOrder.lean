import G1SharpCoreCombReduced

/-! An explicit outer circular order of EVERY original vertex. Interleaved
bridge subtrees are nested between HR and U; all original edge intervals
are laminar. This is the combinatorial input to an actual convex drawing. -/
namespace G1SharpCoreCombOuterOrder
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombAdmission
open scoped Classical

def outerIndex (n : Nat) : Vertex n → Nat
  | .inl (i,k) => match k.val with
    | 0 => 5*i.val
    | 1 => 6*(n-1)-i.val
    | 2 => 5*i.val+3
    | 3 => 5*i.val+1
    | _ => 5*i.val+4
  | .inr x => if x.val < n-1 then 5*x.val+2 else 5*(n-1)

theorem outerIndex_injective (n : Nat) (hn : 4 ≤ n) : Function.Injective (outerIndex n) := by
  intro a b hab
  cases a with
  | inl p =>
    rcases p with ⟨i,k⟩
    cases b with
    | inl q =>
      rcases q with ⟨j,l⟩
      have hi := i.isLt
      have hj := j.isLt
      fin_cases k <;> fin_cases l
      all_goals simp only [outerIndex] at hab
      all_goals simp only [Sum.inl.injEq,Prod.mk.injEq,Fin.ext_iff]
      all_goals norm_num at hab ⊢
      all_goals omega
    | inr x =>
      have hi := i.isLt
      have hx := x.isLt
      fin_cases k
      all_goals simp only [outerIndex] at hab
      all_goals split_ifs at hab <;> norm_num at hab ⊢ <;> omega
  | inr x =>
    have hx := x.isLt
    cases b with
    | inl q =>
      rcases q with ⟨j,l⟩
      have hj := j.isLt
      fin_cases l
      all_goals simp only [outerIndex] at hab
      all_goals split_ifs at hab <;> norm_num at hab ⊢ <;> omega
    | inr y =>
      have hy := y.isLt
      simp only [outerIndex] at hab
      simp only [Sum.inr.injEq,Fin.ext_iff]
      split_ifs at hab <;> norm_num at hab ⊢ <;> omega

def edgeLower (n : Nat) (e : Edge n) : Nat :=
  match e.2.val with
  | 0 => 5*e.1.val
  | 1 => 5*e.1.val
  | 2 => 5*e.1.val+4
  | 3 => 5*e.1.val+3
  | 4 => 5*e.1.val+1
  | 5 => 5*e.1.val+3
  | 6 => 5*e.1.val+1
  | _ => 5*e.1.val+4

def edgeUpper (n : Nat) (e : Edge n) : Nat :=
  match e.2.val with
  | 0 => 5*e.1.val+1
  | 1 => 6*(n-1)-e.1.val
  | 2 => 6*(n-1)-e.1.val
  | 3 => 6*(n-1)-e.1.val
  | 4 => 5*e.1.val+3
  | 5 => 5*e.1.val+4
  | 6 => 5*e.1.val+2
  | _ => 5*e.1.val+5

theorem original_endpoints_in_outer_order (n : Nat) (hn : 4 ≤ n) (e : Edge n) :
    (outerIndex n ((graph n).source e) = edgeLower n e ∧ outerIndex n ((graph n).target e) = edgeUpper n e) ∨
    (outerIndex n ((graph n).source e) = edgeUpper n e ∧ outerIndex n ((graph n).target e) = edgeLower n e) := by
  rcases e with ⟨i,k⟩
  have hi := i.isLt
  fin_cases k
  all_goals simp [graph,source,target,localSource,outerIndex,edgeLower,edgeUpper]
  all_goals split_ifs <;> norm_num [outerIndex] <;> omega
  all_goals omega

theorem original_interval_strict (n : Nat) (hn : 4 ≤ n) (e : Edge n) :
    edgeLower n e < edgeUpper n e := by
  rcases e with ⟨i,k⟩
  have hi := i.isLt
  fin_cases k <;> simp only [edgeLower,edgeUpper] <;> norm_num at * <;> omega

theorem original_intervals_laminar (n : Nat) (hn : 4 ≤ n) (e f : Edge n) :
    edgeUpper n e ≤ edgeLower n f ∨ edgeUpper n f ≤ edgeLower n e ∨
    (edgeLower n e ≤ edgeLower n f ∧ edgeUpper n f ≤ edgeUpper n e) ∨
    (edgeLower n f ≤ edgeLower n e ∧ edgeUpper n e ≤ edgeUpper n f) := by
  rcases e with ⟨i,k⟩
  rcases f with ⟨j,l⟩
  have hi := i.isLt
  have hj := j.isLt
  fin_cases k <;> fin_cases l <;> simp only [edgeLower,edgeUpper] <;> norm_num at * <;> omega

theorem original_interval_identity (n : Nat) (hn : 4 ≤ n) (e f : Edge n)
    (hlo : edgeLower n e = edgeLower n f) (hhi : edgeUpper n e = edgeUpper n f) : e = f := by
  rcases e with ⟨i,k⟩
  rcases f with ⟨j,l⟩
  have hi := i.isLt
  have hj := j.isLt
  fin_cases k <;> fin_cases l
  all_goals simp only [edgeLower,edgeUpper] at hlo hhi
  all_goals simp only [Prod.mk.injEq,Fin.ext_iff]
  all_goals norm_num at *
  all_goals omega

#print axioms outerIndex_injective
#print axioms original_intervals_laminar
end G1SharpCoreCombOuterOrder
