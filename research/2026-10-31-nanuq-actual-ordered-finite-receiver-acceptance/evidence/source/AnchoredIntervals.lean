import SyntaxFocus
import FrontierPartition

/-! UNCOMPILED anchored interval receiver. Its no-alternation input will be
DISCHARGED from the actual source, not added to the manuscript class. -/
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V R : Type*} [LinearOrder R]

/-- A hole in an anchored subtree produces four distinct ranks in the forbidden
second pattern. Empty/singleton sides are included: they cannot have two strict
endpoints of a hole. No claim that the reshaped subtree is an original directed
subtree is required. -/
theorem anchored_frontier_convex (v anchor : V) (rest : BinarySyntax V)
    (rank : V → R) (code : V → Nat)
    (hnd : (.fork v (.tip anchor) rest : BinarySyntax V).frontier.Nodup)
    (hfirst : ∀ x∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier,
      x≠anchor → rank anchor<rank x)
    (hno : ∀ a c d e,
      a∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier →
      c∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier →
      d∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier →
      e∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier →
      (encode code (.fork v (.tip anchor) rest)).Witness [] (code a) (code c) (code d) (code e) →
      ¬((rank a<rank d ∧ rank d<rank c ∧ rank c<rank e) ∨
        (rank d<rank a ∧ rank a<rank e ∧ rank e<rank c)))
    {u : BinarySyntax V} {out : List V} (hu : Context rest u out) :
    ∀ a∈u.frontier, ∀ c∈u.frontier,
      ∀ b∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier,
        rank a<rank b → rank b<rank c → b∈u.frontier := by
  intro a ha c hc b hb hab hbc
  by_contra hbu
  have hctx : Context (.fork v (.tip anchor) rest) u (out++[anchor]) :=
    .right v (.tip anchor) rest u out hu
  have hp := hctx.frontier_perm
  have hwhole (x : V) (hx : x∈u.frontier) :
      x∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier :=
    hp.mem_iff.mpr (List.mem_append_left _ hx)
  have hout (x : V) : x ∈ out++[anchor] ↔
      x ∈ (.fork v (.tip anchor) rest : BinarySyntax V).frontier ∧ x ∉ u.frontier := by
    have hnd' : (u.frontier ++ (out++[anchor])).Nodup := hp.nodup_iff.mp hnd
    have hd := (List.nodup_append.mp hnd').2.2
    constructor
    · intro hx
      exact ⟨hp.mem_iff.mpr (List.mem_append_right _ hx),fun hu => hd x hu x hx rfl⟩
    · rintro ⟨hx,hu⟩
      rcases List.mem_append.mp (hp.mem_iff.mp hx) with h | h
      · exact False.elim (hu h)
      · exact h
  have hbout : b∈out++[anchor] := (hout b).mpr ⟨hb,hbu⟩
  have hanchorout : anchor∈out++[anchor] := by simp
  have hanchoru : anchor∉u.frontier := ((hout anchor).mp hanchorout).2
  have hane : a≠anchor := by intro h; subst a; exact hanchoru ha
  have h0 := hfirst a (hwhole a ha) hane
  have haall : anchor∈(.fork v (.tip anchor) rest : BinarySyntax V).frontier :=
    ((hout anchor).mp hanchorout).1
  have hw : (encode code (.fork v (.tip anchor) rest)).Witness []
      (code a) (code c) (code anchor) (code b) := by
    apply (encode_witness_iff code _ [] _ _ _ _).mpr
    refine ⟨u,out++[anchor],hctx,Or.inl ⟨?_,?_,?_,?_⟩⟩
    · exact List.mem_map.mpr ⟨a,ha,rfl⟩
    · exact List.mem_map.mpr ⟨c,hc,rfl⟩
    · exact List.mem_append_left [] (List.mem_map.mpr ⟨anchor,hanchorout,rfl⟩)
    · exact List.mem_append_left [] (List.mem_map.mpr ⟨b,hbout,rfl⟩)
  exact hno a c anchor b (hwhole a ha) (hwhole c hc) haall hb hw
    (Or.inr ⟨h0,hab,hbc⟩)

#print axioms anchored_frontier_convex
end Nanuq.GraphReceiver
