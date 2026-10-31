import ConvexSeparation

/-! UNCOMPILED sorting of actual occurrence sets by DERIVED interval order.
Child swaps preserve witnesses with every outside context and every label map. -/
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V R : Type*} [LinearOrder R]

theorem witness_fork_right_congr (l r r' : LTree)
    (hleaves : ∀ x, x∈r.leaves ↔ x∈r'.leaves)
    (hw : ∀ out a b c d, r.Witness out a b c d ↔ r'.Witness out a b c d)
    (out : List Nat) (a b c d : Nat) :
    (LTree.fork l r).Witness out a b c d ↔
      (LTree.fork l r').Witness out a b c d :=
  (witness_fork_swap l r out a b c d).trans
    ((witness_fork_left_congr r r' l hleaves hw out a b c d).trans
      (witness_fork_swap r' l out a b c d))

theorem order_convex_syntax (ambient : List V) (rank : V → R)
    (hi : ∀ a∈ambient, ∀ b∈ambient, rank a=rank b → a=b)
    (t : BinarySyntax V)
    (hall : ∀ x∈t.frontier, x∈ambient) (hnd : t.frontier.Nodup)
    (hconv : ∀ u out, Context t u out → RankConvex ambient rank u.frontier) :
    ∃ s : BinarySyntax V, s.frontier.Perm t.frontier ∧
      s.frontier.Pairwise (fun a b => rank a<rank b) ∧
      ∀ (label : V → Nat) out a b c d,
        (encode label s).Witness out a b c d ↔ (encode label t).Witness out a b c d := by
  revert hall hnd hconv
  induction t with
  | tip v =>
    intro hall hnd hconv
    exact ⟨.tip v,List.Perm.refl _,by simp [BinarySyntax.frontier],fun _ _ _ _ _ _ => Iff.rfl⟩
  | fork v l r il ir =>
    intro hall hnd hconv
    have hn := List.nodup_append.mp hnd
    have hl : ∀ x∈l.frontier, x∈ambient := by
      intro x hx; exact hall x (List.mem_append_left _ hx)
    have hr : ∀ x∈r.frontier, x∈ambient := by
      intro x hx; exact hall x (List.mem_append_right _ hx)
    have hcl : ∀ u out, Context l u out → RankConvex ambient rank u.frontier := by
      intro u out hu
      exact hconv u (out++r.frontier) (.left v l r u out hu)
    have hcr : ∀ u out, Context r u out → RankConvex ambient rank u.frontier := by
      intro u out hu
      exact hconv u (out++l.frontier) (.right v l r u out hu)
    obtain ⟨sl,hpl,hsl,hwl⟩ := il hl hn.1 hcl
    obtain ⟨sr,hpr,hsr,hwr⟩ := ir hr hn.2.1 hcr
    have hw (label : V → Nat) out a b c d :
        (encode label (.fork v sl sr)).Witness out a b c d ↔
          (encode label (.fork v l r)).Witness out a b c d := by
      have hlmem : ∀ x, x∈(encode label sl).leaves ↔ x∈(encode label l).leaves := by
        intro x
        simpa only [encode_leaves] using (hpl.map label).mem_iff (a:=x)
      have hrmem : ∀ x, x∈(encode label sr).leaves ↔ x∈(encode label r).leaves := by
        intro x
        simpa only [encode_leaves] using (hpr.map label).mem_iff (a:=x)
      exact (witness_fork_left_congr (encode label sl) (encode label l)
        (encode label sr) hlmem (hwl label) out a b c d).trans
        (witness_fork_right_congr (encode label l) (encode label sr)
          (encode label r) hrmem (hwr label) out a b c d)
    have hd : ∀ x∈l.frontier, x∉r.frontier := by
      intro x hx hy
      exact hn.2.2 x hx x hy rfl
    rcases convex_sides_separated ambient l.frontier r.frontier rank hl hr hi hd
      (frontier_nonempty l) (frontier_nonempty r)
      (hcl l [] (.here l)) (hcr r [] (.here r)) with hsep | hsep
    · refine ⟨.fork v sl sr,hpl.append hpr,?_,hw⟩
      apply List.pairwise_append.mpr
      refine ⟨hsl,hsr,?_⟩
      intro a ha b hb
      exact hsep a (hpl.mem_iff.mp ha) b (hpr.mem_iff.mp hb)
    · refine ⟨.fork v sr sl,(hpr.append hpl).trans List.perm_append_comm,?_,?_⟩
      · apply List.pairwise_append.mpr
        refine ⟨hsr,hsl,?_⟩
        intro a ha b hb
        exact hsep a (hpr.mem_iff.mp ha) b (hpl.mem_iff.mp hb)
      · intro label out a b c d
        exact (witness_fork_swap (encode label sr) (encode label sl) out a b c d).trans
          (hw label out a b c d)

#print axioms order_convex_syntax
end Nanuq.GraphReceiver
