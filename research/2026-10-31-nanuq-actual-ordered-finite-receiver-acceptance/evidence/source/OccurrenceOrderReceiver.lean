import OrderedSyntax

/-! UNCOMPILED finite receiver. Original graph/drawing adapters must derive
its no-alternation premise; the output is syntax, not a redrawn physical graph. -/
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V R : Type*} [LinearOrder R]

theorem occurrence_order_receiver (t : BinarySyntax V) (xs : List V)
    (rank : V → R) (code : V → Nat)
    (hp : t.frontier.Perm xs) (hnd : xs.Nodup) (hs : 2≤xs.length)
    (hsort : xs.Pairwise (fun a b => rank a<rank b))
    (hi : ∀ a∈xs, ∀ b∈xs, rank a=rank b → a=b)
    (hno : ∀ a c d e, a∈xs → c∈xs → d∈xs → e∈xs →
      (encode code t).Witness [] (code a) (code c) (code d) (code e) →
      ¬((rank a<rank d ∧ rank d<rank c ∧ rank c<rank e) ∨
        (rank d<rank a ∧ rank a<rank e ∧ rank e<rank c))) :
    ∃ s : BinarySyntax V, s.frontier=xs ∧
      ∀ (label : V → Nat) a b c d,
        (encode label s).Witness [] a b c d ↔ (encode label t).Witness [] a b c d := by
  cases xs with
  | nil => simp at hs
  | cons anchor tail =>
    have hat : anchor∈t.frontier := hp.mem_iff.mpr (by simp)
    have hts : 2≤t.frontier.length := by simpa only [hp.length_eq] using hs
    obtain ⟨v,rest,hfocus,hfw⟩ := focus_occurrence t anchor hat hts
    let focused : BinarySyntax V := .fork v (.tip anchor) rest
    have hfp : focused.frontier.Perm (anchor::tail) := hfocus.trans hp
    have hfn : focused.frontier.Nodup := hfp.nodup_iff.mpr hnd
    have hfirst : ∀ x∈focused.frontier, x≠anchor → rank anchor<rank x := by
      intro x hx hne
      have hm := hfp.mem_iff.mp hx
      have ht : x∈tail := (List.mem_cons.mp hm).resolve_left hne
      exact List.rel_of_pairwise_cons hsort ht
    have hno' : ∀ a c d e,
        a∈focused.frontier → c∈focused.frontier → d∈focused.frontier → e∈focused.frontier →
        (encode code focused).Witness [] (code a) (code c) (code d) (code e) →
        ¬((rank a<rank d ∧ rank d<rank c ∧ rank c<rank e) ∨
          (rank d<rank a ∧ rank a<rank e ∧ rank e<rank c)) := by
      intro a c d e ha hc hd he hw
      exact hno a c d e (hfp.mem_iff.mp ha) (hfp.mem_iff.mp hc)
        (hfp.mem_iff.mp hd) (hfp.mem_iff.mp he) ((hfw code _ _ _ _).mp hw)
    have hconv : ∀ u out, Context rest u out → RankConvex (anchor::tail) rank u.frontier := by
      intro u out hu a ha c hc b hb hab hbc
      exact anchored_frontier_convex v anchor rest rank code hfn hfirst hno' hu
        a ha c hc b (hfp.mem_iff.mpr hb) hab hbc
    have hrmem : ∀ x∈rest.frontier, x∈anchor::tail := by
      intro x hx
      exact hfp.mem_iff.mp (by change x∈[anchor]++rest.frontier; exact List.mem_append_right _ hx)
    have hrnd : rest.frontier.Nodup := by
      have hn : (anchor::rest.frontier).Nodup := hfn
      exact (List.nodup_cons.mp hn).2
    obtain ⟨ordered,hrop,hros,hrow⟩ :=
      order_convex_syntax (anchor::tail) rank hi rest hrmem hrnd hconv
    let s : BinarySyntax V := .fork v (.tip anchor) ordered
    have hsp : s.frontier.Perm (anchor::tail) :=
      (hrop.cons anchor).trans hfp
    have hss : s.frontier.Pairwise (fun a b => rank a<rank b) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_,hros⟩
      intro x hx
      have hrx := hrop.mem_iff.mp hx
      apply hfirst x
      · change x∈[anchor]++rest.frontier
        exact List.mem_append_right _ hrx
      · intro he
        have hn : anchor∉rest.frontier := (List.nodup_cons.mp hfn).1
        exact hn (he ▸ hrx)
    refine ⟨s,List.Perm.eq_of_pairwise (fun a b _ _ hab hba =>
      False.elim (lt_asymm hab hba)) hss hsort hsp,?_⟩
    intro label a b c d
    have hleaves : ∀ x, x∈(encode label ordered).leaves ↔ x∈(encode label rest).leaves := by
      intro x
      simpa only [encode_leaves] using (hrop.map label).mem_iff (a:=x)
    exact (witness_fork_right_congr (.tip (label anchor)) (encode label ordered)
      (encode label rest) hleaves (hrow label) [] a b c d).trans (hfw label a b c d)

#print axioms occurrence_order_receiver
end Nanuq.GraphReceiver
