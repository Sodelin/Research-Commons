import Context
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V : Type*}

theorem encode_witness_iff (label : V → Nat) (t : BinarySyntax V)
    (outside : List Nat) (a b c d : Nat) :
    (encode label t).Witness outside a b c d ↔
      ∃ u inner, Context t u inner ∧
        Cut (u.frontier.map label) (inner.map label ++ outside) a b c d := by
  induction t generalizing outside with
  | tip v =>
    constructor
    · intro h
      exact ⟨.tip v,[],.here _,by simpa [BinarySyntax.frontier,encode,LTree.Witness] using h⟩
    · rintro ⟨u,inner,hctx,hcut⟩
      cases hctx
      simpa [BinarySyntax.frontier,encode,LTree.Witness] using hcut
  | fork v l r il ir =>
    simp only [encode,LTree.Witness,encode_leaves]
    constructor
    · rintro (h | h | h)
      · exact ⟨.fork v l r,[],.here _,by simpa [BinarySyntax.frontier] using h⟩
      · obtain ⟨u,inner,hctx,hcut⟩ := (il _).mp h
        exact ⟨u,inner++r.frontier,.left v l r u inner hctx,
          by simpa only [List.map_append,List.append_assoc] using hcut⟩
      · obtain ⟨u,inner,hctx,hcut⟩ := (ir _).mp h
        exact ⟨u,inner++l.frontier,.right v l r u inner hctx,
          by simpa only [List.map_append,List.append_assoc] using hcut⟩
    · rintro ⟨u,inner,hctx,hcut⟩
      cases hctx with
      | here => exact Or.inl (by simpa [BinarySyntax.frontier] using hcut)
      | left _ _ _ _ inner hctx =>
        exact Or.inr (Or.inl ((il _).mpr ⟨u,inner,hctx,
          by simpa only [List.map_append,List.append_assoc] using hcut⟩))
      | right _ _ _ _ inner hctx =>
        exact Or.inr (Or.inr ((ir _).mpr ⟨u,inner,hctx,
          by simpa only [List.map_append,List.append_assoc] using hcut⟩))

#print axioms encode_witness_iff
end Nanuq.GraphReceiver
