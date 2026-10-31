import ActualOrderedBlockReceiver
import CanonicalPortRanks

/-! UNCOMPILED canonical coding of the SAME all-label source-equivalent
syntax. A new finite Tree is derived, not relabelled by an unsupported rule. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.GraphReceiver
open Nanuq.Source Nanuq.GraphSyntax Nanuq.Restriction Nanuq.AdjacentCertificate
open scoped Classical
variable {V E X O : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem canonical_syntax_receiver (G : EdgeGraph V E) (tip : O ↪ V)
    (tipLabel : O → X) (code : X ↪ Nat) (xs : List O) (k : Nat) (base : List Nat)
    (dup : Nat → Bool) (s : BinarySyntax V) (oldLab : V → Nat)
    (hfront : s.frontier=xs.map tip) (hs : 2≤xs.length) (hk : k≤1) (hbase : base.Nodup)
    (hblocks : (xs.rotate k).map (fun t => code (tipLabel t))=blocks base dup)
    (hold : ∀ t, oldLab (tip t)=code (tipLabel t))
    (hsource : ∀ (lab : V → Nat) a b c d,
      LabelledQuartet G lab a b c d ↔ (encode lab s).Witness [] a b c d)
    (rank : X ≃ Fin base.length) (hrank : ∀ x, (rank x).val=base.idxOf (code x)) :
    ∃ (lab : V → Nat) (T : Tree),
      (∀ t, lab (tip t)=(rank (tipLabel t)).val) ∧
      T.size=(occurrenceLabels base.length (restrictedMask base dup)).length-1 ∧
      (∀ (q : Quartet) (r a b c d : Nat), q.parts r=(a,b,c,d) → a≠b → c≠d →
        (LabelledQuartet G lab a b c d ↔
          ∃ e∈T.internalIntervals 1,
            edgeWitness (occurrenceLabels base.length (restrictedMask base dup)) e.1 e.2 q r=true)) := by
  let lab : V → Nat := fun v => base.idxOf (oldLab v)
  have hlabel (t : O) : lab (tip t)=(rank (tipLabel t)).val := by
    simp only [lab,hold,hrank]
  have hleaves : (encode lab s).leaves=
      (xs.map (fun t => code (tipLabel t))).map base.idxOf := by
    simp only [encode_leaves,hfront,List.map_map,Function.comp_def,lab,hold]
  have hsize : 2≤(encode lab s).leaves.length := by
    simpa only [hleaves,List.length_map] using hs
  have hcanon : (encode lab s).leaves.rotate k=
      occurrenceLabels base.length (restrictedMask base dup) := by
    rw [hleaves,← List.map_rotate,← List.map_rotate,hblocks,
      restricted_blocks_canonical base hbase dup]
  obtain ⟨T,hT,hfinite⟩ := rotated_finite_receiver (encode lab s) hsize k hk
  refine ⟨lab,T,hlabel,?_,?_⟩
  · simpa only [hcanon] using hT
  · intro q r a b c d hp hab hcd
    simpa only [hcanon] using (hsource lab a b c d).trans (hfinite q r a b c d hp hab hcd)

#print axioms canonical_syntax_receiver
end Nanuq.GraphReceiver
