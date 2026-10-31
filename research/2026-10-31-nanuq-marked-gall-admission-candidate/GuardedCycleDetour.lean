import OriginalSimpleGallDetour

/-! UNCOMPILED orientation-independent version of the accepted cycle-tail argument.
A marked incoming edge may be oriented toward the stored source endpoint. -/
namespace Nanuq.MarkedGallAdmission
open Nanuq.Source Nanuq.SimpleGallAdmission
open scoped Graph
variable {V E : Type*} (G : EdgeGraph V E)

theorem guarded_cycle_detour {h a b : V} {e f : E} {W : List E} {keep : E → Prop}
    (hc : (originalGraph G).IsCycleThrough e h a W)
    (hf : (originalGraph G).IsLink f h b) (hfm : f∈W)
    (hkeep : ∀ d ∈ e::W, d≠e → d≠f → keep d) :
    G.UReach (fun d => keep d ∧ G.source d≠h ∧ G.target d≠h) a b := by
  cases W with
  | nil => simp at hfm
  | cons g R =>
    have hfg : f=g := hc.isPath.eq_head_of_inc_source hfm hf.inc_left
    subst g
    have hfn : f∉R := (List.nodup_cons.mp hc.isPath.nodup).1
    cases hp : hc.isPath with
    | @cons h w a f R hl ht hnot =>
      have hwb : w=b := hl.right_unique hf
      subst w
      apply G.ureach_symm
      apply original_walk_ureach G ht.isWalk
      intro d hd
      have hde : d≠e := fun hh => hc.notMem (hh ▸ List.mem_cons_of_mem f hd)
      have hdf : d≠f := fun hh => hfn (hh ▸ hd)
      refine ⟨hkeep d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)) hde hdf,?_,?_⟩
      · intro hs
        apply hnot
        apply Graph.mem_walkVertices_of_mem_covered
        exact ⟨d,hd,(show (originalGraph G).IsLink d h (G.target d) from
          Or.inl ⟨hs,rfl⟩).inc_left⟩
      · intro ht
        apply hnot
        apply Graph.mem_walkVertices_of_mem_covered
        exact ⟨d,hd,(show (originalGraph G).IsLink d (G.source d) h from
          Or.inl ⟨rfl,ht⟩).inc_right⟩

#print axioms guarded_cycle_detour
end Nanuq.MarkedGallAdmission
