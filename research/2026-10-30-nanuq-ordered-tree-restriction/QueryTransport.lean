import QuartetRelabel
import CodeBridge
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

def codedPattern (T : Tree) (tips : List Nat) (n : Nat) : Nat :=
  T.summary (edgeContribution tips (quartets n)) 1

def EdgeTransport (n : Nat) (keep : Nat → Bool) (T U : Tree) (tips tips' : List Nat) : Prop :=
  ∀ q∈quartets n, (∀ v∈q.labels, v∈retained n keep) → ∀ r, r<3 →
    ((∃ e∈T.internalIntervals 1, edgeWitness tips e.1 e.2 q r=true) ↔
     (∃ e∈U.internalIntervals 1,
      edgeWitness tips' e.1 e.2 (relabelQuartet (retained n keep).idxOf q) r=true))

theorem query_transport (n : Nat) (keep : Nat → Bool) (T U : Tree) (tips tips' : List Nat)
    (ht : EdgeTransport n keep T U tips tips') (x y p z : Nat)
    (hx : x∈retained n keep) (hy : y∈retained n keep) (hp : p∈retained n keep) (hz : z∈retained n keep)
    (hxy : x≠y) (hxp : x≠p) (hxz : x≠z) (hyp : y≠p) (hyz : y≠z) (hpz : p≠z) :
    code (codedPattern T tips n) (quartetIndex (quartets n) x y p z) =
      code (codedPattern U tips' (retained n keep).length)
        (quartetIndex (quartets (retained n keep).length)
          ((retained n keep).idxOf x) ((retained n keep).idxOf y)
          ((retained n keep).idxOf p) ((retained n keep).idxOf z)) ∧
    quartetAt (quartets (retained n keep).length)
      ((retained n keep).idxOf x) ((retained n keep).idxOf y)
      ((retained n keep).idxOf p) ((retained n keep).idxOf z) =
      relabelQuartet (retained n keep).idxOf (quartetAt (quartets n) x y p z) := by
  let P := retained n keep
  have hxn : x<n := List.mem_range.mp (List.mem_filter.mp hx).1
  have hyn : y<n := List.mem_range.mp (List.mem_filter.mp hy).1
  have hpn : p<n := List.mem_range.mp (List.mem_filter.mp hp).1
  have hzn : z<n := List.mem_range.mp (List.mem_filter.mp hz).1
  obtain ⟨q,hq,hset⟩ := query_quartet_exists n x y p z hxn hyn hpn hzn hxy hxp hxz hyp hyz hpz
  have hqP := querySet_palette P q x y p z hset hx hy hp hz
  have old := query_lookup n x y p z q hq hset
  have new := query_lookup P.length (P.idxOf x) (P.idxOf y) (P.idxOf p) (P.idxOf z)
    (relabelQuartet P.idxOf q) (ranked_quartet_mem n keep q hq hqP)
    (querySet_relabel P.idxOf q x y p z hset)
  dsimp only [P] at new
  constructor
  · apply code_eq_of_three_bits
    intro r hr
    apply Bool.eq_iff_iff.mpr
    unfold codedPattern
    rw [summary_code_edge T tips (quartets n) _ q old r hr,
      summary_code_edge U tips' (quartets (retained n keep).length) _ (relabelQuartet (retained n keep).idxOf q) new r hr]
    exact ht q hq hqP r hr
  · simp only [quartetAt,new,old,Option.getD_some]

theorem relabel_side_rank (P : List Nat) (q : Quartet) (r x : Nat) (hx : x∈P) :
    (relabelQuartet P.idxOf q).side r (P.idxOf x) = q.side r x := by
  have hh (y : Nat) : (P.idxOf x == P.idxOf y) = (x==y) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact List.idxOf_inj hx
  simp only [Quartet.side,relabelQuartet,hh]

#print axioms query_transport
#print axioms relabel_side_rank
end Nanuq.Restriction
