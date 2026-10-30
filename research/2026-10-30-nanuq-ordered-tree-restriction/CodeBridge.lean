import FiniteEdgeBridge
import BitWitness
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem summary_code_edge (T : Tree) (tips : List Nat) (qs : List Quartet) (idx : Nat)
    (q : Quartet) (hq : qs[idx]?=some q) (r : Nat) (hr : r<3) :
    (code (T.summary (edgeContribution tips qs) 1) idx).testBit r=true ↔
      ∃ e∈T.internalIntervals 1, edgeWitness tips e.1 e.2 q r=true := by
  rw [T.code_physical_iff tips qs 1 idx r hr]
  constructor
  · rintro ⟨e,he,qi,hqi,hidx,hw⟩
    have hget := List.mem_zipIdx_iff_getElem?.mp hqi
    rw [hidx,hq] at hget
    have heq : q=qi.1 := Option.some.inj hget
    exact ⟨e,he,heq.symm ▸ hw⟩
  · rintro ⟨e,he,hw⟩
    exact ⟨e,he,(q,idx),List.mk_mem_zipIdx_iff_getElem?.mpr hq,rfl,hw⟩

theorem code_eq_of_three_bits (p i p' i' : Nat)
    (h : ∀ r, r<3 → (code p i).testBit r=(code p' i').testBit r) :
    code p i=code p' i' := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r<3
  · exact h r hr
  · unfold code
    change (((p >>> (3*i)) % 2^3).testBit r) = (((p' >>> (3*i')) % 2^3).testBit r)
    simp only [Nat.testBit_mod_two_pow,hr,decide_false,Bool.false_and]

#print axioms summary_code_edge
#print axioms code_eq_of_three_bits
end Nanuq.Restriction
