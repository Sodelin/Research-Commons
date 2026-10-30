import QuartetLookup
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem query_quartet_exists (n x y p z : Nat)
    (hx : x<n) (hy : y<n) (hp : p<n) (hz : z<n)
    (hxy : x≠y) (hxp : x≠p) (hxz : x≠z) (hyp : y≠p) (hyz : y≠z) (hpz : p≠z) :
    ∃ q∈quartets n, QuerySet q x y p z := by
  by_cases cmp1 : y<x
  ·
    by_cases cmp2 : p<y
    ·
      by_cases cmp3 : z<p
      ·
        refine ⟨⟨z,p,y,x⟩,(mem_quartets_iff n _).mpr ⟨by change z<p ∧ p<y ∧ y<x; omega,by assumption⟩,?_⟩
        intro w
        simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
      ·
        by_cases cmp4 : z<y
        ·
          refine ⟨⟨p,z,y,x⟩,(mem_quartets_iff n _).mpr ⟨by change p<z ∧ z<y ∧ y<x; omega,by assumption⟩,?_⟩
          intro w
          simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
        ·
          by_cases cmp5 : z<x
          ·
            refine ⟨⟨p,y,z,x⟩,(mem_quartets_iff n _).mpr ⟨by change p<y ∧ y<z ∧ z<x; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
          ·
            refine ⟨⟨p,y,x,z⟩,(mem_quartets_iff n _).mpr ⟨by change p<y ∧ y<x ∧ x<z; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
    ·
      by_cases cmp6 : p<x
      ·
        by_cases cmp7 : z<y
        ·
          refine ⟨⟨z,y,p,x⟩,(mem_quartets_iff n _).mpr ⟨by change z<y ∧ y<p ∧ p<x; omega,by assumption⟩,?_⟩
          intro w
          simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
        ·
          by_cases cmp8 : z<p
          ·
            refine ⟨⟨y,z,p,x⟩,(mem_quartets_iff n _).mpr ⟨by change y<z ∧ z<p ∧ p<x; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
          ·
            by_cases cmp9 : z<x
            ·
              refine ⟨⟨y,p,z,x⟩,(mem_quartets_iff n _).mpr ⟨by change y<p ∧ p<z ∧ z<x; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
            ·
              refine ⟨⟨y,p,x,z⟩,(mem_quartets_iff n _).mpr ⟨by change y<p ∧ p<x ∧ x<z; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
      ·
        by_cases cmp10 : z<y
        ·
          refine ⟨⟨z,y,x,p⟩,(mem_quartets_iff n _).mpr ⟨by change z<y ∧ y<x ∧ x<p; omega,by assumption⟩,?_⟩
          intro w
          simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
        ·
          by_cases cmp11 : z<x
          ·
            refine ⟨⟨y,z,x,p⟩,(mem_quartets_iff n _).mpr ⟨by change y<z ∧ z<x ∧ x<p; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
          ·
            by_cases cmp12 : z<p
            ·
              refine ⟨⟨y,x,z,p⟩,(mem_quartets_iff n _).mpr ⟨by change y<x ∧ x<z ∧ z<p; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
            ·
              refine ⟨⟨y,x,p,z⟩,(mem_quartets_iff n _).mpr ⟨by change y<x ∧ x<p ∧ p<z; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
  ·
    by_cases cmp13 : p<x
    ·
      by_cases cmp14 : z<p
      ·
        refine ⟨⟨z,p,x,y⟩,(mem_quartets_iff n _).mpr ⟨by change z<p ∧ p<x ∧ x<y; omega,by assumption⟩,?_⟩
        intro w
        simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
      ·
        by_cases cmp15 : z<x
        ·
          refine ⟨⟨p,z,x,y⟩,(mem_quartets_iff n _).mpr ⟨by change p<z ∧ z<x ∧ x<y; omega,by assumption⟩,?_⟩
          intro w
          simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
        ·
          by_cases cmp16 : z<y
          ·
            refine ⟨⟨p,x,z,y⟩,(mem_quartets_iff n _).mpr ⟨by change p<x ∧ x<z ∧ z<y; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
          ·
            refine ⟨⟨p,x,y,z⟩,(mem_quartets_iff n _).mpr ⟨by change p<x ∧ x<y ∧ y<z; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
    ·
      by_cases cmp17 : p<y
      ·
        by_cases cmp18 : z<x
        ·
          refine ⟨⟨z,x,p,y⟩,(mem_quartets_iff n _).mpr ⟨by change z<x ∧ x<p ∧ p<y; omega,by assumption⟩,?_⟩
          intro w
          simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
        ·
          by_cases cmp19 : z<p
          ·
            refine ⟨⟨x,z,p,y⟩,(mem_quartets_iff n _).mpr ⟨by change x<z ∧ z<p ∧ p<y; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
          ·
            by_cases cmp20 : z<y
            ·
              refine ⟨⟨x,p,z,y⟩,(mem_quartets_iff n _).mpr ⟨by change x<p ∧ p<z ∧ z<y; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
            ·
              refine ⟨⟨x,p,y,z⟩,(mem_quartets_iff n _).mpr ⟨by change x<p ∧ p<y ∧ y<z; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
      ·
        by_cases cmp21 : z<x
        ·
          refine ⟨⟨z,x,y,p⟩,(mem_quartets_iff n _).mpr ⟨by change z<x ∧ x<y ∧ y<p; omega,by assumption⟩,?_⟩
          intro w
          simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
        ·
          by_cases cmp22 : z<y
          ·
            refine ⟨⟨x,z,y,p⟩,(mem_quartets_iff n _).mpr ⟨by change x<z ∧ z<y ∧ y<p; omega,by assumption⟩,?_⟩
            intro w
            simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
          ·
            by_cases cmp23 : z<p
            ·
              refine ⟨⟨x,y,z,p⟩,(mem_quartets_iff n _).mpr ⟨by change x<y ∧ y<z ∧ z<p; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
            ·
              refine ⟨⟨x,y,p,z⟩,(mem_quartets_iff n _).mpr ⟨by change x<y ∧ y<p ∧ p<z; omega,by assumption⟩,?_⟩
              intro w
              simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc]
#print axioms query_quartet_exists
end Nanuq.Restriction
