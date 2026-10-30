import RankOrder
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

def QuartetOrdered (q : Quartet) : Prop := q.a<q.b ∧ q.b<q.c ∧ q.c<q.d

def QuerySet (q : Quartet) (x y p z : Nat) : Prop :=
  ∀ w, w∈q.labels ↔ w∈[x,y,p,z]

theorem mem_quartets_iff (n : Nat) (q : Quartet) :
    q∈quartets n ↔ QuartetOrdered q ∧ q.d<n := by
  rcases q with ⟨a,b,c,d⟩
  simp only [quartets,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨aa,haa,bb,hbb,cc,hcc,dd,hdd,hm⟩
    split at hm
    · simp only [List.mem_singleton,Quartet.mk.injEq] at hm
      rcases hm with ⟨rfl,rfl,rfl,rfl⟩
      exact ⟨by assumption,hdd⟩
    · simp at hm
  · intro h
    change (a<b ∧ b<c ∧ c<d) ∧ d<n at h
    refine ⟨a,by omega,b,by omega,c,by omega,d,h.2,?_⟩
    simp [h.1]

theorem ordered_quartet_unique (q r : Quartet) (hq : QuartetOrdered q) (hr : QuartetOrdered r)
    (hsub : ∀ x∈q.labels, x∈r.labels) : q=r := by
  rcases q with ⟨a,b,c,d⟩
  rcases r with ⟨aa,bb,cc,dd⟩
  have ha := hsub a (by simp [Quartet.labels])
  have hb := hsub b (by simp [Quartet.labels])
  have hc := hsub c (by simp [Quartet.labels])
  have hd := hsub d (by simp [Quartet.labels])
  simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false] at ha hb hc hd
  change a<b ∧ b<c ∧ c<d at hq
  change aa<bb ∧ bb<cc ∧ cc<dd at hr
  have h1 : a=aa := by omega
  have h2 : b=bb := by omega
  have h3 : c=cc := by omega
  have h4 : d=dd := by omega
  simp only [h1,h2,h3,h4]

 theorem query_lookup (n x y p z : Nat) (q : Quartet)
    (hq : q∈quartets n) (hset : QuerySet q x y p z) :
    (quartets n)[quartetIndex (quartets n) x y p z]? = some q := by
  let test := fun Q : Quartet => [x,y,p,z].all (fun w => Q.labels.contains w)
  have hp : test q=true := by
    apply List.all_eq_true.mpr
    intro w hw
    simpa only [List.contains_iff_mem] using (hset w).mpr hw
  have hi := List.findIdx_lt_length_of_exists (xs:=quartets n) (p:=test) ⟨q,hq,hp⟩
  let r := (quartets n)[(quartets n).findIdx test]'hi
  have hrm : r∈quartets n := List.getElem_mem hi
  have hrp : test r=true := List.findIdx_getElem
  have he : q=r := ordered_quartet_unique q r ((mem_quartets_iff n q).mp hq).1
    ((mem_quartets_iff n r).mp hrm).1 (by
      intro w hw
      have hh := List.all_eq_true.mp hrp w ((hset w).mp hw)
      simpa only [List.contains_iff_mem] using hh)
  change (quartets n)[(quartets n).findIdx test]? = some q
  rw [List.getElem?_eq_getElem hi]
  exact congrArg some he.symm

#print axioms query_lookup
end Nanuq.Restriction
