import QueryExists
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

def relabelQuartet (f : Nat → Nat) (q : Quartet) : Quartet := ⟨f q.a,f q.b,f q.c,f q.d⟩

theorem querySet_relabel (f : Nat → Nat) (q : Quartet) (x y p z : Nat)
    (h : QuerySet q x y p z) : QuerySet (relabelQuartet f q) (f x) (f y) (f p) (f z) := by
  intro w
  change w∈q.labels.map f ↔ w∈([x,y,p,z].map f)
  simp only [List.mem_map]
  constructor
  · rintro ⟨v,hv,he⟩; exact ⟨v,(h v).mp hv,he⟩
  · rintro ⟨v,hv,he⟩; exact ⟨v,(h v).mpr hv,he⟩

theorem querySet_palette (P : List Nat) (q : Quartet) (x y p z : Nat)
    (h : QuerySet q x y p z) (hx : x∈P) (hy : y∈P) (hp : p∈P) (hz : z∈P) :
    ∀ v∈q.labels, v∈P := by
  intro v hv
  have hh := (h v).mp hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl <;> assumption

theorem ranked_quartet_mem (n : Nat) (keep : Nat → Bool) (q : Quartet) (hq : q∈quartets n)
    (hP : ∀ v∈q.labels, v∈retained n keep) :
    relabelQuartet (retained n keep).idxOf q ∈ quartets (retained n keep).length := by
  have ha := hP q.a (by simp [Quartet.labels])
  have hb := hP q.b (by simp [Quartet.labels])
  have hc := hP q.c (by simp [Quartet.labels])
  have hd := hP q.d (by simp [Quartet.labels])
  have hs := ((mem_quartets_iff n q).mp hq).1
  apply (mem_quartets_iff _ _).mpr
  exact ⟨⟨retained_rank_strict n keep q.a q.b ha hb hs.1,
    retained_rank_strict n keep q.b q.c hb hc hs.2.1,
    retained_rank_strict n keep q.c q.d hc hd hs.2.2⟩,
    List.idxOf_lt_length_iff.mpr hd⟩

theorem relabel_parts (f : Nat → Nat) (q : Quartet) (r a b c d : Nat)
    (h : q.parts r=(a,b,c,d)) :
    (relabelQuartet f q).parts r=(f a,f b,f c,f d) := by
  unfold Quartet.parts at h ⊢
  split at h <;> split <;> simp_all [relabelQuartet]
  all_goals split at h <;> split <;> simp_all [relabelQuartet]

 theorem ordered_parts (q : Quartet) (h : QuartetOrdered q) (r a b c d : Nat)
    (hp : q.parts r=(a,b,c,d)) :
    a∈q.labels ∧ b∈q.labels ∧ c∈q.labels ∧ d∈q.labels ∧ a≠b ∧ c≠d := by
  unfold Quartet.parts at hp
  split at hp
  · cases hp; simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false]; simp_all [QuartetOrdered]; omega
  · split at hp
    · cases hp; simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false]; simp_all [QuartetOrdered]; omega
    · cases hp; simp only [Quartet.labels,List.mem_cons,List.not_mem_nil,or_false]; simp_all [QuartetOrdered]; omega

#print axioms ranked_quartet_mem
#print axioms relabel_parts
end Nanuq.Restriction
