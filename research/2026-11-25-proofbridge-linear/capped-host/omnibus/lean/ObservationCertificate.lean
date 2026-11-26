import NanuqOmnibusFixture

set_option warningAsError true

namespace ResearchCommons.ObservationCertificate
variable {C O P : Type}

def Identified (admit : C → Prop) (obs : C → O) (target : C → P) (o : O) : Prop :=
  (∃ c, admit c ∧ obs c = o) ∧
  ∀ c d, admit c → admit d → obs c = o → obs d = o → target c = target d

/-- A certificate rejects identification, not feasibility. A pair is checked
under the same observation operator, target, and admission predicate. -/
theorem ambiguity (admit : C → Prop) (obs : C → O) (target : C → P) (o : O)
    (c d : C) (hc : admit c) (hd : admit d)
    (ho : obs c = o) (ho' : obs d = o) (hn : target c ≠ target d) :
    ¬ Identified admit obs target o := by
  intro h
  exact hn (h.2 c d hc hd ho ho')

/-- Finite exhaustive certificates need both declared coverage and an actual
matching witness to claim identification. -/
theorem finite_identified (admit : C → Prop) (obs : C → O) (target : C → P) (o : O)
    (enumerated : List C)
    (cover : ∀ c, admit c → obs c = o → c ∈ enumerated)
    (witness : ∃ c, admit c ∧ obs c = o)
    (all : ∃ p, ∀ c ∈ enumerated, admit c → obs c = o → target c = p) :
    Identified admit obs target o := by
  refine ⟨witness,?_⟩
  obtain ⟨p,h⟩ := all
  intro c d ac ad oc od
  exact (h c (cover c ac oc) ac oc).trans (h d (cover d ad od) ad od).symm

open ResearchCommons.NanuqOmnibusFixture

/-- Exact in the pinned finite contender pair. Extending the admission
predicate to a network class requires proving both embeddings into that class. -/
theorem checked_caterpillar_ambiguity :
    ¬ Identified (fun c => c = original ∨ c = reduced) observable joint (observable original) := by
  obtain ⟨hs,htrue,hfalse⟩ := same_obs_different_joint
  exact ambiguity _ observable joint _ original reduced
    (Or.inl rfl) (Or.inr rfl) rfl hs.symm (by rw [htrue,hfalse]; decide)

#print axioms ambiguity
#print axioms finite_identified
#print axioms checked_caterpillar_ambiguity
end ResearchCommons.ObservationCertificate
