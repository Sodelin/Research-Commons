import Std

set_option warningAsError true

namespace ResearchCommons.LineGraphTriangleGuard
variable {V E : Type}

def Next (tail head : E → V) (e f : E) : Prop := head e = tail f

def Adj (tail head : E → V) (e f : E) : Prop :=
  Next tail head e f ∨ Next tail head f e

private theorem no_transitive_triple (tail head : E → V)
    (noloop : ∀ e, tail e ≠ head e) {e f g : E}
    (ef : Next tail head e f) (fg : Next tail head f g)
    (eg : Next tail head e g) : False :=
  noloop f (ef.symm.trans (eg.trans fg.symm))

/-- Source coloring via directed line graph erases the triangle signature
of every chronological base graph; not a proof of nonexistence of another invariant. -/
theorem triangle_free (tail head : E → V) (time : V → Nat)
    (rises : ∀ e, time (tail e) < time (head e)) (e f g : E) :
    ¬ (Adj tail head e f ∧ Adj tail head f g ∧ Adj tail head e g) := by
  have noloop (e : E) : tail e ≠ head e := by
    intro h
    have hp := rises e
    rw [h] at hp
    exact Nat.lt_irrefl _ hp
  have forward {a b : E} (h : Next tail head a b) :
      time (tail a) < time (tail b) := by
    have h' := rises a
    change head a = tail b at h
    rwa [h] at h'
  rintro ⟨ef | fe, fg | gf, eg | ge⟩
  · exact no_transitive_triple tail head noloop ef fg eg
  · have a := forward ef; have b := forward fg; have c := forward ge; omega
  · exact no_transitive_triple tail head noloop eg gf ef
  · exact no_transitive_triple tail head noloop ge ef gf
  · exact no_transitive_triple tail head noloop fe eg fg
  · exact no_transitive_triple tail head noloop fg ge fe
  · have a := forward fe; have b := forward gf; have c := forward eg; omega
  · exact no_transitive_triple tail head noloop gf fe ge

#print axioms triangle_free
end ResearchCommons.LineGraphTriangleGuard
