import Alexander001
import ChronologyFixture
open PopulationCounting PopulationReindex BirthOrder
open ResearchCommons.CappedLabeledGrid ResearchCommons.CappedPaddingLanguage
open ResearchCommons.PresentedCappedHost ResearchCommons.Alexander001
open ChronologicalEncoding

example {H V Time : Type} [LE Time] [LT Time]
    [Std.IsLinearPreorder Time] [Std.LawfulOrderLT Time]
    {dH : H → Time} {dV : V → Time} {k : Nat}
    (host : PresentedPopulation dH k k) (base : PresentedPopulation dV k k) (hk : 2 ≤ k)
    (word : Nat → Nat) (avoids : ¬ Realizes base.edge word) :
    ∃ (n : Nat) (date : Sum V (Vertex n k) → Time)
      (p : PresentedPopulation date k k),
      (¬ Realizes p.edge word) ∧ ¬ Embeds p.edge host.edge :=
  no_universal_labeled host base hk word avoids

private noncomputable def base := present ChronologyFixture.population
private noncomputable def n : Nat := 2 * fullRootCount (toNatPopulation base) + 2

/-- A downstream specialization to an actual populated graph with date ties. -/
theorem tied_fixture :
    ∃ (date : Sum Nat (Vertex n 2) → Nat)
      (q : PresentedPopulation date 2 2) (tint : Sum Nat (Vertex n 2) → Nat),
      (∀ x, tint x < 2) ∧
      (∀ x y l, q.edge x y = some l → tint x = l) ∧
      (∀ word, Realizes q.edge word ↔ Realizes base.edge word) ∧
      ¬ Embeds q.edge base.edge := by
  have same (x y l : Nat) (h : base.edge x y = some l) : x % 2 = l := by
    have z := (encode_some_iff ChronologyFixture.population x y l).mp h
    exact z.2.symm
  exact fixed_nonuniversal base base (by decide) (· % 2) (fun x => by omega) same n (by dsimp [n]; omega)

#print axioms tied_fixture
