import FiniteGenomeIdentifiability
import ThreeTaxonIdentifiability
import ThreeTaxonFiniteEvidence

/-!
Reuse the existing complete finite-gARG obstruction and prescribed three-taxon
proofs. The only new proof is transport between the two ORIGINAL nominal
three-topology types, so exact-law identification and finite-evidence bounds
can be called on one carrier. No biological/source-law or tail-bound claim is
introduced. All old source bodies and original conclusions remain unchanged.
-/
namespace ResearchCommons.Claims.Genome

/-- Literal constructor-preserving identification of the two retained types. -/
def exactTopology : ThreeTaxonFiniteEvidence.Topology ≃ ThreeTaxonIdentifiability.Topology where
  toFun t := match t with
    | .ab_c => .ab_c
    | .ac_b => .ac_b
    | .bc_a => .bc_a
  invFun t := match t with
    | .ab_c => .ab_c
    | .ac_b => .ac_b
    | .bc_a => .bc_a
  left_inv t := by cases t <;> rfl
  right_inv t := by cases t <;> rfl

theorem law_transport (s g : ThreeTaxonFiniteEvidence.Topology) (c : ℝ) :
    ThreeTaxonIdentifiability.law (exactTopology s) c (exactTopology g) =
      ThreeTaxonFiniteEvidence.law s c g := by
  cases s <;> cases g <;> rfl

/-- The OLD exact-law theorem, now on the SAME literal topology carrier used
by the OLD finite-support, adverse-witness and strict-margin endpoints. -/
theorem evidence_law_identifiable (s r : ThreeTaxonFiniteEvidence.Topology) (c d : ℝ)
    (hc : c < 1) (hd : d < 1) :
    ThreeTaxonFiniteEvidence.law s c = ThreeTaxonFiniteEvidence.law r d ↔
      s = r ∧ c = d := by
  constructor
  · intro h
    have same : ThreeTaxonIdentifiability.law (exactTopology s) c =
        ThreeTaxonIdentifiability.law (exactTopology r) d := by
      funext g
      calc
        ThreeTaxonIdentifiability.law (exactTopology s) c g =
            ThreeTaxonFiniteEvidence.law s c (exactTopology.symm g) := by
          simpa only [Equiv.apply_symm_apply] using law_transport s (exactTopology.symm g) c
        _ = ThreeTaxonFiniteEvidence.law r d (exactTopology.symm g) := congrFun h _
        _ = ThreeTaxonIdentifiability.law (exactTopology r) d g := by
          simpa only [Equiv.apply_symm_apply] using
            (law_transport r (exactTopology.symm g) d).symm
    obtain ⟨hs, hp⟩ :=
      (ThreeTaxonIdentifiability.law_identifiable (exactTopology s) (exactTopology r)
        c d hc hd).mp same
    exact ⟨exactTopology.injective hs, hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end ResearchCommons.Claims.Genome
