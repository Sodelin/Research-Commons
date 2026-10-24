import PedigreeBlockRecovery
import PedigreeBlockDependence

/-!
Reuse the COMPLETE original one-generation observed-symbol recovery law and
actual repeated-block counterexample. The only new proof composes the OLD
pathwise restriction theorem with its OLD observed-partition equivalence.
One SAME choice array and injective parental-symbol bank are retained.
No independence is needed by this deterministic composition. Probability
formulas keep their separate fair-independent law and positive-block premise.
-/
namespace ResearchCommons.Claims.BlockRecovery

universe u v

/-- More observed blocks preserve an already correct partition, for the SAME
actual configuration and parental-symbol assignment. No random law is used. -/
theorem recovered_of_restrict {Family : Type u} {Symbol : Type v}
    {n : Family → Nat} {B D : Nat} (hBD : B ≤ D)
    (x : ∀ i, PedigreeBlock.Config (n i) D)
    (symbols : Fin D → Family × Bool → Symbol)
    (hinj : ∀ j, Function.Injective (symbols j))
    (h : PedigreeBlock.Recovered
      (fun i => PedigreeBlock.restrictBlocks hBD (x i))
      (fun j => symbols (Fin.castLE hBD j))) :
    PedigreeBlock.Recovered x symbols := by
  apply (PedigreeBlock.recovered_iff_connected x symbols hinj).mpr
  have restricted :=
    (PedigreeBlock.recovered_iff_connected
      (fun i => PedigreeBlock.restrictBlocks hBD (x i))
      (fun j => symbols (Fin.castLE hBD j))
      (fun j => hinj (Fin.castLE hBD j))).mp h
  intro i
  exact PedigreeBlock.connected_of_restrict hBD (x i) (restricted i)

end ResearchCommons.Claims.BlockRecovery
