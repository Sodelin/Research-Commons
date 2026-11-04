import NativePopulationTableCertificate
import G7SparseRowProducts

/-! SOURCE PROPOSAL. The COMPLETE imported context is UNELABORATED.
No selected type/axiom audit, generated literal, checker run or native result
is claimed. This composes an actual supplied finite-table check with the
existing sparse row reader. It does not introduce a population kernel. -/

namespace Astra.CertifiedPopulationRows

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.FullEpochPolynomial
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.SparseRowProducts

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Embed every original list position in the SAME population coordinate.
Duplicate destination rows and zero terms are retained. -/
def sparseRows {N : RootedBinary V E X} {sample : Copy → X}
    (i : Option E) (rows : NativePopulationTableCertificate.Table N sample) :
    Rows (Option E) (Code N sample) :=
  rows.map fun row => (row.1, embedExpr i row.2)

/-- Literal fibre aggregation commutes with the inherited exponent embedding. -/
theorem read_sparseRows {N : RootedBinary V E X} {sample : Copy → X}
    (i : Option E) (rows : NativePopulationTableCertificate.Table N sample)
    (d : Code N sample) :
    readRows id (sparseRows i rows) d =
      embedExpr i (NativePopulationTableCertificate.collect rows d) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change (if row.1 = d then embedExpr i row.2 else []) ++
        readRows id (sparseRows i rows) d =
          embedExpr i ((if row.1 = d then row.2 else []) ++
            NativePopulationTableCertificate.collect rows d)
      rw [ih]
      by_cases h : row.1 = d <;> simp [h, embedExpr, List.map_append]

/-- Total evaluated Code fibres for ONE checked table and actual population.
The supplied Boolean check covers all admitted destinations, including zero
on absence. Physical rates and duration are the SAME on both sides. -/
theorem checked_sparseRows_actual (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (rows : NativePopulationTableCertificate.Table N sample)
    (h : NativePopulationTableCertificate.check N (Fintype.card Copy) s rows = true)
    (d : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r : PositivePairRates E) (t : ℝ≥0) :
    value (readRows id (sparseRows i rows) d) (survival r t) =
      (sourceTimeKernel N r t s d).toReal := by
  rw [read_sparseRows, value_embedExpr]
  exact NativePopulationTableCertificate.checked_actual_population
    N s rows h d i hs r t

end Astra.CertifiedPopulationRows
