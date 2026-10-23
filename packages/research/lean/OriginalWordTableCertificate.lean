import NativeSparseTableCertificate
import G7EffectiveWordCoefficients

/-! A direct finite-result certificate against the EXISTING concrete word
recurrence. No universal primitive/native step equivalence or desired-law
premise is assumed. Natural initialization retains one complete register draw.
Completion, legal calendar admission and final observation remain separate. -/
namespace Astra.OriginalWordTableCertificate
open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveInitializationCoefficients
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.SymbolicProgramPolynomial
open Astra.NativeSparseTableCertificate
open scoped NNReal

variable {J V E X Copy : Type*}
variable [DecidableEq J] [Fintype J]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

local instance (N : RootedBinary V E X) : DecidablePred N.graph.IsHybrid :=
  hybridDecidable N

def checkWord (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (s : Code N sample)
    (supplied : Rows (WordVariable N J) (Code N sample)) : Bool :=
  checkRows (project N Finset.univ) (wordRows N H common word s) supplied

theorem checked_original_word (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (s : Code N sample)
    (supplied : Rows (WordVariable N J) (Code N sample))
    (h : checkWord N H common word s supplied = true)
    (b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E)
    (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) :
    value (readRows (project N Finset.univ) supplied b) (wordVariables N r gamma dur) =
      (((sourceProgram N r (word.map (instantiateGamma N H gamma common dur)) s).map
        (projection N Finset.univ)) b).toReal := by
  have heq := checkRows_sound (project N Finset.univ)
    (wordRows N H common word s) supplied h b
  have evaluated := congrArg
    (MvPolynomial.eval₂ (Rat.castHom ℝ) (wordVariables N r gamma dur)) heq
  rw [eval_polynomial, eval_polynomial] at evaluated
  exact evaluated.symm.trans (wordRows_actual N H common r gamma dur word s b)

def checkNaturalWord (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E))
    (supplied : Rows (WordVariable N J) (Code N sample)) : Bool :=
  checkRows (project N Finset.univ) (naturalWordRows N sample H common word) supplied

/-- The entire natural initial polynomial is OUTSIDE the transition word.
Every selected register-labelled output fibre is compared before evaluation. -/
theorem checked_natural_word (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E))
    (supplied : Rows (WordVariable N J) (Code N sample))
    (h : checkNaturalWord N sample H common word supplied = true)
    (b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E)
    (p : HybridProbabilities N) (dur : J → ℝ≥0) :
    value (readRows (project N Finset.univ) supplied b)
        (wordVariables N r (originalGamma p) dur) =
      (((initializedWordLaw N sample H p common r dur word).map
        (projection N Finset.univ)) b).toReal := by
  have heq := checkRows_sound (project N Finset.univ)
    (naturalWordRows N sample H common word) supplied h b
  have evaluated := congrArg
    (MvPolynomial.eval₂ (Rat.castHom ℝ) (wordVariables N r (originalGamma p) dur)) heq
  rw [eval_polynomial, eval_polynomial] at evaluated
  exact evaluated.symm.trans (naturalWordRows_actual N sample H common r p dur word b)

/-- The native bank uses literal finite positions. Its source-variable map is
checked structurally; no physical variable or inheritance coordinate is refit. -/
def checkNaturalWordIndexed {Native : Type*} [DecidableEq Native] [Fintype Native]
    (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (encode : WordVariable N J → Native)
    (supplied : Rows Native (Code N sample)) : Bool :=
  checkRows (project N Finset.univ)
    (renameRows encode (naturalWordRows N sample H common word)) supplied

/-- Literal native positions -> SAME shared original bank. LeftInverse is a
data/coordinate premise, not a desired native-law or emitted-row equality.
The complete final polynomial fibres are still supplied by the Boolean check. -/
theorem checked_natural_word_indexed {Native : Type*} [DecidableEq Native] [Fintype Native]
    (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (encode : WordVariable N J → Native)
    (decode : Native → WordVariable N J) (hleft : Function.LeftInverse decode encode)
    (supplied : Rows Native (Code N sample))
    (h : checkNaturalWordIndexed N sample H common word encode supplied = true)
    (b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E)
    (p : HybridProbabilities N) (dur : J → ℝ≥0) :
    value (readRows (project N Finset.univ) supplied b)
        (fun i => wordVariables N r (originalGamma p) dur (decode i)) =
      (((initializedWordLaw N sample H p common r dur word).map
        (projection N Finset.univ)) b).toReal := by
  have heq := checkRows_sound (project N Finset.univ)
    (renameRows encode (naturalWordRows N sample H common word)) supplied h b
  have evaluated := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ)
    (fun i => wordVariables N r (originalGamma p) dur (decode i))) heq
  rw [eval_polynomial, eval_polynomial] at evaluated
  have renamed_value :
      value (readRows (project N Finset.univ)
        (renameRows encode (naturalWordRows N sample H common word)) b)
        (fun i => wordVariables N r (originalGamma p) dur (decode i)) =
      value (readRows (project N Finset.univ) (naturalWordRows N sample H common word) b)
        (wordVariables N r (originalGamma p) dur) := by
    rw [← eval_polynomial, polynomial_read_renameRows,
      MvPolynomial.eval₂_rename, eval_polynomial]
    congr 1
    funext i
    exact congrArg (wordVariables N r (originalGamma p) dur) (hleft i)
  exact evaluated.symm.trans
    (renamed_value.trans (naturalWordRows_actual N sample H common r p dur word b))

end Astra.OriginalWordTableCertificate
