import RootBlobForkIdentification

/-!
# Full original-class maximal-root-blob endpoint
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No execution, elaboration or kernel verification.

Every graph obligation is included in the conclusion, rather than inferred
from a rank-free model-image equality. The original binary/simple/root-LSA
class is preserved, as are original leaf labels and original surviving edge
occurrences and inheritance weights. This does NOT instantiate the broader
literal root-trapping 2-sub-blob definition or a semidirected root lift.
-/

open RootBlobInterfaces RootBlobEdgeIndexed RootBlobBoundaryGraph
open RootBlobMaximalSource RootBlobBinaryReplacement RootBlobForkIdentification
namespace RootBlobMaximalEndpoint
universe u v w x
variable {S : Type u} [Fintype S] [Nonempty S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable (G : Network V E O)

/-- The full selected maximal-root-blob claim for all strictly positive
H-equivariant stochastic matrices, free independent edge matrices, a freely
varying invariant root, and fixed positive normalized original inheritance.

The proof does not require the original two boundary sources to be internal
sinks. The intermediate ports are actually constructed, then actually
suppressed through exact two-directional free-edge factorization.
-/
theorem maximal_root_blob_full
    (B : MaximalRootTwoBlob G) (hG : GraphAdmitted G)
    (hB : BinaryAdmission G) (hNP : NoParallel G) (hLSA : RootLSA G)
    (W : E → ℝ) (hW : WeightsAdmitted G W)
    (H : Subgroup (Equiv.Perm S)) (hS : 1 < Fintype.card S) :
    let R := B.region hG hB
    GraphAdmitted R.replacement ∧ BinaryAdmission R.replacement ∧
    NoParallel R.replacement ∧ RootLSA R.replacement ∧
    WeightsAdmitted R.replacement (R.replacementWeights W) ∧
    RootBlobFullModel.modelImage G W H =
      RootBlobFullModel.modelImage R.replacement (R.replacementWeights W) H := by
  let R := B.region hG hB
  refine ⟨R.replacement_admitted hG, R.replacement_binary hG hB,
    maximal_replacement_noParallel B hG hB hNP, R.replacement_rootLSA hG hLSA,
    R.replacement_weights_admitted W hW, ?_⟩
  exact R.modelImage_eq_replacement hG W hW H hS

end RootBlobMaximalEndpoint
