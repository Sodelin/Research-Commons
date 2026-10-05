import guards.NanuqActualLocalChoiceCapGraph

set_option debug.skipKernelTC false

/-! Actual local-choice factorization of the DISTINCT displayed quartet set
and mean. Surjectivity removes exterior choices without weighting their
multiplicities. The local evaluator has a literal capped-graph resolution spec. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
open Nanuq.Quartet
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable instance originalBlobSwitchingFintype (b : N.graph.Blob) :
    Fintype (N.OriginalBlobSwitching b) :=
  Fintype.ofSurjective (fun S : N.Switching => S.restrictOriginalBlobSwitching b)
    (N.actual_blob_switching_restriction_surjective b)

noncomputable def actualLocalPortResolve (q : Fin 4 ↪ X) (b : N.graph.Blob)
    (L : N.OriginalBlobSwitching b) : Resolution :=
  (L.extendOriginalBlobSwitching (Classical.choice (inferInstance : Nonempty N.Switching))).resolve q

theorem actualLocalPortResolve_spec (q : Fin 4 ↪ X) (b : N.graph.Blob)
    (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (L : N.OriginalBlobSwitching b) (r : Resolution) :
    L.localCappedGraph.Resolves (fun i => Sum.inr (N.blobProjection b hb (q i))) r ↔
      r = N.actualLocalPortResolve q b L := by
  let S0 : N.Switching := Classical.choice inferInstance
  have h := (L.extendOriginalBlobSwitching S0).actual_local_choice_cap_resolution_iff q b hb hinj r
  rw [L.restriction_extension_roundtrip S0] at h
  exact h

theorem actual_resolve_factors_local_choice (q : Fin 4 ↪ X) (b : N.graph.Blob)
    (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) (S : N.Switching) :
    S.resolve q = N.actualLocalPortResolve q b (S.restrictOriginalBlobSwitching b) := by
  apply (N.actualLocalPortResolve_spec q b hb hinj (S.restrictOriginalBlobSwitching b) (S.resolve q)).mp
  exact (S.actual_local_choice_cap_resolution_iff q b hb hinj (S.resolve q)).mpr rfl

theorem actual_four_port_local_choice_distinct_set_and_mean
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) :
    N.rawDisplayedQuartets q = displayed (N.actualLocalPortResolve q b) ∧
      N.rawQuartetMean q = sourceMean (N.actualLocalPortResolve q b) := by
  have hfun : (fun S : N.Switching => S.resolve q) =
      N.actualLocalPortResolve q b ∘ (fun S : N.Switching => S.restrictOriginalBlobSwitching b) := by
    funext S
    exact N.actual_resolve_factors_local_choice q b hb hinj S
  constructor
  · unfold rawDisplayedQuartets
    rw [hfun,displayed_comp_surjective (fun S : N.Switching => S.restrictOriginalBlobSwitching b)
      (N.actual_blob_switching_restriction_surjective b)]
  · unfold rawQuartetMean
    rw [hfun,sourceMean_comp_surjective (fun S : N.Switching => S.restrictOriginalBlobSwitching b)
      (N.actual_blob_switching_restriction_surjective b)]

theorem actual_local_choice_port_representative_independent
    (q q' : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (hports : ∀ i, N.blobProjection b hb (q i) = N.blobProjection b hb (q' i))
    (L : N.OriginalBlobSwitching b) :
    N.actualLocalPortResolve q b L = N.actualLocalPortResolve q' b L :=
  (L.extendOriginalBlobSwitching (Classical.choice (inferInstance : Nonempty N.Switching))).actual_four_port_resolve_invariant
    q q' b hb hinj hports
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_four_port_local_choice_distinct_set_and_mean
#print axioms Nanuq.Source.RootedBinary.actualLocalPortResolve_spec
