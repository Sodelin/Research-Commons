import RootBlobClaimInterfaces

/-!
# Edge-indexed full-claim interfaces

SOURCE-ONLY, UNELABORATED DRAFT, 22 October 2026, dot (OpenAI).
No compiler was run. Every declaration ending in "Claim" is a proposition
definition, NOT a theorem or an axiom.

This is the primary interface for the general image theorems. An explicit
finite edge type preserves parallel original edges, their distinct matrices
and their distinct inheritance weights. It does NOT merge parallel edges by
convexity, an invalid shortcut for the continuous-time K3P domain.

RootBlobClaimInterfaces supplies matrix classes, the concrete semidirected
quartet experiment, and convenient simple-graph examples. The two files
together specify the full claim and its remaining proof obligations.
-/

open scoped BigOperators
open RootBlobInterfaces

namespace RootBlobEdgeIndexed

universe u v w x

structure Network (V : Type u) (E : Type v) (O : Type w) where
  root : V
  observed : O → V
  source : E → V
  target : E → V
  rank : V → ℕ

def GraphAdmitted {V : Type u} {E : Type v} {O : Type w}
    (N : Network V E O) : Prop :=
  Function.Injective N.observed ∧
  (∀ o, N.observed o ≠ N.root) ∧
  (∀ e, N.rank (N.source e) < N.rank (N.target e)) ∧
  (∀ e, N.target e ≠ N.root) ∧
  (∀ v, v ≠ N.root → ∃ e, N.target e = v) ∧
  (∀ v, (∀ e, N.source e ≠ v) ↔ ∃ o, N.observed o = v)

noncomputable def WeightsAdmitted {V : Type u} {E : Type v} {O : Type w}
    [Fintype E] (N : Network V E O) (W : E → ℝ) : Prop := by
  classical
  exact (∀ e, 0 < W e) ∧
    (∀ v, v ≠ N.root → (∑ e, if N.target e = v then W e else 0) = 1)

/-- The original finite edge-indexed DAG factorization.
    A parallel edge remains a distinct summand with its own parameter. -/
noncomputable def assignmentMass {V : Type u} {E : Type v} {O : Type w}
    {S : Type x} [Fintype V] [DecidableEq V] [Fintype E]
    (N : Network V E O) (π : S → ℝ) (W : E → ℝ)
    (M : E → Mat S) (a : V → S) : ℝ :=
  π (a N.root) *
    (Finset.univ.erase N.root).prod
      (fun v => ∑ e,
        if N.target e = v then W e * M e (a (N.source e)) (a v) else 0)

noncomputable def observedLaw {V : Type u} {E : Type v} {O : Type w}
    {S : Type x} [Fintype V] [DecidableEq V] [Fintype E]
    [Fintype O] [Fintype S]
    (N : Network V E O) (π : S → ℝ) (W : E → ℝ)
    (M : E → Mat S) : (O → S) → ℝ := by
  classical
  exact fun z => ∑ a : V → S,
    if (∀ o, a (N.observed o) = z o)
    then assignmentMass N π W M a else 0

noncomputable def pairLaw {V : Type u} {E : Type v} {S : Type x}
    [Fintype V] [DecidableEq V] [Fintype E] [Fintype S]
    (N : Network V E (Fin 2)) (π : S → ℝ) (W : E → ℝ)
    (M : E → Mat S) : Mat S :=
  fun i j => observedLaw N π W M (fun k => if k = 0 then i else j)

noncomputable def openImage {V : Type u} {E : Type v} {S : Type x}
    [Fintype V] [DecidableEq V] [Fintype E] [Fintype S]
    (N : Network V E (Fin 2)) (W : E → ℝ)
    (H : Subgroup (Equiv.Perm S)) : Set (Mat S) :=
  {P | ∃ (π : S → ℝ) (M : E → Mat S),
    RootAdmitted H π ∧ (∀ e, OpenTransition H (M e)) ∧
    pairLaw N π W M = P}

def OpenImageClaim {V : Type u} {E : Type v} {S : Type x}
    [Fintype V] [DecidableEq V] [Fintype E] [Fintype S] [Nonempty S]
    (N : Network V E (Fin 2)) (W : E → ℝ)
    (H : Subgroup (Equiv.Perm S)) : Prop :=
  1 < Fintype.card S → GraphAdmitted N → WeightsAdmitted N W →
    openImage N W H = {P | PositiveInvariantPair H P}

def OpenRealizationClaim {V : Type u} {E : Type v} {S : Type x}
    [Fintype V] [DecidableEq V] [Fintype E] [Fintype S] [Nonempty S]
    (N : Network V E (Fin 2)) (W : E → ℝ)
    (H : Subgroup (Equiv.Perm S)) : Prop :=
  1 < Fintype.card S → GraphAdmitted N → WeightsAdmitted N W →
    ∀ P, PositiveInvariantPair H P →
      ∃ (π : S → ℝ) (M : E → Mat S),
        (∀ i, 0 < π i) ∧ RootAdmitted H π ∧
        (∀ e, OpenTransition H (M e)) ∧ pairLaw N π W M = P

def rootedFork : Network (Fin 3) (Fin 2) (Fin 2) where
  root := 0
  observed := ![1, 2]
  source := ![0, 0]
  target := ![1, 2]
  rank := fun v => if v = 0 then 0 else 1

def forkWeights : Fin 2 → ℝ := fun _ => 1

def RootForkContextClaim {V : Type u} {E : Type v}
    {S : Type x} {Z : Type w}
    [Fintype V] [DecidableEq V] [Fintype E]
    [Fintype S] [Nonempty S] [Fintype Z]
    (N : Network V E (Fin 2)) (W : E → ℝ)
    (H : Subgroup (Equiv.Perm S)) (Q : S → S → Z → ℝ) : Prop :=
  1 < Fintype.card S → GraphAdmitted N → WeightsAdmitted N W →
    ContextAdmitted Q →
    Set.image (fun P => context P Q) (openImage N W H) =
    Set.image (fun P => context P Q) (openImage rootedFork forkWeights H)

noncomputable def effectiveImage {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [Fintype E]
    (N : Network V E (Fin 2)) (W : E → ℝ)
    (T : Mat DNA → Prop) : Set (Mat DNA) :=
  {K | ∃ M : E → Mat DNA,
    (∀ e, T (M e)) ∧
    pairLaw N (fun _ => (1 : ℝ) / 4) W M = fun i j => K i j / 4}

def NucleotideImageClaim {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [Fintype E]
    (N : Network V E (Fin 2)) (W : E → ℝ)
    (model : NucleotideModel) : Prop :=
  GraphAdmitted N → WeightsAdmitted N W →
    effectiveImage N W (NucleotideTransition model) =
      {K | NucleotideTransition model K ∧ PositiveMatrix K}

def CT2StrictImageClaim {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [Fintype E]
    (N : Network V E (Fin 2)) (W : E → ℝ) : Prop :=
  GraphAdmitted N → WeightsAdmitted N W →
    effectiveImage N W CT2Strict = {K | CT2Strict K}

def CT3RealizationClaim {V : Type u} {E : Type v}
    [Fintype V] [DecidableEq V] [Fintype E]
    (N : Network V E (Fin 2)) (W : E → ℝ) : Prop :=
  GraphAdmitted N → WeightsAdmitted N W →
    {K | CT3Strict K} ⊆ effectiveImage N W CT3Strict

/-- Original eight-edge rooted component, no vertex/edge identifications. -/
def twoReticulationBlob : Network (Fin 7) (Fin 8) (Fin 2) where
  root := 0
  observed := ![5, 6]
  source := ![0, 0, 1, 1, 2, 2, 3, 4]
  target := ![1, 2, 3, 4, 3, 4, 5, 6]
  rank := fun v =>
    if v = 0 then 0 else
    if v = 1 ∨ v = 2 then 1 else
    if v = 3 ∨ v = 4 then 2 else 3

def halfWeights : Fin 8 → ℝ :=
  ![1, 1, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1, 1]

def CT2BoundaryBlobClaim (W : Fin 8 → ℝ) : Prop :=
  WeightsAdmitted twoReticulationBlob W →
    effectiveImage twoReticulationBlob W CT2PositiveEntries = {K | CT2Strict K}

def CT2ForkImageClaim : Prop :=
  effectiveImage rootedFork forkWeights CT2PositiveEntries =
    {K | CT2PositiveEntries K}

def CT3ForkImageClaim : Prop :=
  effectiveImage rootedFork forkWeights CT3Strict = {K | CT3Strict K}

def CT3ForkStrictInclusionClaim : Prop :=
  effectiveImage rootedFork forkWeights CT3Strict ⊆
    effectiveImage twoReticulationBlob halfWeights CT3Strict ∧
  effectiveImage rootedFork forkWeights CT3Strict ≠
    effectiveImage twoReticulationBlob halfWeights CT3Strict

def CT2ObservableBoundaryClaim : Prop :=
  CT2PositiveEntries ct2BoundaryMatrix ∧
  ct2BoundaryMatrix ∈ effectiveImage rootedFork forkWeights CT2PositiveEntries ∧
  QuartetSourceExclusionClaim CT2PositiveEntries ct2BoundaryMatrix

def CT3ObservableMixtureClaim : Prop :=
  ct3MixtureMatrix ∈ effectiveImage twoReticulationBlob halfWeights CT3Strict ∧
  QuartetEdgeExclusionClaim CT3Strict ct3MixtureMatrix

end RootBlobEdgeIndexed
