import Mathlib

/-!
# Root-blob full-claim interfaces

SOURCE-ONLY, UNELABORATED DRAFT, 22 October 2026, dot (OpenAI).
No compiler was run. This file contains concrete finite probability semantics
and named proposition-valued proof obligations. A definition ending in "Claim"
is NOT a proved theorem. There are no axioms, sorry terms, or admitted results.
Only the final elementary context-congruence lemma has a proof term, which has
also not been elaborated. No full formal-verification claim is made.

The mathematical sources and exact remaining semantic bridges are in
FORMALIZATION-HANDOFF.md. In particular, the semidirected path expression below
must still be connected formally to the source paper's graph conventions.
-/

open scoped BigOperators

namespace RootBlobInterfaces

universe u v w

abbrev Mat (S : Type w) := S → S → ℝ

structure Network (V : Type u) (O : Type v) where
  root : V
  observed : O → V
  edge : V → V → Bool
  rank : V → ℕ

/-- Concrete finite rooted DAG contract, with exactly the observed sinks. -/
def GraphAdmitted {V : Type u} {O : Type v} (N : Network V O) : Prop :=
  Function.Injective N.observed ∧
  (∀ o, N.observed o ≠ N.root) ∧
  (∀ u v, N.edge u v = true → N.rank u < N.rank v) ∧
  (∀ u, N.edge u N.root = false) ∧
  (∀ v, v ≠ N.root → ∃ u, N.edge u v = true) ∧
  (∀ v, (∀ z, N.edge v z = false) ↔ ∃ o, N.observed o = v)

/-- Every original incoming edge has positive prescribed probability.
    Nonedges have weight zero; a one-parent vertex necessarily has weight one. -/
def WeightsAdmitted {V : Type u} {O : Type v} [Fintype V]
    (N : Network V O) (W : V → V → ℝ) : Prop :=
  (∀ u v, N.edge u v = true → 0 < W u v) ∧
  (∀ u v, N.edge u v = false → W u v = 0) ∧
  (∀ v, v ≠ N.root → (∑ u, W u v) = 1)

/-- The actual displayed-tree DAG factorization, not an abstract port oracle. -/
noncomputable def assignmentMass {V : Type u} {O : Type v} {S : Type w}
    [Fintype V] [DecidableEq V] [Fintype S]
    (N : Network V O) (π : S → ℝ) (W : V → V → ℝ)
    (M : V → V → Mat S) (a : V → S) : ℝ :=
  π (a N.root) *
    (Finset.univ.erase N.root).prod
      (fun v => ∑ u, W u v * M u v (a u) (a v))

noncomputable def observedLaw {V : Type u} {O : Type v} {S : Type w}
    [Fintype V] [DecidableEq V] [Fintype O] [Fintype S]
    (N : Network V O) (π : S → ℝ) (W : V → V → ℝ)
    (M : V → V → Mat S) : (O → S) → ℝ := by
  classical
  exact fun z => ∑ a : V → S,
    if (∀ o, a (N.observed o) = z o)
    then assignmentMass N π W M a else 0

noncomputable def pairLaw {V : Type u} {S : Type w}
    [Fintype V] [DecidableEq V] [Fintype S]
    (N : Network V (Fin 2)) (π : S → ℝ) (W : V → V → ℝ)
    (M : V → V → Mat S) : Mat S :=
  fun i j => observedLaw N π W M (fun k => if k = 0 then i else j)

def Probability {S : Type w} [Fintype S] (π : S → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ (∑ i, π i) = 1

def StrictStochastic {S : Type w} [Fintype S] (M : Mat S) : Prop :=
  (∀ i j, 0 < M i j) ∧ (∀ i, (∑ j, M i j) = 1)

def Invariant {S : Type w} (H : Subgroup (Equiv.Perm S))
    (π : S → ℝ) : Prop :=
  ∀ h : H, ∀ i, π (h.val i) = π i

def Equivariant {S : Type w} (H : Subgroup (Equiv.Perm S))
    (M : Mat S) : Prop :=
  ∀ h : H, ∀ i j, M (h.val i) (h.val j) = M i j

def RootAdmitted {S : Type w} [Fintype S]
    (H : Subgroup (Equiv.Perm S)) (π : S → ℝ) : Prop :=
  Probability π ∧ Invariant H π

def OpenTransition {S : Type w} [Fintype S]
    (H : Subgroup (Equiv.Perm S)) (M : Mat S) : Prop :=
  StrictStochastic M ∧ Equivariant H M

def PositiveInvariantPair {S : Type w} [Fintype S]
    (H : Subgroup (Equiv.Perm S)) (P : Mat S) : Prop :=
  (∀ i j, 0 < P i j) ∧
  (∑ i, ∑ j, P i j) = 1 ∧ Equivariant H P

noncomputable def openImage {V : Type u} {S : Type w}
    [Fintype V] [DecidableEq V] [Fintype S]
    (N : Network V (Fin 2)) (W : V → V → ℝ)
    (H : Subgroup (Equiv.Perm S)) : Set (Mat S) :=
  {P | ∃ (π : S → ℝ) (M : V → V → Mat S),
    RootAdmitted H π ∧
    (∀ u v, N.edge u v = true → OpenTransition H (M u v)) ∧
    pairLaw N π W M = P}

/-- Theorem E's complete source/observation/image obligation. UNPROVED. -/
def OpenImageClaim {V : Type u} {S : Type w}
    [Fintype V] [DecidableEq V] [Fintype S] [Nonempty S]
    (N : Network V (Fin 2)) (W : V → V → ℝ)
    (H : Subgroup (Equiv.Perm S)) : Prop :=
  1 < Fintype.card S → GraphAdmitted N → WeightsAdmitted N W →
    openImage N W H = {P | PositiveInvariantPair H P}

/-- Strong constructive reverse direction, retaining a strictly positive root.
    This also supplies the positive-root-distribution variant. UNPROVED. -/
def OpenRealizationClaim {V : Type u} {S : Type w}
    [Fintype V] [DecidableEq V] [Fintype S] [Nonempty S]
    (N : Network V (Fin 2)) (W : V → V → ℝ)
    (H : Subgroup (Equiv.Perm S)) : Prop :=
  1 < Fintype.card S → GraphAdmitted N → WeightsAdmitted N W →
    ∀ P, PositiveInvariantPair H P →
      ∃ (π : S → ℝ) (M : V → V → Mat S),
        (∀ i, 0 < π i) ∧ RootAdmitted H π ∧
        (∀ u v, N.edge u v = true → OpenTransition H (M u v)) ∧
        pairLaw N π W M = P

def rootedFork : Network (Fin 3) (Fin 2) where
  root := 0
  observed := fun o => if o = 0 then 1 else 2
  edge := fun u v => decide (u = 0 ∧ (v = 1 ∨ v = 2))
  rank := fun v => if v = 0 then 0 else 1

def forkWeights : Fin 3 → Fin 3 → ℝ :=
  fun u v => if u = 0 ∧ (v = 1 ∨ v = 2) then 1 else 0

noncomputable def context {S : Type w} {Z : Type v} [Fintype S]
    (P : Mat S) (Q : S → S → Z → ℝ) : Z → ℝ :=
  fun z => ∑ i, ∑ j, P i j * Q i j z

def ContextAdmitted {S : Type w} {Z : Type v} [Fintype Z]
    (Q : S → S → Z → ℝ) : Prop :=
  ∀ i j, (∀ z, 0 ≤ Q i j z) ∧ (∑ z, Q i j z) = 1

/-- Theorem E-root, after the ancestral-DAG/exterior-kernel bridge. UNPROVED. -/
def RootForkContextClaim {V : Type u} {S : Type w} {Z : Type v}
    [Fintype V] [DecidableEq V] [Fintype S] [Nonempty S] [Fintype Z]
    (N : Network V (Fin 2)) (W : V → V → ℝ)
    (H : Subgroup (Equiv.Perm S)) (Q : S → S → Z → ℝ) : Prop :=
  1 < Fintype.card S → GraphAdmitted N → WeightsAdmitted N W → ContextAdmitted Q →
    Set.image (fun P => context P Q) (openImage N W H) =
    Set.image (fun P => context P Q) (openImage rootedFork forkWeights H)

abbrev DNA := ZMod 2 × ZMod 2

def character (g x : DNA) : ℝ :=
  if g.1 * x.1 + g.2 * x.2 = 0 then 1 else -1

noncomputable def fourier (p : DNA → ℝ) (g : DNA) : ℝ :=
  ∑ x, p x * character g x

noncomputable def eigen (M : Mat DNA) (g : DNA) : ℝ :=
  fourier (fun x => M 0 x) g

inductive NucleotideModel where
  | jc | k2p | k3p
  deriving DecidableEq

def NucleotideTransition (model : NucleotideModel) (M : Mat DNA) : Prop :=
  ∃ p : DNA → ℝ,
    Probability p ∧
    (∀ i j, M i j = p (j - i)) ∧
    (∀ g, g ≠ 0 → 0 < fourier p g ∧ fourier p g < 1) ∧
    (match model with
     | .jc => ∀ g, g ≠ 0 → fourier p g = fourier p (1, 0)
     | .k2p => fourier p (1, 0) = fourier p (0, 1)
     | .k3p => True)

def PositiveMatrix {S : Type w} (M : Mat S) : Prop := ∀ i j, 0 < M i j

noncomputable def effectiveImage {V : Type u}
    [Fintype V] [DecidableEq V] (N : Network V (Fin 2))
    (W : V → V → ℝ) (T : Mat DNA → Prop) : Set (Mat DNA) :=
  {K | ∃ M : V → V → Mat DNA,
    (∀ u v, N.edge u v = true → T (M u v)) ∧
    pairLaw N (fun _ => (1 : ℝ) / 4) W M = fun i j => K i j / 4}

/-- PROOF.md Theorem 4.1, with its full graph and parameter quantifiers. UNPROVED. -/
def NucleotideImageClaim {V : Type u} [Fintype V] [DecidableEq V]
    (N : Network V (Fin 2)) (W : V → V → ℝ)
    (model : NucleotideModel) : Prop :=
  GraphAdmitted N → WeightsAdmitted N W →
    effectiveImage N W (NucleotideTransition model) =
      {K | NucleotideTransition model K ∧ PositiveMatrix K}

def jcMatrix (t : ℝ) : Mat DNA :=
  fun i j => t * (if i = j then 1 else 0) + (1 - t) / 4

noncomputable def matMul {S : Type w} [Fintype S]
    (A B : Mat S) : Mat S :=
  fun i j => ∑ k, A i k * B k j

noncomputable def matProduct {S : Type w} [Fintype S] [DecidableEq S]
    (L : List (Mat S)) : Mat S :=
  L.foldl matMul (fun i j => if i = j then 1 else 0)

/-- Exact original semidirected path formula. Edge order:
    a-u, b-v, x-a, x-b, y-a, y-b, x-y.
    The source-to-formula graph bridge is a remaining formal obligation. -/
noncomputable def semidirectedCore (α β : ℝ)
    (M : Fin 7 → Mat DNA) : Mat DNA :=
  let Kxx := matProduct [M 0, M 2, M 3, M 1]
  let Kyy := matProduct [M 0, M 4, M 5, M 1]
  let Kxy := matProduct [M 0, M 2, M 6, M 5, M 1]
  let Kyx := matProduct [M 0, M 4, M 6, M 3, M 1]
  fun i j =>
    α * β * Kxx i j + (1 - α) * (1 - β) * Kyy i j +
    α * (1 - β) * Kxy i j + (1 - α) * β * Kyx i j

noncomputable def quartetLaw (K : Mat DNA) (B : Fin 4 → Mat DNA) :
    (Fin 4 → DNA) → ℝ :=
  fun z => ∑ i, ∑ j,
    (K i j / 4) * B 0 i (z 0) * B 1 i (z 1) *
      B 2 j (z 2) * B 3 j (z 3)

def boundaryIncrement (x : DNA) : ℝ :=
  if x = 0 then 3 / 5 else if x = (1, 1) then 0 else 1 / 5

def boundaryMatrix : Mat DNA := fun i j => boundaryIncrement (j - i)

noncomputable def boundaryQuartet : (Fin 4 → DNA) → ℝ :=
  quartetLaw boundaryMatrix (fun _ => jcMatrix (1 / 2))

/-- PROOF.md Theorem 6.1, including all rival pendant parameters. UNPROVED.
    The target's admissible pendant-root realization is a separate graph lemma. -/
def SemidirectedQuartetObstructionClaim (model : NucleotideModel) : Prop :=
  (model = .k2p ∨ model = .k3p) →
    NucleotideTransition model boundaryMatrix ∧
    ∀ (α β : ℝ) (M : Fin 7 → Mat DNA) (B : Fin 4 → Mat DNA),
      0 < α → α < 1 → 0 < β → β < 1 →
      (∀ e, NucleotideTransition model (M e)) →
      (∀ e, NucleotideTransition model (B e)) →
      quartetLaw (semidirectedCore α β M) B ≠ boundaryQuartet

/-- The fixed two-reticulation rooted component, in original vertices
    r=0,x=1,y=2,a=3,b=4,u=5,v=6. -/
def twoReticulationBlob : Network (Fin 7) (Fin 2) where
  root := 0
  observed := fun o => if o = 0 then 5 else 6
  edge := fun u v => decide (
    (u = 0 ∧ (v = 1 ∨ v = 2)) ∨
    ((u = 1 ∨ u = 2) ∧ (v = 3 ∨ v = 4)) ∨
    (u = 3 ∧ v = 5) ∨ (u = 4 ∧ v = 6))
  rank := fun v =>
    if v = 0 then 0 else
    if v = 1 ∨ v = 2 then 1 else
    if v = 3 ∨ v = 4 then 2 else 3

def halfWeights : Fin 7 → Fin 7 → ℝ :=
  fun u v => if twoReticulationBlob.edge u v = true
    then (if v = 3 ∨ v = 4 then 1 / 2 else 1) else 0

/-- The rate-cone interpretation requires proof via the exact generator formula. -/
def CT2Strict (M : Mat DNA) : Prop :=
  NucleotideTransition .k2p M ∧ eigen M (1, 0) ^ 2 < eigen M (1, 1)

def CT2PositiveEntries (M : Mat DNA) : Prop :=
  NucleotideTransition .k2p M ∧ eigen M (1, 0) ^ 2 ≤ eigen M (1, 1)

def CT3Strict (M : Mat DNA) : Prop :=
  NucleotideTransition .k3p M ∧
    eigen M (0, 1) * eigen M (1, 1) < eigen M (1, 0) ∧
    eigen M (1, 0) * eigen M (1, 1) < eigen M (0, 1) ∧
    eigen M (1, 0) * eigen M (0, 1) < eigen M (1, 1)

def CT2StrictImageClaim {V : Type u} [Fintype V] [DecidableEq V]
    (N : Network V (Fin 2)) (W : V → V → ℝ) : Prop :=
  GraphAdmitted N → WeightsAdmitted N W →
    effectiveImage N W CT2Strict = {K | CT2Strict K}

def CT2BoundaryBlobClaim (W : Fin 7 → Fin 7 → ℝ) : Prop :=
  WeightsAdmitted twoReticulationBlob W →
    effectiveImage twoReticulationBlob W CT2PositiveEntries = {K | CT2Strict K}

def CT3ForkStrictInclusionClaim : Prop :=
  effectiveImage rootedFork forkWeights CT3Strict ⊆
    effectiveImage twoReticulationBlob halfWeights CT3Strict ∧
  effectiveImage rootedFork forkWeights CT3Strict ≠
    effectiveImage twoReticulationBlob halfWeights CT3Strict

def CT2ForkImageClaim : Prop :=
  effectiveImage rootedFork forkWeights CT2PositiveEntries =
    {K | CT2PositiveEntries K}

def CT3ForkImageClaim : Prop :=
  effectiveImage rootedFork forkWeights CT3Strict = {K | CT3Strict K}

def CT3RealizationClaim {V : Type u} [Fintype V] [DecidableEq V]
    (N : Network V (Fin 2)) (W : V → V → ℝ) : Prop :=
  GraphAdmitted N → WeightsAdmitted N W →
    {K | CT3Strict K} ⊆ effectiveImage N W CT3Strict

def ct2BoundaryMatrix : Mat DNA :=
  fun i j =>
    if j - i = 0 then 9 / 16 else
    if j - i = (1, 1) then 1 / 16 else 3 / 16

def ct3MixtureMatrix : Mat DNA :=
  fun i j =>
    if j - i = 0 then 511 / 1000 else
    if j - i = (1, 1) then 61 / 1000 else 214 / 1000

/-- Full leaf-observable source exclusion, not just a port mismatch. -/
def QuartetSourceExclusionClaim (T : Mat DNA → Prop) (target : Mat DNA) : Prop :=
  ∀ (α β : ℝ) (M : Fin 7 → Mat DNA) (B : Fin 4 → Mat DNA),
    0 < α → α < 1 → 0 < β → β < 1 →
    (∀ e, T (M e)) → (∀ e, T (B e)) →
    quartetLaw (semidirectedCore α β M) B ≠
      quartetLaw target (fun _ => jcMatrix (1 / 2))

/-- Excludes all effective comparison edges, allowing arbitrary pendants. -/
def QuartetEdgeExclusionClaim (T : Mat DNA → Prop) (target : Mat DNA) : Prop :=
  ∀ (K : Mat DNA) (B : Fin 4 → Mat DNA),
    T K → (∀ e, T (B e)) →
    quartetLaw K B ≠ quartetLaw target (fun _ => jcMatrix (1 / 2))

def CT2ObservableBoundaryClaim : Prop :=
  CT2PositiveEntries ct2BoundaryMatrix ∧
  ct2BoundaryMatrix ∈ effectiveImage rootedFork forkWeights CT2PositiveEntries ∧
  QuartetSourceExclusionClaim CT2PositiveEntries ct2BoundaryMatrix

def CT3ObservableMixtureClaim : Prop :=
  ct3MixtureMatrix ∈ effectiveImage twoReticulationBlob halfWeights CT3Strict ∧
  QuartetEdgeExclusionClaim CT3Strict ct3MixtureMatrix

/-- An elementary consequence of equality, NOT a proof of any image claim. -/
theorem context_congr {S : Type w} {Z : Type v} [Fintype S]
    (P R : Mat S) (Q : S → S → Z → ℝ) (h : P = R) :
    context P Q = context R Q :=
  congrArg (fun K => context K Q) h

end RootBlobInterfaces
