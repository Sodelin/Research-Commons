import G1NonrootBigonKernel
import G7ProgramRelabelling
import G7CompletedUnrankedRelabelling

/-!
Contributor: Codex Lean reuse, 2026-10-10. PROPOSAL, not yet kernel checked.

This instantiates the accepted original source relabelling at the two distinct
parallel parent occurrences of an actual NonrootBigon. The vertex and Copy
labels are fixed. The source, target, root, named taxa and original register
labels are consequently unchanged. The two parent occurrence names and their
positive rate entries are explicitly exchanged; the transported Boolean parent
labels themselves retain the inherited order.

The final theorem compares actual full forest/register epoch laws after two
constant-current-owner pulses, not fitted count kernels. It applies to arbitrary
admitted entering Codes whose live owners are at the original hybrid, including
old carried genealogy and noncanonical dead snapshot fields: the actual pulse
encodes its output before transport.

This is the population-name transport interface for a later COMMON
factorization. It asserts no Bernoulli mixture for a fixed entering Code, which
already contains a stored bit. The natural COMMON mixture additionally requires
the original naturally drawn private seed, its marginalization, and an actual
NoPrivateWordRead prefix (and a no-read continuation when erasing that seed).
Those premises have existing accepted providers in PrivateSeedHistoryFactorization
and ActualUnusedSeedConditioning. No natural gamma is refitted here; in the
original convention gamma is the mass of true/parent1.
-/

namespace GProgram.G6.OriginalParallelArmTransport

set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open G1NonrootBigonKernel G1ContextualForestReplacement
open GProgram.G7.OriginalRelabelling GProgram.G7.SnapshotRelabelling
open GProgram.G7.ProgramRelabelling
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- The actual two original incoming occurrences, not their endpoint quotient. -/
def edgeSwap (N : RootedBinary V E X) (B : NonrootBigon N) : E ≃ E :=
  Equiv.swap B.parents.parent0 B.parents.parent1

theorem arm_swap_source (N : RootedBinary V E X) (B : NonrootBigon N) (e : E) :
    N.graph.source (edgeSwap N B e) = N.graph.source e := by
  apply Equiv.apply_swap_eq_self
  exact (B.arm_sources false).trans (B.arm_sources true).symm

theorem arm_swap_target (N : RootedBinary V E X) (B : NonrootBigon N) (e : E) :
    N.graph.target (edgeSwap N B e) = N.graph.target e := by
  apply Equiv.apply_swap_eq_self
  exact B.parents.target0.trans B.parents.target1.symm

private theorem edgeGraph_eq {G H : EdgeGraph V E}
    (hs : G.source = H.source) (ht : G.target = H.target) : G = H := by
  cases G
  cases H
  cases hs
  cases ht
  rfl

private theorem rootedBinary_eq {N M : RootedBinary V E X}
    (hg : N.graph = M.graph) (hr : N.root = M.root) (hl : N.leaf = M.leaf) : N = M := by
  cases N
  cases M
  cases hg
  cases hr
  cases hl
  rfl

/-- The parallel-arm permutation is an automorphism of this actual source;
no replacement graph or additional admission premise is supplied. -/
theorem arm_network_eq (N : RootedBinary V E X) (B : NonrootBigon N) :
    network N (Equiv.refl V) (edgeSwap N B) = N := by
  apply rootedBinary_eq
  · apply edgeGraph_eq
    · funext e
      change N.graph.source (edgeSwap N B e) = N.graph.source e
      exact arm_swap_source N B e
    · funext e
      change N.graph.target (edgeSwap N B e) = N.graph.target e
      exact arm_swap_target N B e
  · rfl
  · rfl

/-- The Boolean index is transported unchanged; its original occurrence name
is exchanged. This explicitly distinguishes the two parallel IDs. -/
theorem arm_parent_occurrence (N : RootedBinary V E X) (B : NonrootBigon N) (b : Bool) :
    (parents N (Equiv.refl V) (edgeSwap N B) B.parents).parent b =
      B.parents.parent (!b) := by
  cases b <;> simp [parents, edgeSwap, GProgram.G2.OriginalHybridParents.parent]

theorem arm_rate_occurrence (N : RootedBinary V E X) (B : NonrootBigon N)
    (r : PositivePairRates E) (b : Bool) :
    (rates (edgeSwap N B) r).edge (B.parents.parent (!b)) =
      r.edge (B.parents.parent b) := by
  cases b <;> simp [rates, edgeSwap, GProgram.G2.OriginalHybridParents.parent]

private noncomputable def castCode {N M : RootedBinary V E X}
    {sample : Copy → X} (h : M = N) (s : Code M sample) : Code N sample :=
  Eq.mp (congrArg (fun K : RootedBinary V E X => Code K sample) h) s

private theorem castCode_val {N M : RootedBinary V E X}
    {sample : Copy → X} (h : M = N) (s : Code M sample) :
    (castCode h s).val = s.val := by
  cases h
  rfl

private theorem castCode_time {N M : RootedBinary V E X}
    {sample : Copy → X} (h : M = N) (r : PositivePairRates E)
    (t : ℝ≥0) (s : Code M sample) :
    (sourceTimeKernel M r t s).map (castCode h) =
      sourceTimeKernel N r t (castCode h s) := by
  cases h
  change (sourceTimeKernel N r t s).map id = sourceTimeKernel N r t s
  exact PMF.map_id _

/-- Actual snapshot relabelling, returned to the equal original source. -/
noncomputable def armCode (N : RootedBinary V E X) (B : NonrootBigon N)
    {sample : Copy → X} (s : Code N sample) : Code N sample :=
  castCode (arm_network_eq N B) (code N (Equiv.refl V) (edgeSwap N B) s)

theorem armCode_val (N : RootedBinary V E X) (B : NonrootBigon N)
    {sample : Copy → X} (s : Code N sample) :
    (armCode N B s).val = snapshot (Equiv.refl V) (edgeSwap N B) s.val :=
  castCode_val (arm_network_eq N B) _

/-- Every original register label and the entire rooted labelled unranked
forest are retained, including the genealogy carried into this component. -/
theorem armCode_full_forest_register (N : RootedBinary V E X) (B : NonrootBigon N)
    {sample : Copy → X} (s : Code N sample) :
    ((state (armCode N B s)).register, rootForest N (armCode N B s)) =
      ((state s).register, rootForest N s) := by
  change ((decodeSnapshot N.root (armCode N B s).val).register,
    (decodeSnapshot N.root (armCode N B s).val).live.image
      (fun l => UnifiedLean.Source.UnrankedGenealogyObservation.toUnranked
        ((decodeSnapshot N.root (armCode N B s).val).genealogy l))) = _
  rw [armCode_val]
  rfl

/-- The actual pulse removes dead encoding variants. Hence all-at-hybrid
source admission suffices; no encoded-input hypothesis is added. -/
theorem armCode_constant_pulse (N : RootedBinary V E X) (B : NonrootBigon N)
    {sample : Copy → X} (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    (b : Bool) :
    armCode N B (pulseCode B.parents s (fun _ => b)) =
      pulseCode B.parents s (fun _ => !b) := by
  apply Subtype.ext
  rw [armCode_val]
  apply Snapshot.ext
  · rfl
  · rfl
  · rfl
  · funext l
    by_cases hl : l ∈ (state s).live
    · have hloc := hinput l hl
      cases b <;> simp [snapshot, pulseCode, admittedCode, encodeSnapshot,
        pulse, transport, hl, hloc, edgeSwap,
        GProgram.G7.SourceStateRelabelling.location,
        GProgram.G2.OriginalHybridParents.parent]
    · simp [snapshot, pulseCode, admittedCode, encodeSnapshot, pulse, transport, hl]
  · rfl

theorem armCode_time_kernel (N : RootedBinary V E X) (B : NonrootBigon N)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (armCode N B) =
      sourceTimeKernel N (rates (edgeSwap N B) r) t (armCode N B s) := by
  calc
    (sourceTimeKernel N r t s).map (armCode N B) =
        ((sourceTimeKernel N r t s).map (code N (Equiv.refl V) (edgeSwap N B))).map
          (castCode (arm_network_eq N B)) := by
      rw [PMF.map_comp]
      rfl
    _ = (sourceTimeKernel (network N (Equiv.refl V) (edgeSwap N B))
        (rates (edgeSwap N B) r) t (code N (Equiv.refl V) (edgeSwap N B) s)).map
          (castCode (arm_network_eq N B)) :=
      congrArg (PMF.map (castCode (arm_network_eq N B)))
        (time_kernel N (Equiv.refl V) (edgeSwap N B) r t s)
    _ = sourceTimeKernel N (rates (edgeSwap N B) r) t (armCode N B s) :=
      castCode_time (arm_network_eq N B) (rates (edgeSwap N B) r) t _

/-- Exact full-FKey/register port interface for the two original parallel
populations. This is arm-conditional; natural COMMON seed marginalization is
an additional, separately supplied source operation, never a fixed-Code claim. -/
theorem actual_parallel_arm_full_forest_transport
    (N : RootedBinary V E X) (B : NonrootBigon N) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    (b : Bool) :
    (sourceTimeKernel N r t (pulseCode B.parents s (fun _ => b))).map
      (fun d => ((state d).register, rootForest N d)) =
    (sourceTimeKernel N (rates (edgeSwap N B) r) t
      (pulseCode B.parents s (fun _ => !b))).map
      (fun d => ((state d).register, rootForest N d)) := by
  have h := congrArg
    (PMF.map (fun d : Code N sample => ((state d).register, rootForest N d)))
    (armCode_time_kernel N B r t (pulseCode B.parents s (fun _ => b)))
  rw [PMF.map_comp, armCode_constant_pulse N B s hinput b] at h
  have hf :
      (fun d : Code N sample => ((state d).register, rootForest N d)) ∘ armCode N B =
      (fun d : Code N sample => ((state d).register, rootForest N d)) := by
    funext d
    exact armCode_full_forest_register N B d
  rw [hf] at h
  exact h

#print axioms arm_network_eq
#print axioms arm_parent_occurrence
#print axioms armCode_constant_pulse
#print axioms actual_parallel_arm_full_forest_transport

end GProgram.G6.OriginalParallelArmTransport
