import RootBlobRetainedPortModel
import RootBlobBinaryReplacement

/-!
# From the original maximal binary root blob to the direct port contract
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler/kernel verification.

The original maximal/root/binary hypotheses are kept. An actual terminal
boundary vertex is derived by finite rank maximality, not supplied as an
extra source assumption. The other port need not be terminal. Its two
original cut matrices remain in the exterior subtype of the final theorem.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobEdgeIndexed RootBlobBoundaryGraph
open RootBlobMaximalSource RootBlobBinaryReplacement
open RootBlobRetainedPortSemantics RootBlobRetainedPortGraph RootBlobRetainedPortModel
namespace RootBlobRetainedMaximal
universe u v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable {G : Network V E O} (B : MaximalRootTwoBlob G)

def InternalSink (v : V) : Prop :=
  ∀ e, G.target e ∈ B.vertices → G.source e ≠ v

theorem exists_internal_sink (hG : GraphAdmitted G) :
    ∃ v, v ∈ B.vertices ∧ B.InternalSink v := by
  classical
  let F : Finset V := Finset.univ.filter (fun v => v ∈ B.vertices)
  have hr : G.root ∈ F := by simp [F, B.root_mem]
  obtain ⟨v, hv, hm⟩ := Finset.exists_max_image F G.rank ⟨G.root, hr⟩
  refine ⟨v, (Finset.mem_filter.mp hv).2, ?_⟩
  intro e ht hs
  have htarget : G.target e ∈ F := by simp [F, ht]
  have hle := hm _ htarget
  have hlt := hG.2.2.1 e
  rw [hs] at hlt
  exact (not_lt_of_ge hle) hlt

theorem sink_has_exit (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    {v : V} (hv : v ∈ B.vertices) (hs : B.InternalSink v) :
    ∃ e, Outgoing G B.vertices e ∧ G.source e = v := by
  classical
  have hex : ∃ e, G.source e = v := by
    by_contra hh
    have hn : ∀ e, G.source e ≠ v := by simpa using hh
    obtain ⟨o, ho⟩ := (hG.2.2.2.2.2 v).mp hn
    exact B.hidden hG hB o (by simpa [ho] using hv)
  obtain ⟨e, he⟩ := hex
  refine ⟨e, ⟨by simpa [he] using hv, ?_⟩, he⟩
  intro ht
  exact hs e ht he

theorem one_exit_sink (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    B.InternalSink (G.source (B.region hG hB).pair.first) ∨
      B.InternalSink (G.source (B.region hG hB).pair.second) := by
  obtain ⟨v, hv, hs⟩ := B.exists_internal_sink hG
  obtain ⟨e, he, hev⟩ := B.sink_has_exit hG hB hv hs
  rcases ((B.region hG hB).pair.cover e).mp (Or.inl he) with h | h
  · exact Or.inl (by simpa [← hev, h] using hs)
  · exact Or.inr (by simpa [← hev, h] using hs)

/-- The ordering is fixed from graph data, before any target parameters. -/
noncomputable def orderedExit (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    (i : Fin 2) : E := by
  classical
  exact if B.InternalSink (G.source (B.region hG hB).pair.first) then
    if i = 0 then (B.region hG hB).pair.first else (B.region hG hB).pair.second
  else if i = 0 then (B.region hG hB).pair.second else (B.region hG hB).pair.first

theorem ordered_outgoing (hG : GraphAdmitted G) (hB : BinaryAdmission G) (i : Fin 2) :
    Outgoing G B.vertices (B.orderedExit hG hB i) := by
  classical
  unfold orderedExit
  split_ifs <;>
    first | exact (B.region hG hB).first_outgoing hG
          | exact (B.region hG hB).second_outgoing hG

theorem ordered_injective (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    Function.Injective (B.orderedExit hG hB) := by
  classical
  intro i j hij
  have hn := (B.region hG hB).pair.distinct
  by_cases hs : B.InternalSink (G.source (B.region hG hB).pair.first)
  · fin_cases i <;> fin_cases j <;> simp_all [orderedExit]
  · fin_cases i <;> fin_cases j <;> simp_all [orderedExit]

theorem ordered_sources_injective (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    Function.Injective (fun i => G.source (B.orderedExit hG hB i)) := by
  intro i j hij
  by_contra hne
  have he : B.orderedExit hG hB i ≠ B.orderedExit hG hB j :=
    fun hh => hne (B.ordered_injective hG hB hh)
  exact B.exit_sources_distinct hG hB he
    (B.ordered_outgoing hG hB i) (B.ordered_outgoing hG hB j) hij

theorem ordered_cover (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    {e : E} (he : Outgoing G B.vertices e) :
    ∃ i, B.orderedExit hG hB i = e := by
  classical
  rcases ((B.region hG hB).pair.cover e).mp (Or.inl he) with h | h
  · by_cases hs : B.InternalSink (G.source (B.region hG hB).pair.first)
    · exact ⟨0, by simp [orderedExit, hs, h]⟩
    · exact ⟨1, by simp [orderedExit, hs, h]⟩
  · by_cases hs : B.InternalSink (G.source (B.region hG hB).pair.first)
    · exact ⟨1, by simp [orderedExit, hs, h]⟩
    · exact ⟨0, by simp [orderedExit, hs, h]⟩

theorem ordered_first_sink (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    B.InternalSink (G.source (B.orderedExit hG hB 0)) := by
  classical
  by_cases hs : B.InternalSink (G.source (B.region hG hB).pair.first)
  · simpa [orderedExit, hs] using hs
  · have ht := (B.one_exit_sink hG hB).resolve_left hs
    simpa [orderedExit, hs] using ht

noncomputable def component (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    PortComponent G where
  vertices := B.vertices
  root_mem := B.root_mem
  ports := fun i => G.source (B.orderedExit hG hB i)
  ports_mem := fun i => (B.ordered_outgoing hG hB i).1
  ports_injective := B.ordered_sources_injective hG hB
  ports_nonroot := fun i => B.exit_source_nonroot hG hB (B.ordered_outgoing hG hB i)
  ancestral := (B.region hG hB).ancestral hG
  first_sink := B.ordered_first_sink hG hB
  outgoing_ports := by
    intro e hs ht
    obtain ⟨i, hi⟩ := B.ordered_cover hG hB ⟨hs, ht⟩
    exact ⟨i, congrArg G.source hi⟩
  port_exits := fun i => ⟨B.orderedExit hG hB i, rfl,
    (B.ordered_outgoing hG hB i).2⟩
  hidden := B.hidden hG hB

/-- Terminal port indegree two follows from original binary admission and
internal bridgelessness; it is not silently inserted into the source class. -/
theorem terminal_indegree_two (hG : GraphAdmitted G) (hB : BinaryAdmission G) :
    (incomingEdges G ((B.component hG hB).ports 0)).card = 2 := by
  classical
  let v := (B.component hG hB).ports 0
  have hv : v ∈ B.vertices := (B.component hG hB).ports_mem 0
  have hs : B.InternalSink v := B.ordered_first_sink hG hB
  have hsub : internalIncident G B.vertices v ⊆ incomingEdges G v := by
    intro e he
    have hh := Finset.mem_filter.mp he
    have hi : G.source e = v ∨ G.target e = v := by
      simpa [incidentEdges] using hh.1
    rcases hi with hi | hi
    · exact False.elim (hs e hh.2.2 hi)
    · simp [incomingEdges, hi]
  have hmin := internal_degree_ge_two G B.bridgeless B.root_mem B.nontrivial hv
  have hcard := Finset.card_le_card hsub
  have hn : v ≠ G.root := (B.component hG hB).ports_nonroot 0
  have ho : ∀ o, G.observed o ≠ v := by
    intro o he
    exact B.hidden hG hB o (by simpa [he] using hv)
  rcases hB.internal_degrees v hn ho with hd | hd
  · have hi := hd.1
    omega
  · exact hd.1

theorem other_terminal_parent (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    (hNP : NoParallel G) :
    ∃ e : (B.component hG hB).InnerEdge,
      (B.component hG hB).interior.target e = (B.component hG hB).interior.observed 0 ∧
      (B.component hG hB).interior.source e ≠ (B.component hG hB).interior.observed 1 := by
  classical
  let R := B.component hG hB
  obtain ⟨e, f, hef, hset⟩ := Finset.card_eq_two.mp (B.terminal_indegree_two hG hB)
  have he : G.target e = R.ports 0 := by
    have hm : e ∈ incomingEdges G (R.ports 0) := by rw [hset]; simp
    simpa [incomingEdges] using hm
  have hf : G.target f = R.ports 0 := by
    have hm : f ∈ incomingEdges G (R.ports 0) := by rw [hset]; simp
    simpa [incomingEdges] using hm
  have hex : ∃ g, G.target g = R.ports 0 ∧ G.source g ≠ R.ports 1 := by
    by_cases hs : G.source e = R.ports 1
    · refine ⟨f, hf, ?_⟩
      intro ht
      exact hef (hNP e f (hs.trans ht.symm) (he.trans hf.symm))
    · exact ⟨e, he, hs⟩
  obtain ⟨g, hg, hn⟩ := hex
  have hm : G.target g ∈ R.vertices := by simpa [hg] using R.ports_mem 0
  refine ⟨⟨g, hm⟩, Subtype.ext hg, ?_⟩
  intro hh
  exact hn (congrArg Subtype.val hh)

/-- Explicit positive-weight long resolution, retained for the independent
literal Fourier support/convolution proof obligation. -/
theorem positive_long_resolution {S : Type u} [Fintype S] [Nonempty S]
    (hG : GraphAdmitted G) (hB : BinaryAdmission G) (hNP : NoParallel G)
    (W : E → ℝ) (hW : WeightsAdmitted G W) :
    let R := B.component hG hB
    ∃ σ : RootBlobSwitching.Switching R.interior,
      0 < RootBlobSwitching.weight R.interior (R.insideWeights W) σ ∧
      0 < pathExponent (S := S) R.interior (R.interior_admitted hG) σ := by
  let R := B.component hG hB
  obtain ⟨e, ht, hs⟩ := B.other_terminal_parent hG hB hNP
  obtain ⟨σ, hσ⟩ := exists_positive_pathExponent (S := S) R.interior
    (R.interior_admitted hG) e ht hs
  exact ⟨σ, RootBlobSwitching.weight_positive R.interior (R.insideWeights W)
    (R.insideWeights_admitted hG W hW) σ, hσ⟩

/-- Original maximal-source to actual admitted retained-fork equality.
The new target has two degree-two retained ports, not a binary/single-edge
suppression. No continuous-time or Fourier subclass theorem is inferred
from the full open-equivariant parameter predicate used here. -/
theorem maximal_fixed_exterior_full {S : Type u} [Fintype S] [Nonempty S]
    (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    (_hNP : NoParallel G) (_hLSA : RootLSA G)
    (W : E → ℝ) (hW : WeightsAdmitted G W)
    (MX : (B.component hG hB).OuterEdge → Mat S)
    (H : Subgroup (Equiv.Perm S)) (hMX : ∀ e, OpenTransition H (MX e)) :
    let R := B.component hG hB
    GraphAdmitted (R.retainedFork hG) ∧
    WeightsAdmitted (R.retainedFork hG) (R.retainedWeights W) ∧
    R.fixedImage W MX H =
      RootBlobCutFactorization.cutImage rootedFork (R.exterior hG) R.labels R.forkRank
        forkWeights (R.outsideWeights W) MX H :=
  (B.component hG hB).fixed_exterior_full hG W hW MX H hMX

end RootBlobRetainedMaximal
