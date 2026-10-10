import G7OriginalEdgeOperators
import UnifiedLean.Source.SourceBoundaryLocations

/-! Safe original-boundary interchanges needed INSIDE the complete all-edge
frontier gathering. These operate on the inherited source fields, with safety
ultimately derived from original endpoint IDs. No global epoch is interchanged
with a boundary. Uncompiled internal candidate, dot 2026-10-10. -/
namespace GProgram.G7.OriginalEdgeBoundary
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open GProgram.G7.NodeActions GProgram.G7.OriginalEdgeOperators
open GProgram.G7.SinglePopulationPolynomialKernel
open Matrix NormedSpace
open scoped Classical BigOperators Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Only the explicit target of this inherited node action is inspected. -/
def AvoidsPopulation {N : RootedBinary V E X} (a : Action N) (i : Option E) : Prop :=
  ∀ (reg : V → Bool) (coin : Copy → Bool) (l : Copy),
    target a reg coin l ≠ originalPlace N i

lemma route_population_iff {N : RootedBinary V E X} (a : Action N) (i : Option E)
    (ha : AvoidsPopulation (Copy:=Copy) a i) (reg : V → Bool)
    (coin : Copy → Bool) (l : Copy) (loc : Location V E) :
    route a reg coin l loc = originalPlace N i ↔ loc = originalPlace N i := by
  by_cases h : loc = .node (site a)
  · subst loc
    simp [route,ha reg coin l,Ne.symm (originalPlace_not_node N i (site a))]
  · simp [route,h]

/-- Current pair legality is unchanged by a node which cannot route into the
pair's original population. Current live-owner coins are kept on the fixed
original Copy carrier already bound by G7NodeActions.kernel_fixed_carrier. -/
lemma node_pair_preserved {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (i : Option E) (ha : AvoidsPopulation (Copy:=Copy) a i)
    (p : Copy × Copy) (s : Code N sample) (coin : Copy → Bool) :
    PairAt N i p (destination a s coin) ↔ PairAt N i p s := by
  rw [pairAt_iff,pairAt_iff,destination_live,destination_location,destination_location]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
    refine ⟨h₁,?_,h₃,?_,h₅⟩
    · apply (route_population_iff a i ha _ coin _ _).mp
      simpa [h₁] using h₂
    · apply (route_population_iff a i ha _ coin _ _).mp
      simpa [h₃] using h₄
  · rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
    refine ⟨h₁,?_,h₃,?_,h₅⟩
    · simpa [h₁] using (route_population_iff a i ha _ coin _ _).mpr h₂
    · simpa [h₃] using (route_population_iff a i ha _ coin _ _).mpr h₄

/-- Safe original-node action and one literal population merger commute on
the actual source code, including retained genealogy orientation and register. -/
theorem node_mergeAt_commute {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (i : Option E) (ha : AvoidsPopulation (Copy:=Copy) a i)
    (p : Copy × Copy) (s : Code N sample) (coin : Copy → Bool) :
    destination a (mergeAt N i p s) coin = mergeAt N i p (destination a s coin) := by
  by_cases hp : PairAt N i p s
  · have hp' := (node_pair_preserved a i ha p s coin).mpr hp
    have pp := (pairAt_iff N i p s).mp hp
    apply canonical_ext _ _ (destination_canonical _ _ _) (merged_canonical N i p _ hp')
    apply state_ext
    · simp only [destination_live,merged_live N i p s hp,
        merged_live N i p _ hp']
    · funext x
      simp only [destination_ancestor,merged_ancestor N i p s hp,
        merged_ancestor N i p _ hp']
    · funext x
      simp only [destination_genealogy,merged_genealogy N i p s hp,
        merged_genealogy N i p _ hp',destination_live,merged_live N i p s hp]
      by_cases hx : x ∈ (state s).live.erase p.2
      · have hxold := (Finset.mem_erase.mp hx).2
        simp [hx,hxold,pp.1,pp.2.2.1]
      · simp [hx]
    · funext x
      simp only [destination_location,merged_location N i p s hp,
        merged_location N i p _ hp',destination_live,merged_live N i p s hp,merged_register]
      by_cases hx : x ∈ (state s).live.erase p.2
      · have hxold := (Finset.mem_erase.mp hx).2
        simp [hx,hxold]
      · simp [hx]
    · simp only [destination_register,merged_register]
    · rfl
  · have hp' : ¬ PairAt N i p (destination a s coin) :=
      fun h => hp ((node_pair_preserved a i ha p s coin).mp h)
    rw [mergeAt_of_not_mem N i p s hp,mergeAt_of_not_mem N i p _ hp']

/-- Original graph endpoint inequality discharges safe routing for every
ordinary/common/independent operation and every forced gamma endpoint. -/
theorem original_node_avoids_other_edge (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (e : E) (h : v ≠ N.graph.target e) :
    AvoidsPopulation (Copy:=Copy) (originalAction N H gamma common v) (some e) := by
  intro reg coin l he
  unfold originalAction at he
  split at he
  · simp [target,originalPlace] at he
  · split at he
    · rename_i hh
      split at he
      · have hp : (H.parents ⟨v,hh⟩).parent (reg (H.parents ⟨v,hh⟩).hybrid) = e :=
          Location.edge.inj he
        have ht := registry_parent_target N H ⟨v,hh⟩ (reg (H.parents ⟨v,hh⟩).hybrid)
        exact h ((hp ▸ ht).symm)
      · have hp : (H.parents ⟨v,hh⟩).parent (coin l) = e := Location.edge.inj he
        have ht := registry_parent_target N H ⟨v,hh⟩ (coin l)
        exact h ((hp ▸ ht).symm)
    · have hp : (defaultSelector N).edge ⟨v,by assumption⟩ = e := Location.edge.inj he
      have ht := (defaultSelector N).target ⟨v,by assumption⟩
      exact h ((hp ▸ ht).symm)

/-- The ancestor population can only be entered at the original root. -/
theorem original_node_avoids_root (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (h : v ≠ N.root) :
    AvoidsPopulation (Copy:=Copy) (originalAction N H gamma common v) none := by
  intro reg coin l
  unfold originalAction
  simp only [h,dif_neg]
  split
  · split <;> simp [target,originalPlace]
  · simp [target,originalPlace]

noncomputable def boundaryMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) : Matrix (Code N sample) (Code N sample) ℝ :=
  fun s d => (boundaryKernel N op s d).toReal

/-- The source-bound fixed-coin node kernel intertwines with each safe actual
population trial. No desired boundary/epoch law is assumed. -/
theorem node_pair_matrix_commute {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (i : Option E) (ha : AvoidsPopulation (Copy:=Copy) a i) (p : Copy × Copy) :
    Commute (pairMatrix N (sample:=sample) i p) (boundaryMatrix N (operation a)) := by
  have hk (s : Code N sample) :
      ((boundaryKernel N (operation a) s).map (mergeAt N i p)) =
        boundaryKernel N (operation a) (mergeAt N i p s) := by
    rw [kernel_fixed_carrier,kernel_fixed_carrier,PMF.map_comp]
    congr 1
    funext coin
    exact (node_mergeAt_commute a i ha p s coin).symm
  change _ * _ = _ * _
  ext s d
  simp only [Matrix.mul_apply,pairMatrix,boundaryMatrix,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]
  have hm := congrArg (fun q : PMF (Code N sample) => (q d).toReal) (hk s)
  rw [UnifiedLean.Source.SourceFiniteProjection.map_probability_real] at hm
  exact hm.symm

theorem node_population_generator_commute {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (i : Option E) (ha : AvoidsPopulation (Copy:=Copy) a i) :
    Commute (populationGenerator N (sample:=sample) i) (boundaryMatrix N (operation a)) := by
  unfold populationGenerator
  exact (Commute.sum_left _ _ _ (fun p _ =>
    (node_pair_matrix_commute a i ha p).sub_left (Commute.one_left _))).smul_left (1/2:ℝ)

lemma exit_live (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : (state (exitCode N s e)).live = (state s).live := rfl
lemma exit_ancestor (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : (state (exitCode N s e)).ancestor = (state s).ancestor := rfl
lemma exit_register (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : (state (exitCode N s e)).register = (state s).register := rfl
lemma exit_genealogy (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    (state (exitCode N s e)).genealogy x =
      if x ∈ (state s).live then (state s).genealogy x else .leaf x := by
  simp [state,exitCode,admittedCode,encodeSnapshot,decodeSnapshot,exitEdge,transport]
lemma exit_location (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    (state (exitCode N s e)).location x =
      if x ∈ (state s).live then exitLocation N e ((state s).location x) else .node N.root := by
  simp [state,exitCode,admittedCode,encodeSnapshot,decodeSnapshot,exitEdge,transport,exitLocation]

lemma exit_population_iff (N : RootedBinary V E X) (i : Option E) (e : E)
    (hi : i ≠ some e) (loc : Location V E) :
    exitLocation N e loc = originalPlace N i ↔ loc = originalPlace N i := by
  cases i with
  | none => by_cases h : loc = .edge e <;> simp [exitLocation,originalPlace,h]
  | some f =>
    have hf : f ≠ e := fun h => hi (congrArg some h)
    by_cases h : loc = .edge e
    · subst loc
      simp [exitLocation,originalPlace,hf,Ne.symm hf]
    · simp [exitLocation,h]

lemma exit_pair_preserved (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (e : E) (hi : i ≠ some e) (p : Copy × Copy) (s : Code N sample) :
    PairAt N i p (exitCode N s e) ↔ PairAt N i p s := by
  rw [pairAt_iff,pairAt_iff,exit_live,exit_location,exit_location]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
    refine ⟨h₁,?_,h₃,?_,h₅⟩
    · apply (exit_population_iff N i e hi _).mp
      simpa [h₁] using h₂
    · apply (exit_population_iff N i e hi _).mp
      simpa [h₃] using h₄
  · rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
    refine ⟨h₁,?_,h₃,?_,h₅⟩
    · simpa [h₁] using (exit_population_iff N i e hi _).mpr h₂
    · simpa [h₃] using (exit_population_iff N i e hi _).mpr h₄

theorem exit_mergeAt_commute (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (e : E) (hi : i ≠ some e) (p : Copy × Copy) (s : Code N sample) :
    exitCode N (mergeAt N i p s) e = mergeAt N i p (exitCode N s e) := by
  by_cases hp : PairAt N i p s
  · have hp' := (exit_pair_preserved N i e hi p s).mpr hp
    have pp := (pairAt_iff N i p s).mp hp
    apply canonical_ext _ _ (admitted_canonical N sample _ _) (merged_canonical N i p _ hp')
    apply state_ext
    · simp only [exit_live,merged_live N i p s hp,merged_live N i p _ hp']
    · funext x
      simp only [exit_ancestor,merged_ancestor N i p s hp,merged_ancestor N i p _ hp']
    · funext x
      simp only [exit_genealogy,merged_genealogy N i p s hp,
        merged_genealogy N i p _ hp',exit_live,merged_live N i p s hp]
      by_cases hx : x ∈ (state s).live.erase p.2
      · have hxold := (Finset.mem_erase.mp hx).2
        simp [hx,hxold,pp.1,pp.2.2.1]
      · simp [hx]
    · funext x
      simp only [exit_location,merged_location N i p s hp,
        merged_location N i p _ hp',exit_live,merged_live N i p s hp]
      by_cases hx : x ∈ (state s).live.erase p.2
      · have hxold := (Finset.mem_erase.mp hx).2
        simp [hx,hxold]
      · simp [hx]
    · simp only [exit_register,merged_register]
    · rfl
  · have hp' : ¬ PairAt N i p (exitCode N s e) :=
      fun h => hp ((exit_pair_preserved N i e hi p s).mp h)
    rw [mergeAt_of_not_mem N i p s hp,mergeAt_of_not_mem N i p _ hp']

theorem exit_pair_matrix_commute (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (e : E) (hi : i ≠ some e) (p : Copy × Copy) :
    Commute (pairMatrix N (sample:=sample) i p) (boundaryMatrix N (.exit e)) := by
  change _ * _ = _ * _
  ext s d
  simp only [Matrix.mul_apply,pairMatrix,boundaryMatrix,boundaryKernel,PMF.pure_apply]
  simp only [ENNReal.toReal_ite,ENNReal.toReal_one,ENNReal.toReal_zero]
  simp [exit_mergeAt_commute N i e hi p s]

theorem exit_population_generator_commute (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (e : E) (hi : i ≠ some e) :
    Commute (populationGenerator N (sample:=sample) i) (boundaryMatrix N (.exit e)) := by
  unfold populationGenerator
  exact (Commute.sum_left _ _ _ (fun p _ =>
    (exit_pair_matrix_commute N i e hi p).sub_left (Commute.one_left _))).smul_left (1/2:ℝ)

/-- A safe ORIGINAL node commutes with the complete edge-local time kernel,
for any exposure. This is not a global source epoch permutation. -/
theorem original_node_population_exponential_commute (N : RootedBinary V E X)
    {sample : Copy → X} (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) (e : E) (hv : v ≠ N.graph.target e) (a : ℝ) :
    Commute (populationExponential N (sample:=sample) (some e) a)
      (boundaryMatrix N (originalNodeOperation N H gamma common v)) := by
  rw [←original_operation N H gamma common v]
  exact ((node_population_generator_commute (originalAction N H gamma common v) (some e)
    (original_node_avoids_other_edge N H gamma common v e hv)).smul_left a).exp_left

theorem other_exit_population_exponential_commute (N : RootedBinary V E X)
    {sample : Copy → X} (e f : E) (hef : e ≠ f) (a : ℝ) :
    Commute (populationExponential N (sample:=sample) (some e) a) (boundaryMatrix N (.exit f)) :=
  ((exit_population_generator_commute N (some e) f (by simpa using hef)).smul_left a).exp_left

end GProgram.G7.OriginalEdgeBoundary
