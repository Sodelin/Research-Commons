import G7CalendarExposureClosedForm
import G7BoundaryPhasePermutation
import Mathlib.Data.List.Perm.Basic

/-! Schedule-independent evaluation of the actual whole-edge frontier. The
only noncommuting pairs are an original edge's own entry/exit interfaces.
Internal candidate toward the full original G7 exposure endpoint; uncompiled.
-/
namespace GProgram.G7.OrderedFrontierProduct
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourcePoissonExponential
open GProgram.G7.NodeActions GProgram.G7.BoundaryExitCommutation
open GProgram.G7.OriginalEdgeOperators GProgram.G7.OriginalEdgeBoundary
open GProgram.G7.OriginalEdgeGathering GProgram.G7.EdgeExposureAccounting
open GProgram.G7.CalendarExposureClosedForm
open scoped Classical BigOperators Matrix.Norms.Operator

/-- Two complete finite schedules respecting the same noncommuting order
constraints have the same product. The commutation condition is applied only
to reversed pairs; it does not assume all original operations commute. -/
theorem product_eq_of_compatible_orders {A M : Type*} [Monoid M] (f : A → M) (R : A → A → Prop)
    (resolve : ∀ a b, R a b → R b a → Commute (f a) (f b))
    (xs ys : List A) (hp : xs.Perm ys) (hx : xs.Pairwise R) (hy : ys.Pairwise R) :
    (xs.map f).prod = (ys.map f).prod := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := List.nil_perm.mp hp
    simp [he]
  | cons a xs ih =>
    have hmem : a ∈ ys := hp.mem_iff.mp (by simp)
    obtain ⟨pre,post,rfl⟩ := List.mem_split hmem
    have hpre := List.pairwise_append.mp hy
    have hxs := List.pairwise_cons.mp hx
    have htail : (pre++post).Pairwise R := List.pairwise_append.mpr
      ⟨hpre.1,(List.pairwise_cons.mp hpre.2.1).2,
        fun b hb c hc => hpre.2.2 b hb c (List.mem_cons_of_mem a hc)⟩
    have hc : Commute (f a) ((pre.map f).prod) := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
      by_cases he : b = a
      · subst b; exact Commute.refl _
      · have hbxs : b ∈ xs := by
          have hm : b ∈ a::xs := hp.mem_iff.mpr (List.mem_append_left _ hb)
          exact (List.mem_cons.mp hm).resolve_left he
        exact resolve a b (hxs.1 b hbxs) (hpre.2.2 b hb a (by simp))
    have ht := ih (pre++post) (hp.trans List.perm_middle |>.cons_inv) hxs.2 htail
    simp only [List.map_cons,List.prod_cons,List.map_append,List.prod_append]
    rw [ht,List.map_append,List.prod_append,←mul_assoc,hc.eq,mul_assoc]

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma route_exit_commute {N : RootedBinary V E X} (a : Action N) (e : E)
    (ht : AvoidsPopulation (Copy:=Copy) a (some e)) (hs : site a ≠ N.graph.source e)
    (reg : V → Bool) (coin : Copy → Bool) (l : Copy) (loc : Location V E) :
    exitLocation N e (route a reg coin l loc) = route a reg coin l (exitLocation N e loc) := by
  by_cases hn : loc = .node (site a)
  · subst loc
    simp [route,exitLocation,ht reg coin l]
  · by_cases he : loc = .edge e
    · subst loc
      simp [route,exitLocation,hs,Ne.symm hs]
    · simp [route,exitLocation,hn,he]

lemma node_exit_destination_commute {N : RootedBinary V E X} {sample : Copy → X}
    (a : Action N) (e : E) (ht : AvoidsPopulation (Copy:=Copy) a (some e))
    (hs : site a ≠ N.graph.source e) (s : Code N sample) (coin : Copy → Bool) :
    exitCode N (destination a s coin) e = destination a (exitCode N s e) coin := by
  apply canonical_ext _ _ (admitted_canonical N sample _ _) (destination_canonical _ _ _)
  apply state_ext
  · simp only [exit_live,destination_live]
  · simp only [exit_ancestor,destination_ancestor]
  · funext l
    simp only [exit_genealogy,destination_genealogy,exit_live,destination_live]
    by_cases hl : l ∈ (state s).live <;> simp [hl]
  · funext l
    simp only [exit_location,destination_location,exit_live,destination_live,exit_register,destination_register]
    by_cases hl : l ∈ (state s).live
    · simp only [hl,if_pos]
      exact route_exit_commute a e ht hs _ coin l _
    · simp [hl]
  · simp only [exit_register,destination_register]
  · rfl

lemma original_node_exit_matrix_commute (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (e : E)
    (ht : v ≠ N.graph.target e) (hs : v ≠ N.graph.source e) :
    Commute (boundaryMatrix N (sample:=sample) (originalNodeOperation N H gamma common v))
      (boundaryMatrix N (.exit e)) := by
  let a := originalAction N H gamma common v
  have hs' : site a ≠ N.graph.source e := by simpa [a,original_site] using hs
  have ht' : AvoidsPopulation (Copy:=Copy) a (some e) := original_node_avoids_other_edge N H gamma common v e ht
  have hk (s : Code N sample) :
      ((boundaryKernel N (operation a) s).bind (boundaryKernel N (.exit e))) =
        ((boundaryKernel N (.exit e) s).bind (boundaryKernel N (operation a))) := by
    simp only [boundaryKernel,PMF.pure_bind]
    rw [kernel_fixed_carrier,PMF.bind_map,kernel_fixed_carrier]
    change (coinLaw (Copy:=Copy) a).map (fun coin => exitCode N (destination a s coin) e) = _
    congr 1
    funext coin
    exact node_exit_destination_commute a e ht' hs' s coin
  change _ * _ = _ * _
  ext s d
  have hm := congrArg (fun p : PMF (Code N sample) => (p d).toReal) (hk s)
  simp only [bind_probability_real,tsum_fintype] at hm
  simpa only [Matrix.mul_apply,boundaryMatrix,original_operation,a] using hm

inductive Atom (V E : Type*)
  | exit (edge : E)
  | node (vertex : V)
  deriving DecidableEq

def RequiredBefore (N : RootedBinary V E X) : Atom V E → Atom V E → Prop
  | .node v,.exit e => v = N.graph.target e
  | .exit e,.node v => v = N.graph.source e
  | _,_ => False

def Compatible (N : RootedBinary V E X) (a b : Atom V E) : Prop := ¬ RequiredBefore N b a

noncomputable def atomMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (w : ExposureBank E) : Atom V E → Matrix (Code N sample) (Code N sample) ℝ
  | .exit e => boundaryMatrix N (.exit e)
  | .node v => boundaryMatrix N (originalNodeOperation N H gamma common v) *
      bankExponential N (retain (Opens N v) w)

lemma bankExponential_commute (N : RootedBinary V E X) {sample : Copy → X} (w z : ExposureBank E) :
    Commute (bankExponential N (sample:=sample) w) (bankExponential N z) :=
  (bankGenerator_commute N w z).exp

lemma other_node_bank_commute (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v u : V) (h : v ≠ u) (w : ExposureBank E) :
    Commute (bankExponential N (sample:=sample) (retain (Opens N v) w))
      (boundaryMatrix N (originalNodeOperation N H gamma common u)) := by
  have he : retain (fun i => ¬ Opens N u i) (retain (Opens N v) w) = retain (Opens N v) w := by
    funext i
    by_cases hv : Opens N v i
    · have hu : ¬ Opens N u i := fun hu => opens_disjoint N h i ⟨hv,hu⟩
      simp [retain,hv,hu]
    · simp [retain,hv]
  rw [←he]
  exact node_remainder_commutes N H gamma common u _

lemma other_exit_node_bank_commute (N : RootedBinary V E X) {sample : Copy → X}
    (e : E) (v : V) (hv : v ≠ N.graph.target e) (w : ExposureBank E) :
    Commute (bankExponential N (sample:=sample) (retain (Opens N v) w)) (boundaryMatrix N (.exit e)) := by
  have he : retain (fun i => i ≠ some e) (retain (Opens N v) w) = retain (Opens N v) w := by
    funext i
    by_cases hi : i = some e
    · subst i; simp [retain,Opens,hv]
    · simp [retain,hi]
  rw [←he]
  exact exit_remainder_commutes N e _

lemma matrix_commute_of_boundary_kernels (N : RootedBinary V E X) {sample : Copy → X}
    (a b : BoundaryOperation N)
    (h : ∀ s : Code N sample, (boundaryKernel N a s).bind (boundaryKernel N b) =
      (boundaryKernel N b s).bind (boundaryKernel N a)) :
    Commute (boundaryMatrix N (sample:=sample) a) (boundaryMatrix N b) := by
  change _ * _ = _ * _
  ext s d
  have hm := congrArg (fun p : PMF (Code N sample) => (p d).toReal) (h s)
  simpa [bind_probability_real,tsum_fintype,Matrix.mul_apply,boundaryMatrix] using hm

lemma original_node_matrices_commute (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v u : V) :
    Commute (boundaryMatrix N (sample:=sample) (originalNodeOperation N H gamma common v))
      (boundaryMatrix N (originalNodeOperation N H gamma common u)) := by
  by_cases h : v=u
  · subst u; exact Commute.refl _
  · apply matrix_commute_of_boundary_kernels
    intro s
    rw [←original_operation N H gamma common v,←original_operation N H gamma common u]
    exact kernels_commute _ _ (by simpa only [original_site] using h) s

lemma original_exit_matrices_commute (N : RootedBinary V E X) {sample : Copy → X} (e f : E) :
    Commute (boundaryMatrix N (sample:=sample) (.exit e)) (boundaryMatrix N (.exit f)) := by
  by_cases h : e=f
  · subst f; exact Commute.refl _
  · apply matrix_commute_of_boundary_kernels
    intro s
    simp only [boundaryKernel,PMF.pure_bind]
    rw [exit_code_commute N s e f h]

/-- All reversed pairs permitted by the ORIGINAL edge endpoint order have
commuting source matrices. This includes every nonbridge and parallel edge. -/
theorem compatible_atoms_commute (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (w : ExposureBank E) (a b : Atom V E)
    (hab : Compatible N a b) (hba : Compatible N b a) :
    Commute (atomMatrix N (sample:=sample) H gamma common w a)
      (atomMatrix N H gamma common w b) := by
  cases a with
  | exit e =>
    cases b with
    | exit f => exact original_exit_matrices_commute N e f
    | node v =>
      exact (original_node_exit_matrix_commute N H gamma common v e hab hba).symm.mul_right
        (other_exit_node_bank_commute N e v hab w).symm
  | node v =>
    cases b with
    | exit e =>
      exact (original_node_exit_matrix_commute N H gamma common v e hba hab).mul_left
        (other_exit_node_bank_commute N e v hba w)
    | node u =>
      by_cases h : v=u
      · subst u; exact Commute.refl _
      · exact ((original_node_matrices_commute N H gamma common v u).mul_right
          (other_node_bank_commute N H gamma common u v h.symm w).symm).mul_left
          ((other_node_bank_commute N H gamma common v u h w).mul_right
            (bankExponential_commute N _ _))

end GProgram.G7.OrderedFrontierProduct
