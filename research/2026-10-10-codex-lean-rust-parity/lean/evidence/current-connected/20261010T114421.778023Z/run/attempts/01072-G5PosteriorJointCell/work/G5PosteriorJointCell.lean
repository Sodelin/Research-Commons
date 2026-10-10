import G5OriginalSelectedPosterior

/-! Bayes cell identity used to connect the actual two-cut joint law to the
existing original source posterior. No independence premise. -/
namespace GProgram.G5.PosteriorJointCell
open scoped Classical ENNReal

lemma posterior_joint_cell {A B I O : Type*} (mu : PMF A) (K : A → PMF B)
    (f : A → I) (g : B → O) (i : I) (o : O)
    (h : ∃ a ∈ {a | f a = i}, a ∈ mu.support) :
    ((((mu.filter {a | f a = i} h).bind K).map g) o) =
      ((mu.bind (fun a => (K a).map (fun b => (f a,g b)))) (i,o)) *
        (mu.toOuterMeasure {a | f a = i})⁻¹ := by
  rw [PMF.map_bind,PMF.bind_apply,PMF.bind_apply,← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  by_cases ha : f a = i
  · have hrow : ((K a).map (fun b => (f a,g b))) (i,o) = ((K a).map g) o := by
      simp only [PMF.map_apply,Prod.mk.injEq,ha,true_and]
    rw [hrow,PMF.filter_apply]
    simp only [Set.mem_setOf_eq,ha,Set.indicator_of_mem,PMF.toOuterMeasure_apply]
    ac_rfl
  · have hrow : ((K a).map (fun b => (f a,g b))) (i,o) = 0 := by
      simp [PMF.map_apply,Prod.mk.injEq,Ne.symm ha]
    rw [hrow,PMF.filter_apply_eq_zero_of_notMem h ha]
    simp

lemma joint_first_marginal {A B I O : Type*} (mu : PMF A) (K : A → PMF B)
    (f : A → I) (g : B → O) :
    (mu.bind (fun a => (K a).map (fun b => (f a,g b)))).map Prod.fst = mu.map f := by
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  change (mu.bind (fun a => (K a).map (fun _ => f a))) = mu.map f
  change (mu.bind (fun a => (K a).map (Function.const B (f a)))) = _
  simp only [PMF.map_const]
  rfl

#print axioms joint_first_marginal
#print axioms posterior_joint_cell
end GProgram.G5.PosteriorJointCell
