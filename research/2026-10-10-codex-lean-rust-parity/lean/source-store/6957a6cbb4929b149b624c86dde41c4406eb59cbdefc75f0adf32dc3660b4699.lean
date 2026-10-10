import G1ConcurrentOriginalSourceWindow

/-! Lawful pending-output fusion for two crossing actor intervals.
The middle concurrent window and the later outside continuation each occur
once. Full actor kernels are their own private source-kernel composites, and
all exterior record data remain joint. Contributor: dot, 2026-10-03. -/
namespace G1CrossingActorKernelFusion
open G1ActualJointEpoch
variable {A A₁ A₂ B B₁ B₂ C C₁ C₂ Record : Type*}

/-- Chronological micro-interpreter: actor A begins first, B begins later,
A closes first, and B closes later while A's output interacts outside. -/
noncomputable def crossingMicroRun
    (pA : A → PMF A₁) (qA : A₁ → PMF A₂)
    (openB : C → PMF (B × C₁)) (qB : B → PMF B₁) (rB : B₁ → PMF B₂)
    (qC : C₁ → PMF C₂) (afterA : A₂ × C₂ → PMF Record) (a : A) (c : C) : PMF (A₂ × B₂ × Record) :=
  (independentProduct (pA a) (openB c)).bind (fun first =>
    (independentProduct (qA first.1)
      (independentProduct (qB first.2.1) (qC first.2.2))).bind (fun middle =>
        (independentProduct (rB middle.2.1) (afterA (middle.1,middle.2.2))).map
          (fun last => (middle.1,last.1,last.2))))

/-- Each full actor K is sampled once from its private composite. B's output
is held pending while the same outside continuation uses A's exposed output. -/
noncomputable def crossingPendingKRun
    (pA : A → PMF A₁) (qA : A₁ → PMF A₂)
    (openB : C → PMF (B × C₁)) (qB : B → PMF B₁) (rB : B₁ → PMF B₂)
    (qC : C₁ → PMF C₂) (afterA : A₂ × C₂ → PMF Record) (a : A) (c : C) : PMF (A₂ × B₂ × Record) :=
  (independentProduct ((pA a).bind qA) (openB c)).bind (fun first =>
    (independentProduct ((qB first.2.1).bind rB) (qC first.2.2)).bind (fun middle =>
      (afterA (first.1,middle.2)).map (fun record => (first.1,middle.1,record))))

/-- Exact full JOINT law, including arbitrary Record-valued exterior history.
No non-overlapping interval premise or supplied full-output identity occurs. -/
theorem crossing_actual_private_kernels_fuse
    (pA : A → PMF A₁) (qA : A₁ → PMF A₂)
    (openB : C → PMF (B × C₁)) (qB : B → PMF B₁) (rB : B₁ → PMF B₂)
    (qC : C₁ → PMF C₂) (afterA : A₂ × C₂ → PMF Record) (a : A) (c : C) :
    crossingMicroRun pA qA openB qB rB qC afterA a c =
      crossingPendingKRun pA qA openB qB rB qC afterA a c := by
  simp only [crossingMicroRun,crossingPendingKRun,independentProduct,
    PMF.bind_bind,PMF.bind_map,PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext a₁
  rw [PMF.bind_comm (openB c) (qA a₁)]
  congr 1
  funext a₂
  congr 1
  funext bc
  congr 1
  funext b₁
  rw [PMF.bind_comm (qC bc.2) (rB b₁)]

#print axioms crossing_actual_private_kernels_fuse
end G1CrossingActorKernelFusion
