import G1CanonicalCrossingRootAndKAdmission

/-! Physical separator agenda cuts use actual original support, including
arbitrary source histories. No kernel identity is a hypothesis. -/
namespace G1SeparatedAgendaSupportCuts
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open G1ActualJointProgram G1JointSeparatedSourceGeometry
open G1SameOriginalExteriorContinuation
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_separated_agenda_append_iff (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (first last : List (ProgramStep N))
    (s : Code N sample) :
    SeparatedAgenda N r inside outside (first ++ last) s ↔
      SeparatedAgenda N r inside outside first s ∧
        ∀ p ∈ (sourceProgram N r first s).support, SeparatedAgenda N r inside outside last p := by
  induction first generalizing s with
  | nil =>
      simp only [List.nil_append,SeparatedAgenda,sourceProgram,PMF.mem_support_pure_iff,true_and]
      exact ⟨fun h p hp => hp ▸ h,fun h => h s rfl⟩
  | cons op first ih =>
      simp only [List.cons_append,SeparatedAgenda]
      constructor
      · rintro ⟨hsep,htail⟩
        refine ⟨⟨hsep,fun p hp => ((ih p).mp (htail p hp)).1⟩,?_⟩
        intro q hq
        obtain ⟨p,hp,hqp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hq
        exact ((ih p).mp (htail p hp)).2 q hqp
      · rintro ⟨⟨hsep,hfirst⟩,hlast⟩
        refine ⟨hsep,?_⟩
        intro p hp
        apply (ih p).mpr
        exact ⟨hfirst p hp,fun q hq => hlast q ((PMF.mem_support_bind_iff _ _ _).mpr ⟨p,hp,hq⟩)⟩

theorem actual_separated_agenda_mono (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right smallLeft smallRight : Finset Copy)
    (hl : smallLeft ⊆ left) (hr : smallRight ⊆ right)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (hs : SeparatedAgenda N r left right ops s) :
    SeparatedAgenda N r smallLeft smallRight ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
      exact ⟨fun x hx y hy => hs.1 x (hl hx) y (hr hy),
        fun d hd => ih d (hs.2 d hd)⟩

#print axioms actual_separated_agenda_append_iff
end G1SeparatedAgendaSupportCuts
