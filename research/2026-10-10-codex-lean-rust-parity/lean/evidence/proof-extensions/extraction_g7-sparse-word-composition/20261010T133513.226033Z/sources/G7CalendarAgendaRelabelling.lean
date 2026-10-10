import G7CalendarNodeRelabelling

/-! The source calendar's actual finite registries and tied-date phases under
original graph relabelling. Contributor: dot,2026-10-09. -/
namespace GProgram.G7.CalendarAgendaRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G7.OriginalRelabelling GProgram.G7.CalendarNodeRelabelling
open GProgram.G7.ProgramRelabelling GProgram.G7.BoundaryPhasePermutation
open scoped Classical
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

theorem filtered_registry_perm {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, Q (e a) ↔ P a) :
    ((Finset.univ.filter P).toList.map e).Perm ((Finset.univ.filter Q).toList) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map e.injective (Finset.nodup_toList _)) (Finset.nodup_toList _)).2
  intro b
  obtain ⟨a,rfl⟩ := e.surjective b
  simp only [List.mem_map,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,
    Equiv.apply_eq_iff_eq,exists_eq_right]
  exact (h a).symm

theorem dates (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) (C : Calendar N.graph) :
    originalDates (network N v e) (calendar N v e C) = originalDates N C := by
  ext t
  simp only [originalDates,Finset.mem_image,Finset.mem_univ,true_and,calendar]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨v.symm a,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨v a,by simpa using ha⟩

theorem sorted_dates (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) (C : Calendar N.graph) :
    sortedOriginalDates (network N v e) (calendar N v e C) = sortedOriginalDates N C := by
  unfold sortedOriginalDates
  rw [dates]

theorem exit_registry_perm (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (t : ℝ) :
    ((Finset.univ.filter (fun f : E => C.age (N.graph.source f) = t)).toList.map e).Perm
      ((Finset.univ.filter (fun f : F => (calendar N v e C).age
        ((network N v e).graph.source f) = t)).toList) := by
  apply filtered_registry_perm
  intro f
  simp [calendar,network,graph]

theorem node_registry_perm (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (t : ℝ) :
    ((Finset.univ.filter (fun a : V => C.age a = t)).toList.map v).Perm
      ((Finset.univ.filter (fun a : W => (calendar N v e C).age a = t)).toList) := by
  apply filtered_registry_perm
  intro a
  simp [calendar]


/-- The two compiler phases are compared separately. No exit/node swap is
used, and tied dates remain tied. This is equality at the actual source PMF. -/
theorem boundary_agenda (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (g : Hybrid N → unitInterval)
    (c : Hybrid N → Bool) (r : PositivePairRates F) (t : ℝ)
    {sample : Copy → X} (s : Code (network N v e) sample) :
    sourceProgram (network N v e) r
      ((boundaryOperations N C H g c t).map (programStep N v e)) s =
    sourceProgram (network N v e) r
      (boundaryOperations (network N v e) (calendar N v e C) (registry N v e H)
        (gamma N v e g) (common N v e c) t) s := by
  have hx := exit_phase_perm (network N v e) r (exit_registry_perm N v e C t) s
  have hn (d : Code (network N v e) sample) := node_phase_perm (network N v e) r
    (registry N v e H) (gamma N v e g) (common N v e c) (node_registry_perm N v e C t) d
  simp only [List.map_map] at hx hn
  dsimp only [Function.comp_def] at hx hn
  simp only [boundaryOperations,List.map_append,List.map_map]
  dsimp only [Function.comp_def,programStep]
  simp_rw [node_operation]
  simp only [GProgram.G7.BoundaryRelabelling.operation]
  rw [program_append,program_append,hx]
  congr 1
  funext d
  exact hn d

#print axioms sorted_dates
#print axioms exit_registry_perm
#print axioms node_registry_perm
end GProgram.G7.CalendarAgendaRelabelling
