import G5CommonSwitchingQuartetWitness
import G5ArbitraryCoupledGroupCountTransfer
import G5ObservableSafePairSupport

/-!
# Safe current original representatives realize all coupled group selectors
Contributor: dot / OpenAI, 2026-10-03.
Every group is an injectively indexed retained ORIGINAL tip. SafeAt proves the
actual current original sites are distinct; a SAME original register is then
constructed to realize every desired private group choice. Descriptions are
actual source geometry, whose uniform existence is already proved.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast GProgram.G5.QuartetKernel GProgram.G5.OriginalCoinLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativeCurrentPortCompiler UnifiedLean.Source.NativeFairCurrentPosition
open UnifiedLean.Source.NativeFairSelectorAssembly
open scoped Classical
variable {V E X G : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def choiceBit (k : Fin 2) : Bool := if k = 0 then false else true
noncomputable def bitChoice (b : Bool) : Fin 2 := if b then 1 else 0

lemma binaryPositions_choiceBit {α : Type*} (p : Bool → α) (k : Fin 2) :
    binaryPositions p k = p (choiceBit k) := by
  fin_cases k <;> simp [binaryPositions,choiceBit]

lemma choiceBit_bitChoice (b : Bool) : choiceBit (bitChoice b) = b := by
  cases b <;> norm_num [choiceBit,bitChoice]

/-- Source-native realization of arbitrary choices, using disjoint actual
hybrid sites. Constant descriptions introduce no extra original coin site. -/
theorem safe_common_register_realizes_group_choices
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (B : Finset X) (tip : G ↪ X)
    (htip : ∀ g, tip g ∈ B) {t : ℝ} (hsafe : SafeAt N C B t)
    (D : ∀ g : G, NativeCurrentDescription N C H (tip g) t) (choice : G → Fin 2) :
    ∃ a : CommonSeed N, ∀ g : G,
      descriptionRead N C hcut H (D g) a = binaryPositions (descriptionPositions N C hcut H (D g)) (choice g) := by
  let site : G → Option (Hybrid N) := fun g => descriptionSite (D g)
  let a : CommonSeed N := fun h =>
    if hx : ∃ g : G, site g = some h then choiceBit (choice (Classical.choose hx)) else false
  have hsite (g : G) (h : Hybrid N) (hg : site g = some h) : a h = choiceBit (choice g) := by
    have hex : ∃ j : G, site j = some h := ⟨g,hg⟩
    have hchosen : Classical.choose hex = g := by
      by_contra hn
      have hne : tip (Classical.choose hex) ≠ tip g := fun he => hn (tip.injective he)
      have hh := common_description_sites_separated N C H B (htip _) (htip g) hne hsafe
        (D (Classical.choose hex)) (D g) h h (Classical.choose_spec hex) hg
      exact hh rfl
    simp only [a,dif_pos hex,hchosen]
  refine ⟨a,?_⟩
  intro g
  rw [binaryPositions_choiceBit]
  unfold descriptionRead
  cases hs : descriptionSite (D g) with
  | none => exact (description_positions_constant N C hcut H (D g) hs (choiceBit (choice g))).symm
  | some h =>
    change descriptionPositions N C hcut H (D g) (a h) = _
    rw [hsite g h hs]

/-- A common register's actual readout is itself one coupled private choice
per original group. Repeated quartet labels use exactly the same group choice. -/
theorem common_group_reads_are_coupled_choices
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (tip : G ↪ X) {t : ℝ}
    (D : ∀ g : G, NativeCurrentDescription N C H (tip g) t) (a : CommonSeed N) :
    ∃ choice : G → Fin 2, ∀ g,
      descriptionRead N C hcut H (D g) a = binaryPositions (descriptionPositions N C hcut H (D g)) (choice g) := by
  let choice : G → Fin 2 := fun g => match descriptionSite (D g) with
    | none => 0
    | some h => bitChoice (a h)
  refine ⟨choice,?_⟩
  intro g
  rw [binaryPositions_choiceBit]
  unfold descriptionRead
  cases hs : descriptionSite (D g) with
  | none => simp [choice,hs,choiceBit]
  | some h => simp [choice,hs,choiceBit_bitChoice]

/-- Exact source-to-coupled-kernel support, derived from actual original sites. -/
theorem safe_common_group_quartet_read_iff_coupled [DecidableEq G]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (B : Finset X) (tip : G ↪ X)
    (htip : ∀ g, tip g ∈ B) {t : ℝ} (hsafe : SafeAt N C B t)
    (D : ∀ g : G, NativeCurrentDescription N C H (tip g) t) (owner : Fin 4 → G) :
    (∃ a : CommonSeed N, quartetAt (fun i => descriptionRead N C hcut H (D (owner i)) a)) ↔
      arbitraryCoupledWitness (fun g => binaryPositions (descriptionPositions N C hcut H (D g))) owner := by
  constructor
  · rintro ⟨a,hw⟩
    obtain ⟨choice,hchoice⟩ := common_group_reads_are_coupled_choices N C hcut H tip D a
    refine ⟨choice,?_⟩
    simpa only [hchoice] using hw
  · rintro ⟨choice,hw⟩
    obtain ⟨a,ha⟩ := safe_common_register_realizes_group_choices N C hcut H B tip htip hsafe D choice
    refine ⟨a,?_⟩
    simpa only [ha] using hw

#print axioms safe_common_register_realizes_group_choices
#print axioms common_group_reads_are_coupled_choices
#print axioms safe_common_group_quartet_read_iff_coupled
end GProgram.G5.AttainedChronology
