import G5OriginalTipRepresentativeDeletion
import UnifiedLean.Source.NativeCommonPairGerm

/-!
# ALL-COMMON original-selector group persistence, including the root
Contributor: dot / OpenAI, 2026-10-03.
A common switching uses one unchanged original incoming selector. Shared
population paths remain shared through later hybrids because the selector is
identical there. Arbitrary independently selected RouteFamily paths are not
claimed to have this global property. No posterior or re-coin is involved.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast GProgram.G5.NonbridgeRoutes
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma selected_edges_equal (N : RootedBinary V E X) (P : IncomingSelector N)
    {es fs : List E} (hP : RespectsSelector N P es) (hQ : RespectsSelector N P fs)
    {e f : E} (he : e ∈ es) (hf : f ∈ fs)
    (ht : N.graph.target e = N.graph.target f) : e = f := by
  obtain ⟨hne,hsel⟩ := hP e he
  obtain ⟨hnf,hself⟩ := hQ f hf
  have hv : (⟨N.graph.target e,hne⟩ : Nonroot N) = ⟨N.graph.target f,hnf⟩ := Subtype.ext ht
  rw [hv] at hsel
  exact hsel.symm.trans hself

lemma respectsSelector_reverse (N : RootedBinary V E X) (P : IncomingSelector N)
    {es : List E} (hP : RespectsSelector N P es) : RespectsSelector N P es.reverse :=
  fun e he => hP e (List.mem_reverse.mp he)

/-- Actual local selected incoming edges, including hybrid parents, force the
same older active edge. No global safe-past hypothesis is used or needed. -/
theorem UpPath.active_edges_equal_of_same_selector
    (N : RootedBinary V E X) (C : Calendar N.graph) (P : IncomingSelector N) {t : ℝ}
    {a b : V} {es fs : List E} (p : UpPath N.graph (fun _ => True) a b es)
    (q : UpPath N.graph (fun _ => True) a b fs)
    (hP : RespectsSelector N P es) (hQ : RespectsSelector N P fs)
    (hl : C.age a ≤ t) (hu : t < C.age b)
    {f g : E} (hf : f ∈ es) (hg : g ∈ fs) (hfa : C.Active t f) (hga : C.Active t g) :
    f = g := by
  induction p generalizing fs f g with
  | nil a => exact False.elim (not_lt_of_ge hl hu)
  | @cons a b e es ht he rest ih =>
    cases q with
    | nil => exact False.elim (not_lt_of_ge hl hu)
    | @cons _ _ d ds htd hd qrest =>
      have hed : e = d := selected_edges_equal N P hP hQ List.mem_cons_self List.mem_cons_self (ht.trans htd.symm)
      subst d
      by_cases hls : C.age (N.graph.source e) ≤ t
      · have hfn : f ≠ e := by
          intro h; subst f
          exact not_lt_of_ge hls hfa.2
        have hgn : g ≠ e := by
          intro h; subst g
          exact not_lt_of_ge hls hga.2
        have hft : f ∈ es := (List.mem_cons.mp hf).resolve_left hfn
        have hgt : g ∈ ds := (List.mem_cons.mp hg).resolve_left hgn
        exact ih qrest (fun j hj => hP j (List.mem_cons_of_mem e hj))
          (fun j hj => hQ j (List.mem_cons_of_mem e hj)) hls hu hft hgt hfa hga
      · have hae : C.Active t e := ⟨by simpa only [ht] using hl,lt_of_not_ge hls⟩
        have hfe : f = e := (UpPath.to_edgePath_reverse (.cons ht he rest)).active_unique
          C (List.mem_reverse.mpr hf) (List.mem_reverse.mpr List.mem_cons_self) hfa hae
        have hge : g = e := (UpPath.to_edgePath_reverse (.cons htd hd qrest)).active_unique
          C (List.mem_reverse.mpr hg) (List.mem_reverse.mpr List.mem_cons_self) hga hae
        exact hfe.trans hge.symm

/-- Shared original populations persist rootward under the SAME selector even
past later shared hybrids. This is not independent-route permanence. -/
theorem same_selector_coOccupy_persists (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (R : RouteFamily N)
    (hR : ∀ x, RespectsSelector N P (R.edges x)) {u t : ℝ}
    (hut : u ≤ t) (hu : t < C.age N.root) {x y : X}
    (hmeeting : CoOccupy N R C u x y) : CoOccupy N R C t x y := by
  obtain ⟨e,hex,hey,heactive⟩ := hmeeting
  by_cases hls : C.age (N.graph.source e) ≤ t
  · obtain ⟨px,sx,hxroute,hpx,hsx⟩ :=
      GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (R.valid x) hex
    obtain ⟨py,sy,hyroute,hpy,hsy⟩ :=
      GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (R.valid y) hey
    obtain ⟨f,hfx,hfa⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hpx hls hu
    obtain ⟨g,hgy,hga⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hpy hls hu
    have hPx : RespectsSelector N P px := by
      intro j hj
      apply hR x
      rw [hxroute]
      exact List.mem_append_left _ hj
    have hPy : RespectsSelector N P py := by
      intro j hj
      apply hR y
      rw [hyroute]
      exact List.mem_append_left _ hj
    have hfg : f = g := UpPath.active_edges_equal_of_same_selector N C P
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hpx (fun _ _ => trivial))
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hpy (fun _ _ => trivial))
      (respectsSelector_reverse N P hPx) (respectsSelector_reverse N P hPy) hls hu
      (List.mem_reverse.mpr hfx) (List.mem_reverse.mpr hgy) hfa hga
    subst g
    refine ⟨f,?_,?_,hfa⟩
    · rw [hxroute]; exact List.mem_append_left _ hfx
    · rw [hyroute]; exact List.mem_append_left _ hgy
  · exact ⟨e,hex,hey,heactive.1.trans hut,lt_of_not_ge hls⟩

/-- Includes the actual ancestral none population. -/
def SharesPopulation (N : RootedBinary V E X) (R : RouteFamily N) (C : Calendar N.graph)
    (t : ℝ) (x y : X) : Prop :=
  ∃ p : Option E, Occupies N R C t x p ∧ Occupies N R C t y p

theorem common_switching_persistence (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) {u t : ℝ} (hut : u ≤ t)
    {x y : X} (h : SharesPopulation N (commonRoutes N C H a) C u x y) :
    SharesPopulation N (commonRoutes N C H a) C t x y := by
  by_cases hroot : C.age N.root ≤ t
  · exact ⟨none,hroot,hroot⟩
  · obtain ⟨p,hp,hq⟩ := h
    cases p with
    | none => exact False.elim (hroot (hp.trans hut))
    | some e =>
      have hmeet : CoOccupy N (commonRoutes N C H a) C u x y := ⟨e,hp.1,hq.1,hp.2⟩
      have hR : ∀ z, RespectsSelector N (coinSelector N H a) ((commonRoutes N C H a).edges z) :=
        fun z => (compiledRoute_source_spec N C (coinSelector N H a) (N.leaf z)).2
      obtain ⟨f,hfx,hfy,hfa⟩ := same_selector_coOccupy_persists N C (coinSelector N H a)
        (commonRoutes N C H a) hR hut (lt_of_not_ge hroot) hmeet
      exact ⟨some f,⟨hfx,hfa⟩,⟨hfy,hfa⟩⟩

/-- A sure exact block's original labels follow its retained original tip in
EVERY complete original COMMON switching, through all later ages and root. -/
theorem sure_block_original_representative_persistence [LinearOrder X]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (B D : Finset X) {u t : ℝ} (hut : u ≤ t) (hD : 2 ≤ D.card)
    (hblock : SureBlock N C B D u) {x : X} (hx : x ∈ D) :
    ∀ a : CommonSeed N, SharesPopulation N (commonRoutes N C H a) C t x (originalRepresentative D hD) := by
  intro a
  obtain ⟨p,hp⟩ := hblock (commonRoutes N C H a)
  have hxpop : x ∈ populationBlock N (commonRoutes N C H a) B C u p := by rw [hp]; exact hx
  have hrpop : originalRepresentative D hD ∈ populationBlock N (commonRoutes N C H a) B C u p := by
    rw [hp]; exact originalRepresentative_mem D hD
  exact common_switching_persistence N C H a hut
    ⟨p,(Finset.mem_filter.mp hxpop).2,(Finset.mem_filter.mp hrpop).2⟩

#print axioms UpPath.active_edges_equal_of_same_selector
#print axioms same_selector_coOccupy_persists
#print axioms common_switching_persistence
#print axioms sure_block_original_representative_persistence
end GProgram.G5.AttainedChronology
