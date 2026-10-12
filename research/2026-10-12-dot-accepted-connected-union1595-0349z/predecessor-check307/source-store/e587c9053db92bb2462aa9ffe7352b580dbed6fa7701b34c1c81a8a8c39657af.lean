import UnifiedLean.Source.NativeSafePastGerm
import G5ParentPositionPushforward
import UnifiedLean.Source.SourceNaturalInitialization

/-!
# Native current positions depend on the actual current original parent bit

Contributor: dot / GPT-6.1 Sol, 2026-10-02. This source adapter connects the
constructed native original-tip routes to the actual component parent-position
map. It preserves every original edge occurrence and proves that earlier/later
unused coins cannot change the current position once the actual current port
and component interval are fixed. Fair probabilities are then derived from
actual finite source product weights, rather than inferred from support size.
Safe chronology/current-port selection and COMMON stopped-law admission remain
separate source obligations; no terminal quartet theorem is asserted here.
-/
namespace UnifiedLean.Source.NativeFairCurrentPosition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.ParentCalendar
open GProgram.G5.ComponentSupport GProgram.G5.NonbridgeRoutes GProgram.G5.SafePast
open GProgram.G5.OriginalCoinLaw GProgram.G5.QuartetKernel
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open scoped Classical BigOperators ENNReal NNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
lemma respectsSelector_of_subset (N : RootedBinary V E X) (P : IncomingSelector N)
    {es fs : List E} (hr : RespectsSelector N P es)
    (hf : ∀ e ∈ fs, e ∈ es) : RespectsSelector N P fs := by
  intro e he
  exact hr e (hf e he)

/-- The last edge at an actual hybrid is its SAME selected original parent,
not just one of the two possible parent occurrences. -/
lemma selected_component_last_parent (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool) (h : Hybrid N)
    {entry : V} {es : List E} (hp : EdgePath N.graph entry (H.parents h).hybrid es)
    (hr : RespectsSelector N (coinSelector N H coin) es)
    {f : E} (hf : f ∈ es) :
    ∃ pre : List E, es = pre ++ [(H.parents h).parent (coin h)] := by
  rcases GProgram.G5.ParentCalendar.EdgePath.empty_or_last hp with hnil | ⟨pre,e,hes,hte⟩
  · rw [hnil] at hf
    simp at hf
  · have hem : e ∈ es := by rw [hes]; simp
    obtain ⟨hne,hsel⟩ := hr e hem
    have hev : N.graph.target e = h.val := hte.trans (H.original_site h)
    have hy : N.graph.IsHybrid (N.graph.target e) := hev.symm ▸ h.property
    have hsame : (⟨N.graph.target e,hy⟩ : Hybrid N) = h := Subtype.ext hev
    have hc : e = (H.parents h).parent (coin h) := by
      have hh := hsel.symm
      simp only [coinSelector,dif_pos hy] at hh
      simpa only [hsame] using hh
    exact ⟨pre,by simpa only [hc] using hes⟩

/-- For an actual selected component path, the current population is a
function of exactly its current hybrid's original parent bit. -/
theorem selected_component_position (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool) (h : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (H.parents h).hybrid)
    {t : ℝ} (hl : C.age (H.parents h).hybrid ≤ t) (hu : t < C.age entry)
    {es : List E} (hp : EdgePath N.graph entry (H.parents h).hybrid es)
    (hr : RespectsSelector N (coinSelector N H coin) es)
    {f : E} (hf : f ∈ es) (ha : C.Active t f) :
    f = parentPosition C (H.parents h) he hl hu (coin h) := by
  obtain ⟨pre,hes⟩ := selected_component_last_parent N H coin h hp hr hf
  rw [hes] at hp hf
  exact active_edge_eq_parentPosition C hcut (H.parents h) he hl hu (coin h) hp hf ha

/-- A complete selected root-to-port path retains the exact selected parent
bit when its actual current component suffix is extracted. -/
theorem selected_root_path_position (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool) (h : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (H.parents h).hybrid)
    {t : ℝ} (hl : C.age (H.parents h).hybrid ≤ t) (hu : t < C.age entry)
    {es : List E} (hp : EdgePath N.graph N.root (H.parents h).hybrid es)
    (hr : RespectsSelector N (coinSelector N H coin) es)
    {f : E} (hf : f ∈ es) (ha : C.Active t f) :
    f = parentPosition C (H.parents h) he hl hu (coin h) := by
  rcases he with ⟨hentry,hblob⟩ | ⟨e,hbridge,hentry,hblob⟩
  · subst entry
    exact selected_component_position N C hcut H coin h (Or.inl ⟨rfl,hblob⟩) hl hu hp hr hf ha
  · subst entry
    have hem := incoming_bridge_mem_root_route N hbridge hblob hp
    obtain ⟨pre,post,hes,hpre,hpost⟩ :=
      GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge hp hem
    have hsub : ∀ g ∈ post, g ∈ es := by
      intro g hg
      rw [hes]
      exact List.mem_append_right _ (List.mem_cons_of_mem e hg)
    have hpostr := respectsSelector_of_subset N _ hr hsub
    have hfp : f ∈ post := by
      rw [hes] at hf
      rcases List.mem_append.mp hf with hpr | hpr
      · have hage : C.age (N.graph.source e) ≤ C.age (N.graph.target f) :=
          C.age_le_of_directed (hpre.target_reaches_end_of_mem hpr)
        exact False.elim (not_le_of_gt (hu.trans ((C.edge_older e).trans_le hage)) ha.1)
      · rcases List.mem_cons.mp hpr with hfe | hfp
        · subst f
          exact False.elim (not_le_of_gt hu ha.1)
        · exact hfp
    exact selected_component_position N C hcut H coin h
      (Or.inr ⟨e,hbridge,rfl,hblob⟩) hl hu hpost hpostr hfp ha

/-- Above an actual exit bridge of the current hybrid port, the original-tip
native route's population depends ONLY on that original hybrid's own coin.
All other preassigned bits may vary freely. -/
theorem native_tip_active_edge_eq_current_parent (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (coin : X → Hybrid N → Bool) (x : X) (h : Hybrid N)
    {exit : E} (hexit : N.graph.IsBridge exit)
    (hport : N.graph.source exit = (H.parents h).hybrid)
    (hbelow : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {entry : V} (he : IsComponentEntryFor N entry (H.parents h).hybrid)
    {t : ℝ} (hl : C.age (H.parents h).hybrid ≤ t) (hu : t < C.age entry)
    {f : E} (hf : f ∈ (compiledRouteFamily N C H coin).edges x) (ha : C.Active t f) :
    f = parentPosition C (H.parents h) he hl hu (coin x h) := by
  have hp := (compiledRouteFamily N C H coin).valid x
  have hr := (compiledRoute_source_spec N C (coinSelector N H (coin x)) (N.leaf x)).2
  have hem := bridge_mem_every_descendant_route N hexit hp hbelow
  obtain ⟨pre,post,hes,hpre,hpost⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge hp hem
  have hsub : ∀ g ∈ pre, g ∈ (compiledRouteFamily N C H coin).edges x := by
    intro g hg
    rw [hes]
    exact List.mem_append_left _ hg
  have hpr := respectsSelector_of_subset N _ hr hsub
  have hfp : f ∈ pre := by
    rw [hes] at hf
    rcases List.mem_append.mp hf with hfp | hfp
    · exact hfp
    · rcases List.mem_cons.mp hfp with hfe | hfp
      · subst f
        exact False.elim (not_lt_of_ge (hport ▸ hl) ha.2)
      · have hage : C.age (N.graph.source f) ≤ C.age (N.graph.target exit) :=
          hpost.source_age_le C hfp
        have hle : C.age (N.graph.source f) ≤ t :=
          hage.trans ((le_of_lt (C.edge_older exit)).trans (hport ▸ hl))
        exact False.elim (not_lt_of_ge hle ha.2)
  rw [hport] at hpre
  exact selected_root_path_position N C hcut H (coin x) h he hl hu hpre hpr hfp ha

/-- The actual native route occupies the parent-selected original edge, not
merely an edge in its possible-position image. -/
theorem native_tip_current_parent_spec (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (coin : X → Hybrid N → Bool) (x : X) (h : Hybrid N)
    {exit : E} (hexit : N.graph.IsBridge exit)
    (hport : N.graph.source exit = (H.parents h).hybrid)
    (hbelow : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {entry : V} (he : IsComponentEntryFor N entry (H.parents h).hybrid)
    {t : ℝ} (hl : C.age (H.parents h).hybrid ≤ t) (hu : t < C.age entry) :
    parentPosition C (H.parents h) he hl hu (coin x h) ∈
      (compiledRouteFamily N C H coin).edges x ∧
    C.Active t (parentPosition C (H.parents h) he hl hu (coin x h)) := by
  have hleaf : C.age (N.leaf x) ≤ t :=
    (C.age_le_of_directed hbelow).trans ((C.edge_older exit).le.trans (hport ▸ hl))
  have hroot : t < C.age N.root := hu.trans_le (C.age_le_of_directed (N.rooted entry))
  obtain ⟨f,hf,ha⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C
    ((compiledRouteFamily N C H coin).valid x) hleaf hroot
  have hfparent := native_tip_active_edge_eq_current_parent N C hcut H coin x h
    hexit hport hbelow he hl hu hf ha
  rw [hfparent] at hf ha
  exact ⟨hf,ha⟩

/-- Every co-occupancy event is exactly the equality of the TWO native
current-parent readouts. It is an unconditional original-route event. -/
theorem native_coOccupy_iff_current_parents (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (coin : X → Hybrid N → Bool) (x y : X)
    (h k : Hybrid N) {exitH exitK : E}
    (hxbridge : N.graph.IsBridge exitH) (hybridge : N.graph.IsBridge exitK)
    (hxport : N.graph.source exitH = (H.parents h).hybrid)
    (hyport : N.graph.source exitK = (H.parents k).hybrid)
    (hxbelow : N.graph.DReach (N.graph.target exitH) (N.leaf x))
    (hybelow : N.graph.DReach (N.graph.target exitK) (N.leaf y))
    {entryH entryK : V}
    (heH : IsComponentEntryFor N entryH (H.parents h).hybrid)
    (heK : IsComponentEntryFor N entryK (H.parents k).hybrid)
    {t : ℝ} (hlH : C.age (H.parents h).hybrid ≤ t) (huH : t < C.age entryH)
    (hlK : C.age (H.parents k).hybrid ≤ t) (huK : t < C.age entryK) :
    CoOccupy N (compiledRouteFamily N C H coin) C t x y ↔
      parentPosition C (H.parents h) heH hlH huH (coin x h) =
      parentPosition C (H.parents k) heK hlK huK (coin y k) := by
  constructor
  · rintro ⟨f,hfx,hfy,ha⟩
    have hx := native_tip_active_edge_eq_current_parent N C hcut H coin x h
      hxbridge hxport hxbelow heH hlH huH hfx ha
    have hy := native_tip_active_edge_eq_current_parent N C hcut H coin y k
      hybridge hyport hybelow heK hlK huK hfy ha
    exact hx.symm.trans hy
  · intro hp
    have hx := native_tip_current_parent_spec N C hcut H coin x h
      hxbridge hxport hxbelow heH hlH huH
    have hy := native_tip_current_parent_spec N C hcut H coin y k
      hybridge hyport hybelow heK hlK huK
    exact ⟨_,hx.1,hp ▸ hy.1,hx.2⟩

/-- Fairness is an ORIGINAL source parameter assignment, not a fitted current
position law. Every original hybrid has its genuine natural weight one half. -/
noncomputable def fairParameters (N : RootedBinary V E X) : HybridProbabilities N where
  gamma _ := 1/2
  positive _ := by norm_num
  below_one _ := by norm_num

omit [DecidableEq E] in
lemma originalCoinMass_fair (N : RootedBinary V E X) (a : NativeCoinSeed N) :
    originalCoinMass N (fairParameters N) a =
      (GProgram.SourceForest.independentWeight (1/2) a : ℝ) := by
  unfold originalCoinMass GProgram.SourceForest.independentWeight
  simp only [fairParameters, Rat.cast_prod, bitWeight_fair]
  apply Finset.prod_congr rfl
  intro i _
  cases a i <;> norm_num

/-- Exact binding of the actual native fair original-site PMF to the inherited
finite fair source law. All other potential original coin sites are retained. -/
theorem originalCoinPMF_fair (N : RootedBinary V E X) :
    originalCoinPMF N (fairParameters N) =
      (independentPMF (1/2) (by norm_num) (by norm_num) : PMF (NativeCoinSeed N)) := by
  apply PMF.ext
  intro a
  simp only [originalCoinPMF, independentPMF, PMF.ofFintype_apply, originalCoinMass_fair]

/-- A current-port description consists solely of actual original graph and
calendar facts. No position, probability or source-law equality is a field. -/
structure CurrentHybridPort (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x : X) (t : ℝ) where
  site : Hybrid N
  exit : E
  exit_bridge : N.graph.IsBridge exit
  port : N.graph.source exit = (H.parents site).hybrid
  below : N.graph.DReach (N.graph.target exit) (N.leaf x)
  entry : V
  component : IsComponentEntryFor N entry (H.parents site).hybrid
  lower : C.age (H.parents site).hybrid ≤ t
  upper : t < C.age entry

noncomputable def currentParentPosition {N : RootedBinary V E X} {C : Calendar N.graph}
    {H : OriginalParentRegistry N} {x : X} {t : ℝ}
    (P : CurrentHybridPort N C H x t) : Bool → E :=
  parentPosition C (H.parents P.site) P.component P.lower P.upper

lemma native_cooccupy_port_readout (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} {t : ℝ}
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t)
    (a : NativeCoinSeed N) :
    CoOccupy N (seededRoutes N C H a) C t x y ↔
      currentParentPosition P (a (x,P.site)) = currentParentPosition Q (a (y,Q.site)) :=
  native_coOccupy_iff_current_parents N C hcut H (fun x h => a (x,h)) x y P.site Q.site
    P.exit_bridge Q.exit_bridge P.port Q.port P.below Q.below
    P.component Q.component P.lower P.upper Q.lower Q.upper

/-- The genuine original native fair coin PMF gives actual current population
co-occupancy equal to its two-selector count/4. All unused original sites have
been integrated out by the inherited finite-source PMF theorem. -/
theorem native_fair_current_meeting_probability (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} (hne : x ≠ y) {t : ℝ}
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t) :
    (originalCoinPMF N (fairParameters N)).toOuterMeasure
      {a | CoOccupy N (seededRoutes N C H a) C t x y} =
      fairMeetingMass (binaryPositions (currentParentPosition P))
        (binaryPositions (currentParentPosition Q)) := by
  have hs : (x,P.site) ≠ (y,Q.site) := fun h => hne (congrArg Prod.fst h)
  have hevent : {a | CoOccupy N (seededRoutes N C H a) C t x y} =
      {a | currentParentPosition P (a (x,P.site)) = currentParentPosition Q (a (y,Q.site))} := by
    ext a
    exact native_cooccupy_port_readout N C hcut H P Q a
  rw [hevent,originalCoinPMF_fair]
  exact fair_source_meeting_probability hs _ _

/-- At a safe stage, the native zero-rate coefficient supplies the complement
of that exact fair selector count. This connects actual graph routing and
original fair weights DIRECTLY to the earlier germ endpoint. -/
theorem safe_native_zero_coefficient_eq_fair_selector_count (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (hsafe : SafeAt N C B t)
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t) :
    UnifiedLean.Source.NativeSafePastGerm.nativeGermCoefficients N C H
      (fairParameters N) r x y t 0 =
      1-(pairCount (binaryPositions (currentParentPosition P))
          (binaryPositions (currentParentPosition Q)) : ℝ)/4 := by
  have ht : t < C.age N.root := P.upper.trans_le (C.age_le_of_directed (N.rooted P.entry))
  rw [UnifiedLean.Source.NativeSafePastGerm.safe_native_zero_coefficient
    N C H (fairParameters N) r B hx hy hne ht hsafe]
  have hs : (x,P.site) ≠ (y,Q.site) := fun h => hne (congrArg Prod.fst h)
  have hq := fair_source_meeting_weight hs (currentParentPosition P) (currentParentPosition Q)
  have hreal : (∑ a : NativeCoinSeed N, originalCoinMass N (fairParameters N) a *
      (if currentParentPosition P (a (x,P.site)) = currentParentPosition Q (a (y,Q.site))
        then 1 else 0)) =
      (pairCount (binaryPositions (currentParentPosition P))
        (binaryPositions (currentParentPosition Q)) : ℝ)/4 := by
    simp_rw [originalCoinMass_fair]
    have hh := congrArg (fun z : ℚ => (z : ℝ)) hq
    push_cast at hh
    simpa only [apply_ite, Rat.cast_one, Rat.cast_zero] using hh
  have hsum : UnifiedLean.Source.NativeSafePastGerm.nativeSeparationMass
      N C H (fairParameters N) x y t +
      (∑ a : NativeCoinSeed N, originalCoinMass N (fairParameters N) a *
        (if currentParentPosition P (a (x,P.site)) = currentParentPosition Q (a (y,Q.site))
          then 1 else 0)) = 1 := by
    rw [UnifiedLean.Source.NativeSafePastGerm.nativeSeparationMass,← Finset.sum_add_distrib]
    convert originalCoinMass_normalized N (fairParameters N) using 1
    apply Finset.sum_congr rfl
    intro a _
    rw [native_cooccupy_port_readout N C hcut H P Q a]
    split_ifs <;> simp_all
  rw [hreal] at hsum
  linarith

/-- At an ordinary current port the actual native original-tip population is
constant under EVERY original coin assignment. This derives the concentrated
branch rather than inferring it from a fitted binary position map. -/
theorem native_ordinary_port_constant (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {exit : E} (he : N.graph.IsBridge exit)
    {x : X} (hbelow : N.graph.DReach (N.graph.target exit) (N.leaf x))
    (ho : ¬N.graph.IsHybrid (N.graph.source exit)) {t : ℝ}
    (ht : InCurrentComponentInterval N C (N.graph.source exit) t) :
    ∃ f : E, ∀ coin : X → Hybrid N → Bool,
      f ∈ (compiledRouteFamily N C H coin).edges x ∧ C.Active t f ∧
      ∀ g ∈ (compiledRouteFamily N C H coin).edges x, C.Active t g → g = f := by
  have hc := current_ordinary_port_support_card_eq_one N C hcut ho ht
  obtain ⟨f,hf⟩ := Finset.card_eq_one.mp hc
  refine ⟨f,?_⟩
  intro coin
  have hleaf : C.age (N.leaf x) ≤ t :=
    (C.age_le_of_directed hbelow).trans ((C.edge_older exit).le.trans ht.1)
  have hroot : t < C.age N.root := by
    rcases ht.2 with ⟨_,hu⟩ | ⟨entry,_,_,hu⟩
    · exact hu
    · exact hu.trans_le (C.age_le_of_directed (N.rooted (N.graph.target entry)))
  have huniq : ∀ g ∈ (compiledRouteFamily N C H coin).edges x, C.Active t g → g = f := by
    intro g hg ha
    have hmem : g ∈ activeRootRouteEdges N.graph C N.root (N.leaf x) t :=
      (mem_activeRootRouteEdges_iff _ _ _ _ _ _).mpr
        ⟨_,(compiledRouteFamily N C H coin).valid x,hg,ha⟩
    rw [original_tip_support_eq_port N C he hbelow ht.1,hf,Finset.mem_singleton] at hmem
    exact hmem
  obtain ⟨g,hg,ha⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C
    ((compiledRouteFamily N C H coin).valid x) hleaf hroot
  have heq := huniq g hg ha
  rw [heq] at hg ha
  exact ⟨hg,ha,huniq⟩

open MeasureTheory ProbabilityTheory
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceForestPulseMeasure

omit [DecidableEq E] in
lemma fair_original_register_bit_mass (N : RootedBinary V E X) (h : Hybrid N) (b : Bool) :
    bitMeasure (originalGamma (fairParameters N) h) {b} = ENNReal.ofReal (1/2) := by
  cases b <;> simp [bitMeasure, bernoulliMeasure, originalGamma, fairParameters,
    unitInterval.toNNReal, unitInterval.symm] <;>
    apply (ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (by norm_num)).mp <;>
    norm_num [ENNReal.coe_toReal, NNReal.coe_mk] <;> rfl

/-- The SAME once-drawn original COMMON register measure has the genuine fair
finite original-site PMF. This theorem does not replace its site coupling by
independent copy-indexed registers. -/
theorem original_common_fair_seed_PMF (N : RootedBinary V E X) :
    (originalRegisterMeasure N (fairParameters N)).toPMF =
      (independentPMF (1/2) (by norm_num) (by norm_num) : PMF (Hybrid N → Bool)) := by
  apply PMF.ext
  intro a
  rw [Measure.toPMF_apply,originalRegisterMeasure,Measure.pi_singleton]
  simp_rw [fair_original_register_bit_mass]
  simp only [independentPMF,PMF.ofFintype_apply,GProgram.SourceForest.independentWeight,
    bitWeight_fair,Rat.cast_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by norm_num)]
  norm_num

/-- On distinct actual COMMON sites the native compiled original routes have
exactly the same fair-selector count law. Unused site bits are marginalized;
this is a current-position law, not yet the COMMON stopped-pair prefix law. -/
theorem native_common_fair_current_meeting_probability (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} {t : ℝ}
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t)
    (hsites : P.site ≠ Q.site) :
    ((originalRegisterMeasure N (fairParameters N)).toPMF).toOuterMeasure
      {a | CoOccupy N (compiledRouteFamily N C H (fun _ h => a h)) C t x y} =
      fairMeetingMass (binaryPositions (currentParentPosition P))
        (binaryPositions (currentParentPosition Q)) := by
  have hevent : {a : Hybrid N → Bool | CoOccupy N (compiledRouteFamily N C H (fun _ h => a h)) C t x y} =
      {a : Hybrid N → Bool | currentParentPosition P (a P.site) = currentParentPosition Q (a Q.site)} := by
    ext a
    exact native_coOccupy_iff_current_parents N C hcut H (fun _ h => a h) x y P.site Q.site
      P.exit_bridge Q.exit_bridge P.port Q.port P.below Q.below
      P.component Q.component P.lower P.upper Q.lower Q.upper
  rw [hevent,original_common_fair_seed_PMF]
  exact fair_source_meeting_probability hsites _ _

/-- Entire-safe-past geometry DERIVES that retained original tips' actual
current hybrid coordinates are distinct. It is not an independence premise. -/
theorem safe_current_hybrid_sites_distinct (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (B : Finset X) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ} (hsafe : SafeAt N C B t)
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t) : P.site ≠ Q.site := by
  have hp : N.graph.DReach P.site.val (N.leaf x) := by
    rw [← H.original_site P.site,← P.port]
    exact (Relation.ReflTransGen.single ⟨P.exit,rfl,rfl⟩).trans P.below
  have hq : N.graph.DReach Q.site.val (N.leaf y) := by
    rw [← H.original_site Q.site,← Q.port]
    exact (Relation.ReflTransGen.single ⟨Q.exit,rfl,rfl⟩).trans Q.below
  intro heq
  rw [← heq] at hq
  have hage : C.age P.site.val ≤ t := by rw [← H.original_site P.site]; exact P.lower
  exact shared_ancestor_not_hybrid N C B hsafe hx hy hne hp hq hage P.site.property

/-- Actual independent CURRENT-tip seeds and SAME-site COMMON registers have
identical native current co-occupancy law at the safe stage. This is derived
from actual path dependence and SafeAt, not from a mode-erasing route field.
The COMMON stopped-prefix survival law remains a separate admission. -/
theorem safe_common_independent_current_meeting_probability (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (B : Finset X) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ} (hsafe : SafeAt N C B t)
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t) :
    ((originalRegisterMeasure N (fairParameters N)).toPMF).toOuterMeasure
      {a | CoOccupy N (compiledRouteFamily N C H (fun _ h => a h)) C t x y} =
    (originalCoinPMF N (fairParameters N)).toOuterMeasure
      {a | CoOccupy N (seededRoutes N C H a) C t x y} := by
  rw [native_common_fair_current_meeting_probability N C hcut H P Q
      (safe_current_hybrid_sites_distinct N C H B hx hy hne hsafe P Q),
    native_fair_current_meeting_probability N C hcut H hne P Q]

#print axioms safe_current_hybrid_sites_distinct
#print axioms safe_common_independent_current_meeting_probability
#print axioms native_ordinary_port_constant
#print axioms original_common_fair_seed_PMF
#print axioms native_common_fair_current_meeting_probability
#print axioms native_fair_current_meeting_probability
#print axioms safe_native_zero_coefficient_eq_fair_selector_count
#print axioms native_tip_current_parent_spec
#print axioms native_coOccupy_iff_current_parents
#print axioms originalCoinPMF_fair
#print axioms selected_component_last_parent
#print axioms selected_component_position
#print axioms selected_root_path_position
#print axioms native_tip_active_edge_eq_current_parent
end UnifiedLean.Source.NativeFairCurrentPosition
