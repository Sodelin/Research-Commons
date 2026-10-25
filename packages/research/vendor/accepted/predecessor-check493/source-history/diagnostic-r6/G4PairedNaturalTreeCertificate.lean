import G4WholeProfileDetermination
import G4ActualBelowMeetingSupport
import G5NativeOriginalRouteCoverage
import G1ActualWholeUnrootedCutTreeFamily
import G7CalendarFrontierOrder
set_option stderrAsMessages false
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC after imports"
  (← IO.getStderr).flush

/-!
# Actual paired natural ordinary-tree certificate

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED source development.
Formalization of the independently accepted paired natural certificate and
one-bit geometric proof. The single intended endpoint includes actual natural
INDEPENDENT readout and all-future BOTH responses; the present file is a complete uncompiled candidate.
No new mathematical result, build acceptance or general G4 closure is claimed.
-/
namespace DotG4.PairedNaturalTreeCertificate
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open Nanuq.Source GProgram.G5 GProgram.G5.NonbridgeRoutes
open GProgram.G5.AttainedChronology GProgram.G5.ComponentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open DotG4.ActualObservableBankCertificate DotG4.ActualNaturalCombMoments
open DotG4.ActualSelectedPathExposure DotG4.ActualBankFirstMeeting
open scoped Classical BigOperators ENNReal NNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Only original finite-edge hazards appear in the geometric comparison. -/
noncomputable def edgeHazard (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) : ℝ :=
  pairRate r (some e) * (C.age (N.graph.source e) - C.age (N.graph.target e))

lemma edgeHazard_pos (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) : 0 < edgeHazard N C r e :=
  mul_pos (pairRate_pos r (some e)) (sub_pos.mpr (C.edge_older e))

lemma realSurvival_eq_selected_path (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (coin : Hybrid N → Bool) :
    realSurvival N C H p r i j coin = Real.exp (-selectedDirectedExposure N C H r coin i j) := by
  simp only [realSurvival,bankSurvival,ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [actual_bank_cut_eq_selected_path]

/-- The observed calibration is bound to the actual selected original edge
coordinate; it is not a supplied mixture or a new calibration assumption. -/
theorem actual_calibration_selected_path_constant (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (i j : X)
    (h : 18 * combProbability N C H p r i j 3 =
      (3 * combProbability N C H p r i j 2)^3)
    (a b : Hybrid N → Bool) :
    selectedDirectedExposure N C H r a i j = selectedDirectedExposure N C H r b i j := by
  have hc := (actual_cubic_observation_iff_constant N C H p r i j).mp h
  have he := (hc a).trans (hc b).symm
  rw [realSurvival_eq_selected_path,realSurvival_eq_selected_path] at he
  exact neg_injective (Real.exp_injective he)

lemma selected_path_unique (N : RootedBinary V E X) (P : IncomingSelector N)
    {a b : V} {es fs : List E} (he : EdgePath N.graph a b es)
    (hf : EdgePath N.graph a b fs) (hs : RespectsSelector N P es)
    (ht : RespectsSelector N P fs) : es = fs := by
  apply List.reverse_inj.mp
  exact UpPath.eq_of_same_selector N P
    (EdgePath.to_upPath_reverse he (fun _ _ => trivial))
    (EdgePath.to_upPath_reverse hf (fun _ _ => trivial))
    (respectsSelector_reverse N P hs) (respectsSelector_reverse N P ht)

lemma respects_sublist (N : RootedBinary V E X) (P : IncomingSelector N)
    {es fs : List E} (hs : RespectsSelector N P fs) (h : ∀ e ∈ es, e ∈ fs) :
    RespectsSelector N P es := fun e he => hs e (h e he)

/-- Incoming-selector agreement is a pointwise physical statement. -/
def SelectorsAgreeExcept (N : RootedBinary V E X) (P Q : IncomingSelector N) (h : V) : Prop :=
  ∀ v : Nonroot N, v.1 ≠ h → P.edge v = Q.edge v

lemma coin_selectors_agree_except (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (a b : Hybrid N → Bool) (h : Hybrid N)
    (hab : ∀ k, k ≠ h → a k = b k) :
    SelectorsAgreeExcept N (coinSelector N H a) (coinSelector N H b) h.1 := by
  intro v hv
  by_cases hy : N.graph.IsHybrid v.1
  · have hne : (⟨v.1,hy⟩ : Hybrid N) ≠ h := by
      intro hh
      exact hv (congrArg Subtype.val hh)
    simp only [coinSelector,dif_pos hy,hab _ hne]
  · simp only [coinSelector,dif_neg hy]

lemma selected_edges_eq_away (N : RootedBinary V E X) (P Q : IncomingSelector N)
    (h : V) (hPQ : SelectorsAgreeExcept N P Q h)
    {es fs : List E} (hp : RespectsSelector N P es) (hq : RespectsSelector N Q fs)
    {e f : E} (he : e ∈ es) (hf : f ∈ fs)
    (ht : N.graph.target e = N.graph.target f) (hne : N.graph.target e ≠ h) : e = f := by
  obtain ⟨hr,her⟩ := hp e he
  obtain ⟨hs,hfs⟩ := hq f hf
  have hv : (⟨N.graph.target e,hr⟩ : Nonroot N) = ⟨N.graph.target f,hs⟩ :=
    Subtype.ext ht
  calc
    e = P.edge ⟨N.graph.target e,hr⟩ := her.symm
    _ = Q.edge ⟨N.graph.target e,hr⟩ := hPQ _ hne
    _ = Q.edge ⟨N.graph.target f,hs⟩ := congrArg Q.edge hv
    _ = f := hfs

/-- A selected younger path ending at h is unchanged when only h's incoming
selector changes. The common older remainder is not asserted or exposed. -/
lemma upPath_prefix_agreement (N : RootedBinary V E X)
    (P Q : IncomingSelector N) (h : V) (hPQ : SelectorsAgreeExcept N P Q h)
    {a : V} {es fs : List E} (p : UpPath N.graph (fun _ => True) a h es)
    (q : UpPath N.graph (fun _ => True) a N.root fs)
    (hp : RespectsSelector N P es) (hq : RespectsSelector N Q fs)
    (havoid : ∀ e ∈ es, N.graph.target e ≠ h) :
    ∃ tail, fs = es ++ tail ∧ UpPath N.graph (fun _ => True) h N.root tail := by
  induction p generalizing fs with
  | nil => exact ⟨fs,rfl,q⟩
  | @cons a z e es ht he rest ih =>
    cases q with
    | nil => exact False.elim (original_edge_target_not_root N e ht)
    | @cons _ _ f fs htf hf tail =>
      have hef : e = f := selected_edges_eq_away N P Q z hPQ hp hq
        List.mem_cons_self List.mem_cons_self (ht.trans htf.symm)
        (havoid e List.mem_cons_self)
      subst f
      obtain ⟨us,hus,hup⟩ := ih hPQ tail
        (fun d hd => hp d (List.mem_cons_of_mem e hd))
        (fun d hd => hq d (List.mem_cons_of_mem e hd))
        (fun d hd => havoid d (List.mem_cons_of_mem e hd))
      exact ⟨us,by simp only [List.cons_append,hus],hup⟩

lemma upPath_target_younger (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} {es : List E} (p : UpPath N.graph (fun _ => True) a b es)
    {e : E} (he : e ∈ es) : C.age (N.graph.target e) < C.age b := by
  have hs := (UpPath.to_edgePath_reverse p).source_age_le C (List.mem_reverse.mpr he)
  exact (C.edge_older e).trans_le hs

lemma upPath_ending_avoids_target (N : RootedBinary V E X) (C : Calendar N.graph)
    {a h : V} {es : List E} (p : UpPath N.graph (fun _ => True) a h es) :
    ∀ e ∈ es, N.graph.target e ≠ h := by
  intro e he hh
  have hz := upPath_target_younger N C p he
  simpa only [hh,lt_self_iff_false] using hz

lemma upPath_prefix_agreement_calendar (N : RootedBinary V E X) (C : Calendar N.graph)
    (P Q : IncomingSelector N) (h : V) (hPQ : SelectorsAgreeExcept N P Q h)
    {a : V} {es fs : List E} (p : UpPath N.graph (fun _ => True) a h es)
    (q : UpPath N.graph (fun _ => True) a N.root fs)
    (hp : RespectsSelector N P es) (hq : RespectsSelector N Q fs) :
    ∃ tail, fs = es ++ tail ∧ UpPath N.graph (fun _ => True) h N.root tail :=
  upPath_prefix_agreement N P Q h hPQ p q hp hq (upPath_ending_avoids_target N C p)

/-- If the changed site is absent, the whole original path is unchanged. -/
lemma upPath_avoiding_agreement (N : RootedBinary V E X)
    (P Q : IncomingSelector N) (h : V) (hPQ : SelectorsAgreeExcept N P Q h)
    {a : V} {es fs : List E}
    (p : UpPath N.graph (fun _ => True) a N.root es)
    (q : UpPath N.graph (fun _ => True) a N.root fs)
    (hp : RespectsSelector N P es) (hq : RespectsSelector N Q fs)
    (havoid : ∀ e ∈ es, N.graph.target e ≠ h) : es = fs := by
  apply UpPath.eq_of_same_selector N Q p q ?_ hq
  intro e he
  obtain ⟨hr,her⟩ := hp e he
  exact ⟨hr,(hPQ ⟨N.graph.target e,hr⟩ (havoid e he)).symm.trans her⟩

lemma edgePath_nodup (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} {es : List E} (p : EdgePath N.graph a b es) : es.Nodup := by
  induction p with
  | nil => exact List.nodup_nil
  | @cons a b e es hs rest ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro he
    have hz := rest.source_age_le C he
    exact not_lt_of_ge hz (C.edge_older e)

lemma selected_prefix_to_target (N : RootedBinary V E X) (P : IncomingSelector N)
    {a b : V} {es : List E} (p : EdgePath N.graph a b es)
    (hp : RespectsSelector N P es) {e : E} (he : e ∈ es) :
    ∃ pre post, es = (pre ++ [e]) ++ post ∧
      EdgePath N.graph a (N.graph.target e) (pre ++ [e]) ∧
      RespectsSelector N P (pre ++ [e]) := by
  obtain ⟨pre,post,hlist,hpre,hpost⟩ := GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge p he
  refine ⟨pre,post,by simpa only [commonRoutes,compiledRouteFamily,List.append_assoc,List.singleton_append] using hlist,
    hpre.append (.cons rfl (.nil _)),?_⟩
  intro d hd
  apply hp d
  rw [hlist]
  simpa only [List.mem_append,List.mem_singleton,List.mem_cons] using
    (show d ∈ pre ∨ d = e ∨ d ∈ post from
      (List.mem_append.mp hd).elim (fun h => Or.inl h)
        (fun h => Or.inr (Or.inl (List.mem_singleton.mp h))))

lemma first_edges_eq_of_shared_target (N : RootedBinary V E X) (P : IncomingSelector N)
    {a b c : V} {e f : E} {es fs : List E}
    (p : EdgePath N.graph a b (e :: es)) (q : EdgePath N.graph a c (f :: fs))
    (hp : RespectsSelector N P (e :: es)) (hq : RespectsSelector N P (f :: fs))
    {d g : E} (hd : d ∈ e :: es) (hg : g ∈ f :: fs)
    (ht : N.graph.target d = N.graph.target g) : e = f := by
  obtain ⟨pre,post,he,hpre,hs⟩ := selected_prefix_to_target N P p hp hd
  obtain ⟨pre',post',hf,hpre',hs'⟩ := selected_prefix_to_target N P q hq hg
  have hpaths : pre ++ [d] = pre' ++ [g] :=
    selected_path_unique N P hpre (by simpa only [ht] using hpre') hs hs'
  rw [← hpaths] at hf
  have hne : pre ++ [d] ≠ [] := by simp
  generalize hz : pre ++ [d] = zs at he hf hne
  cases zs with
  | nil => exact False.elim (hne rfl)
  | cons z zs =>
    simp only [List.cons_append,List.cons.injEq] at he hf
    exact he.1.trans hf.1.symm

/-- A genuine original path fork. No common younger vertex is hidden in the
terminal edge lists; parallel edge occurrences are retained. -/
structure PathFork (N : RootedBinary V E X) (a b c : V) (es fs : List E) where
  vertex : V
  stem : List E
  left : List E
  right : List E
  left_eq : es = stem ++ left
  right_eq : fs = stem ++ right
  stem_path : EdgePath N.graph a vertex stem
  left_path : EdgePath N.graph vertex b left
  right_path : EdgePath N.graph vertex c right
  separate : ∀ e ∈ left, ∀ f ∈ right, N.graph.target e ≠ N.graph.target f

lemma selected_path_fork (N : RootedBinary V E X) (P : IncomingSelector N)
    {a b c : V} {es fs : List E} (p : EdgePath N.graph a b es)
    (q : EdgePath N.graph a c fs) (hp : RespectsSelector N P es)
    (hq : RespectsSelector N P fs) : Nonempty (PathFork N a b c es fs) := by
  induction p generalizing c fs with
  | nil a =>
    exact ⟨⟨a,[],[],fs,rfl,rfl,.nil a,.nil a,q,by intro e he; simp at he⟩⟩
  | @cons a b e es hs rest ih =>
    cases q with
    | nil =>
      exact ⟨⟨a,[],e::es,[],rfl,rfl,.nil a,.cons hs rest,.nil a,
        by intro d hd f hf; simp at hf⟩⟩
    | @cons _ c f fs ht tail =>
      by_cases hef : e = f
      · subst f
        obtain ⟨F⟩ := ih tail (fun d hd => hp d (List.mem_cons_of_mem e hd))
          (fun d hd => hq d (List.mem_cons_of_mem e hd))
        exact ⟨⟨F.vertex,e::F.stem,F.left,F.right,
          by simp [F.left_eq],by simp [F.right_eq],.cons hs F.stem_path,
          F.left_path,F.right_path,F.separate⟩⟩
      · refine ⟨⟨a,[],e::es,f::fs,rfl,rfl,.nil a,.cons hs rest,.cons ht tail,?_⟩⟩
        intro d hd g hg htarget
        exact hef (first_edges_eq_of_shared_target N P (.cons hs rest) (.cons ht tail)
          hp hq hd hg htarget)

noncomputable def pathHazard (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (es : List E) : ℝ := (es.map (edgeHazard N C r)).sum

lemma pathHazard_append (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (es fs : List E) :
    pathHazard N C r (es ++ fs) = pathHazard N C r es + pathHazard N C r fs := by
  simp [pathHazard]

lemma pathHazard_nonneg (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (es : List E) : 0 ≤ pathHazard N C r es := by
  unfold pathHazard
  apply List.sum_nonneg
  intro z hz
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
  exact (edgeHazard_pos N C r e).le

lemma pathHazard_pos (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) {es : List E} (hne : es ≠ []) : 0 < pathHazard N C r es := by
  cases es with
  | nil => exact False.elim (hne rfl)
  | cons e es =>
    change 0 < edgeHazard N C r e + pathHazard N C r es
    exact add_pos_of_pos_of_nonneg (edgeHazard_pos N C r e) (pathHazard_nonneg N C r es)

lemma pathHazard_zero_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (es : List E) : pathHazard N C r es = 0 ↔ es = [] := by
  constructor
  · intro hz
    by_contra hn
    exact (pathHazard_pos N C r hn).ne' hz
  · rintro rfl
    rfl

/-- Equality along one fixed route cannot hide a strictly positive additional
segment. No comparison of unrelated equal-length routes is made. -/
lemma suffix_eq_of_hazard_eq (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) {es fs all : List E}
    (he : es <:+ all) (hf : fs <:+ all)
    (h : pathHazard N C r es = pathHazard N C r fs) : es = fs := by
  rcases List.suffix_or_suffix_of_suffix he hf with hsub | hsub
  · obtain ⟨pre,hpre⟩ := hsub
    rw [← hpre,pathHazard_append] at h
    have hz : pathHazard N C r pre = 0 := by linarith
    have hp := (pathHazard_zero_iff N C r pre).mp hz
    simpa only [hp,List.nil_append] using hpre
  · obtain ⟨pre,hpre⟩ := hsub
    rw [← hpre,pathHazard_append] at h
    have hz : pathHazard N C r pre = 0 := by linarith
    have hp := (pathHazard_zero_iff N C r pre).mp hz
    simpa only [hp,List.nil_append] using hpre.symm

lemma edgePath_source_unique (N : RootedBinary V E X) {a b c : V} {es : List E}
    (p : EdgePath N.graph a c es) (q : EdgePath N.graph b c es) : a = b := by
  cases p with
  | nil => cases q; rfl
  | cons hs rest => cases q with
    | cons ht tail => exact hs.symm.trans ht


def PathFork.swap (N : RootedBinary V E X) {a b c : V} {es fs : List E}
    (F : PathFork N a b c es fs) : PathFork N a c b fs es where
  vertex := F.vertex
  stem := F.stem
  left := F.right
  right := F.left
  left_eq := F.right_eq
  right_eq := F.left_eq
  stem_path := F.stem_path
  left_path := F.right_path
  right_path := F.left_path
  separate := by
    intro e he f hf h
    exact F.separate f hf e he h.symm

lemma PathFork.left_difference (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b c : V} {es fs : List E} (F : PathFork N a b c es fs) (e : E) :
    (e ∈ es ∧ e ∉ fs) ↔ e ∈ F.left := by
  have hn : (F.stem ++ F.left).Nodup := edgePath_nodup N C
    (F.stem_path.append F.left_path)
  have hd := (List.nodup_append.mp hn).2.2
  simp only [F.left_eq,F.right_eq,List.mem_append]
  constructor
  · rintro ⟨he,hf⟩
    exact he.resolve_left (fun hh => hf (Or.inl hh))
  · intro he
    refine ⟨Or.inr he,?_⟩
    rintro (hh | hh)
    · exact hd e hh e he rfl
    · exact F.separate e he e hh rfl

lemma PathFork.difference_hazard (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) {a b c : V} {es fs : List E}
    (F : PathFork N a b c es fs) :
    (∑ e : E, if e ∈ es ∧ e ∉ fs then edgeHazard N C r e else 0) =
      pathHazard N C r F.left := by
  simp_rw [F.left_difference N C]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun e => e ∈ F.left) = F.left.toFinset := by
    ext e
    simp
  rw [hf]
  exact List.sum_toFinset (edgeHazard N C r) (edgePath_nodup N C F.left_path)

noncomputable def bankFork (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool) (i j : X) :
    PathFork N N.root (N.leaf i) (N.leaf j)
      ((commonRoutes N C H coin).edges i) ((commonRoutes N C H coin).edges j) := by
  let P := coinSelector N H coin
  exact Classical.choice (selected_path_fork N P
    (compiledRoute_source_spec N C P (N.leaf i)).1
    (compiledRoute_source_spec N C P (N.leaf j)).1
    (compiledRoute_source_spec N C P (N.leaf i)).2
    (compiledRoute_source_spec N C P (N.leaf j)).2)

noncomputable def bankMeeting (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool) (i j : X) : V :=
  (bankFork N C H coin i j).vertex

lemma bankFork_left_hazard (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) :
    selectedDirectedExposure N C H r coin i j =
      pathHazard N C r (bankFork N C H coin i j).left :=
  (bankFork N C H coin i j).difference_hazard N C r

lemma bankFork_right_hazard (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) :
    selectedDirectedExposure N C H r coin j i =
      pathHazard N C r (bankFork N C H coin i j).right :=
  ((bankFork N C H coin i j).swap N).difference_hazard N C r

lemma meeting_eq_of_fixed_right_route (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (a b : Hybrid N → Bool) (i j : X)
    (hr : (commonRoutes N C H a).edges j = (commonRoutes N C H b).edges j)
    (hh : selectedDirectedExposure N C H r a j i =
      selectedDirectedExposure N C H r b j i) :
    bankMeeting N C H a i j = bankMeeting N C H b i j := by
  let A := bankFork N C H a i j
  let B := bankFork N C H b i j
  have ha : A.right <:+ (commonRoutes N C H a).edges j := ⟨A.stem,A.right_eq.symm⟩
  have hb : B.right <:+ (commonRoutes N C H a).edges j :=
    ⟨B.stem,B.right_eq.symm.trans hr.symm⟩
  have hh' : pathHazard N C r A.right = pathHazard N C r B.right := by
    simpa only [bankFork_right_hazard] using hh
  have hl := suffix_eq_of_hazard_eq N C r ha hb hh'
  exact edgePath_source_unique N A.right_path (hl.symm ▸ B.right_path)

lemma PathFork.vertex_unique (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) {a b c : V} {es fs : List E}
    (F G : PathFork N a b c es fs) : F.vertex = G.vertex := by
  have hh : pathHazard N C r F.right = pathHazard N C r G.right :=
    ((F.swap N).difference_hazard N C r).symm.trans
      ((G.swap N).difference_hazard N C r)
  have he : F.right <:+ fs := ⟨F.stem,F.right_eq.symm⟩
  have hf : G.right <:+ fs := ⟨G.stem,G.right_eq.symm⟩
  have hl := suffix_eq_of_hazard_eq N C r he hf hh
  exact edgePath_source_unique N F.right_path (hl.symm ▸ G.right_path)

lemma bankMeeting_swap (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) :
    bankMeeting N C H coin i j = bankMeeting N C H coin j i :=
  ((bankFork N C H coin i j).swap N).vertex_unique N C r (bankFork N C H coin j i)

def PathFork.prepend (N : RootedBinary V E X) {a h b c : V} {pre es fs : List E}
    (hp : EdgePath N.graph a h pre) (F : PathFork N h b c es fs) :
    PathFork N a b c (pre ++ es) (pre ++ fs) where
  vertex := F.vertex
  stem := pre ++ F.stem
  left := F.left
  right := F.right
  left_eq := by simpa only [List.append_assoc] using congrArg (pre ++ ·) F.left_eq
  right_eq := by simpa only [List.append_assoc] using congrArg (pre ++ ·) F.right_eq
  stem_path := hp.append F.stem_path
  left_path := F.left_path
  right_path := F.right_path
  separate := F.separate

lemma route_avoiding_changed_site (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a b : Hybrid N → Bool) (h : Hybrid N)
    (hab : ∀ k, k ≠ h → a k = b k) (i : X)
    (havoid : ∀ e ∈ (commonRoutes N C H a).edges i, N.graph.target e ≠ h.1) :
    (commonRoutes N C H a).edges i = (commonRoutes N C H b).edges i := by
  apply List.reverse_inj.mp
  apply upPath_avoiding_agreement N (coinSelector N H a) (coinSelector N H b) h.1
    (coin_selectors_agree_except N H a b h hab)
    (EdgePath.to_upPath_reverse (compiledRoute_source_spec N C (coinSelector N H a) (N.leaf i)).1
      (fun _ _ => trivial))
    (EdgePath.to_upPath_reverse (compiledRoute_source_spec N C (coinSelector N H b) (N.leaf i)).1
      (fun _ _ => trivial))
    (respectsSelector_reverse N _ (compiledRoute_source_spec N C (coinSelector N H a) (N.leaf i)).2)
    (respectsSelector_reverse N _ (compiledRoute_source_spec N C (coinSelector N H b) (N.leaf i)).2)
  intro e he
  exact havoid e (List.mem_reverse.mp he)

/-- Original younger suffixes, including their exact edge occurrences, survive
one incoming-bit change. The older prefixes may change independently. -/
lemma route_through_changed_site (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a b : Hybrid N → Bool) (h : Hybrid N)
    (hab : ∀ k, k ≠ h → a k = b k) (i : X)
    (hvisit : ∃ e ∈ (commonRoutes N C H a).edges i, N.graph.target e = h.1) :
    ∃ preA preB post,
      (commonRoutes N C H a).edges i = preA ++ post ∧
      (commonRoutes N C H b).edges i = preB ++ post ∧
      EdgePath N.graph N.root h.1 preA ∧
      EdgePath N.graph N.root h.1 preB ∧
      EdgePath N.graph h.1 (N.leaf i) post ∧
      RespectsSelector N (coinSelector N H a) post := by
  obtain ⟨e,he,ht⟩ := hvisit
  have hpa := (compiledRoute_source_spec N C (coinSelector N H a) (N.leaf i)).1
  have hsa := (compiledRoute_source_spec N C (coinSelector N H a) (N.leaf i)).2
  have hpb := (compiledRoute_source_spec N C (coinSelector N H b) (N.leaf i)).1
  have hsb := (compiledRoute_source_spec N C (coinSelector N H b) (N.leaf i)).2
  obtain ⟨pre,post,hlist,hpre,hpost⟩ := GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge hpa he
  have hpost' : EdgePath N.graph h.1 (N.leaf i) post := by simpa only [ht] using hpost
  have hsel : RespectsSelector N (coinSelector N H a) post := by
    intro d hd
    apply hsa d
    rw [hlist]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem e hd))
  obtain ⟨tail,htail,hup⟩ := upPath_prefix_agreement_calendar N C
    (coinSelector N H a) (coinSelector N H b) h.1
    (coin_selectors_agree_except N H a b h hab)
    (EdgePath.to_upPath_reverse hpost' (fun _ _ => trivial))
    (EdgePath.to_upPath_reverse hpb (fun _ _ => trivial))
    (respectsSelector_reverse N _ hsel) (respectsSelector_reverse N _ hsb)
  refine ⟨pre ++ [e],tail.reverse,post,?_,?_,?_,UpPath.to_edgePath_reverse hup,hpost',hsel⟩
  · simpa only [commonRoutes,compiledRouteFamily,List.append_assoc,List.singleton_append] using hlist
  · simpa only [commonRoutes,compiledRouteFamily,List.reverse_reverse,List.reverse_append] using congrArg List.reverse htail
  · exact hpre.append (.cons rfl (by rw [ht]; exact .nil _))

lemma meeting_eq_when_both_visit (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (a b : Hybrid N → Bool) (h : Hybrid N) (hab : ∀ k, k ≠ h → a k = b k)
    (i j : X)
    (hi : ∃ e ∈ (commonRoutes N C H a).edges i, N.graph.target e = h.1)
    (hj : ∃ e ∈ (commonRoutes N C H a).edges j, N.graph.target e = h.1) :
    bankMeeting N C H a i j = bankMeeting N C H b i j := by
  obtain ⟨ai,bi,pi,hai,hbi,haiP,hbiP,hpi,hpiS⟩ :=
    route_through_changed_site N C H a b h hab i hi
  obtain ⟨aj,bj,pj,haj,hbj,hajP,hbjP,hpj,hpjS⟩ :=
    route_through_changed_site N C H a b h hab j hj
  have selA (x : X) (pre post : List E)
      (he : (commonRoutes N C H a).edges x = pre ++ post) :
      RespectsSelector N (coinSelector N H a) pre := by
    intro e hee
    apply (compiledRoute_source_spec N C (coinSelector N H a) (N.leaf x)).2 e
    change e ∈ (commonRoutes N C H a).edges x
    rw [he]
    exact List.mem_append.mpr (Or.inl hee)
  have selB (x : X) (pre post : List E)
      (he : (commonRoutes N C H b).edges x = pre ++ post) :
      RespectsSelector N (coinSelector N H b) pre := by
    intro e hee
    apply (compiledRoute_source_spec N C (coinSelector N H b) (N.leaf x)).2 e
    change e ∈ (commonRoutes N C H b).edges x
    rw [he]
    exact List.mem_append.mpr (Or.inl hee)
  have heA := selected_path_unique N (coinSelector N H a) haiP hajP
    (selA i ai pi hai) (selA j aj pj haj)
  have heB := selected_path_unique N (coinSelector N H b) hbiP hbjP
    (selB i bi pi hbi) (selB j bj pj hbj)
  obtain ⟨F⟩ := selected_path_fork N (coinSelector N H a) hpi hpj hpiS hpjS
  let FA : PathFork N N.root (N.leaf i) (N.leaf j)
      ((commonRoutes N C H a).edges i) ((commonRoutes N C H a).edges j) := by
    exact {
      vertex := F.vertex
      stem := ai ++ F.stem
      left := F.left
      right := F.right
      left_eq := by simpa only [List.append_assoc] using hai.trans (congrArg (ai ++ ·) F.left_eq)
      right_eq := by simpa only [heA,List.append_assoc] using haj.trans (congrArg (aj ++ ·) F.right_eq)
      stem_path := haiP.append F.stem_path
      left_path := F.left_path, right_path := F.right_path, separate := F.separate }
  let FB : PathFork N N.root (N.leaf i) (N.leaf j)
      ((commonRoutes N C H b).edges i) ((commonRoutes N C H b).edges j) := by
    exact {
      vertex := F.vertex
      stem := bi ++ F.stem
      left := F.left
      right := F.right
      left_eq := by simpa only [List.append_assoc] using hbi.trans (congrArg (bi ++ ·) F.left_eq)
      right_eq := by simpa only [heB,List.append_assoc] using hbj.trans (congrArg (bj ++ ·) F.right_eq)
      stem_path := hbiP.append F.stem_path
      left_path := F.left_path, right_path := F.right_path, separate := F.separate }
  have hA := (bankFork N C H a i j).vertex_unique N C r FA
  have hB := (bankFork N C H b i j).vertex_unique N C r FB
  exact hA.trans hB.symm

lemma one_bit_meeting_invariance (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (a b : Hybrid N → Bool) (h : Hybrid N) (hab : ∀ k, k ≠ h → a k = b k)
    (i j : X)
    (hi : selectedDirectedExposure N C H r a i j = selectedDirectedExposure N C H r b i j)
    (hj : selectedDirectedExposure N C H r a j i = selectedDirectedExposure N C H r b j i) :
    bankMeeting N C H a i j = bankMeeting N C H b i j := by
  by_cases hvi : ∃ e ∈ (commonRoutes N C H a).edges i, N.graph.target e = h.1
  · by_cases hvj : ∃ e ∈ (commonRoutes N C H a).edges j, N.graph.target e = h.1
    · exact meeting_eq_when_both_visit N C H r a b h hab i j hvi hvj
    · have hr := route_avoiding_changed_site N C H a b h hab j
        (by intro e he ht; exact hvj ⟨e,he,ht⟩)
      exact meeting_eq_of_fixed_right_route N C H r a b i j hr hj
  · have hr := route_avoiding_changed_site N C H a b h hab i
      (by intro e he ht; exact hvi ⟨e,he,ht⟩)
    calc
      bankMeeting N C H a i j = bankMeeting N C H a j i := bankMeeting_swap N C H r a i j
      _ = bankMeeting N C H b j i := meeting_eq_of_fixed_right_route N C H r a b j i hr hi
      _ = bankMeeting N C H b i j := bankMeeting_swap N C H r b j i

/-- Finite original-bank connectivity, without any new probability model. -/
lemma finite_bank_function_constant {I A : Type*} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → A)
    (hstep : ∀ a b h, (∀ k, k ≠ h → a k = b k) → f a = f b) :
    ∀ a b, f a = f b := by
  have aux : ∀ (s : Finset I) (a b : I → Bool),
      (∀ k, k ∉ s → a k = b k) → f a = f b := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a b hab
      have he : a = b := funext (fun k => hab k (by simp))
      rw [he]
    | @insert h s hs ih =>
      intro a b hab
      let c := Function.update a h (b h)
      have hac : f a = f c := hstep a c h (by
        intro k hk
        simp [c,Function.update_of_ne hk])
      have hcb : f c = f b := ih c b (by
        intro k hk
        by_cases he : k = h
        · subst k
          simp [c]
        · simp only [c,Function.update_of_ne he]
          exact hab k (by simp [hk,he]))
      exact hac.trans hcb
  intro a b
  exact aux Finset.univ a b (by intro k hk; exact False.elim (hk (Finset.mem_univ k)))

/-- Both actual directed observed calibrations force a single ORIGINAL meeting
vertex for every complete original COMMON bank. -/
theorem actual_calibrations_bank_meeting_constant (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (i j : X)
    (hi : 18 * combProbability N C H p r i j 3 =
      (3 * combProbability N C H p r i j 2)^3)
    (hj : 18 * combProbability N C H p r j i 3 =
      (3 * combProbability N C H p r j i 2)^3) :
    ∀ a b, bankMeeting N C H a i j = bankMeeting N C H b i j := by
  apply finite_bank_function_constant
  intro a b h hab
  exact one_bit_meeting_invariance N C H r a b h hab i j
    (actual_calibration_selected_path_constant N C H p r i j hi a b)
    (actual_calibration_selected_path_constant N C H p r j i hj a b)

lemma hybrid_ne_root (N : RootedBinary V E X) (h : Hybrid N) : h.1 ≠ N.root := by
  intro he
  have hz := h.property.1
  rw [he,N.root_degrees.1] at hz
  omega

/-- Every physical incoming selector is one complete original COMMON bank;
nonhybrid incoming uniqueness is derived from the original degrees. -/
lemma coin_realizes_selector (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (P : IncomingSelector N) :
    ∃ coin : Hybrid N → Bool, ∀ v : Nonroot N, (coinSelector N H coin).edge v = P.edge v := by
  have hx (h : Hybrid N) : ∃ b, (H.parents h).parent b = P.edge ⟨h.1,hybrid_ne_root N h⟩ := by
    apply GProgram.G5.ParentCalendar.incoming_edge_is_original_parent (H.parents h)
    exact (P.target _).trans (H.original_site h).symm
  let coin : Hybrid N → Bool := fun h => Classical.choose (hx h)
  refine ⟨coin,?_⟩
  intro v
  by_cases hy : N.graph.IsHybrid v.1
  · simp only [coinSelector,dif_pos hy]
    exact Classical.choose_spec (hx ⟨v.1,hy⟩)
  · simp only [coinSelector,dif_neg hy]
    exact incoming_equal_of_indegree_le_one N (nonhybrid_indegree_le_one N hy)
      ((defaultSelector N).target v) (P.target v)

lemma descendant_parent_exists (N : RootedBinary V E X) {w v : V}
    (hv : v ≠ w) (hr : N.graph.DReach w v) :
    ∃ e : E, N.graph.target e = v ∧ N.graph.DReach w (N.graph.source e) := by
  rcases Relation.ReflTransGen.cases_tail hr with he | ⟨u,hu,e,hs,ht⟩
  · exact False.elim (hv he)
  · exact ⟨e,ht,by change N.graph.DReach w u at hu; simpa only [hs] using hu⟩

/-- A graph-derived selector which keeps all descendants of w below w until
w is reached. No source or observation law is included in its definition. -/
noncomputable def descendantSelector (N : RootedBinary V E X) (w : V) : IncomingSelector N where
  edge v := if hv : v.1 ≠ w ∧ N.graph.DReach w v.1 then
    Classical.choose (descendant_parent_exists N hv.1 hv.2) else (defaultSelector N).edge v
  target v := by
    split_ifs with hv
    · exact (Classical.choose_spec (descendant_parent_exists N hv.1 hv.2)).1
    · exact (defaultSelector N).target v

lemma descendantSelector_parent (N : RootedBinary V E X) (w : V) (v : Nonroot N)
    (hv : v.1 ≠ w) (hr : N.graph.DReach w v.1) :
    N.graph.DReach w (N.graph.source ((descendantSelector N w).edge v)) := by
  simp only [descendantSelector,dif_pos (show v.1 ≠ w ∧ N.graph.DReach w v.1 from ⟨hv,hr⟩)]
  exact (Classical.choose_spec (descendant_parent_exists N hv hr)).2

lemma descendant_selected_path (N : RootedBinary V E X) (C : Calendar N.graph)
    (w : V) {v : V} (hr : N.graph.DReach w v) :
    ∃ es, EdgePath N.graph w v es ∧ RespectsSelector N (descendantSelector N w) es := by
  have aux : ∀ n : Nat, ∀ v : V, olderRank N C v = n → N.graph.DReach w v →
      ∃ es, EdgePath N.graph w v es ∧ RespectsSelector N (descendantSelector N w) es := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hreach
      by_cases hv : v = w
      · subst v
        exact ⟨[],.nil w,by intro e he; simp at he⟩
      · have hvr : v ≠ N.root := by
          intro he
          have hw : w = N.root := N.graph.dreach_antisymm N.acyclic (he ▸ hreach) (N.rooted w)
          exact hv (he.trans hw.symm)
        let P := descendantSelector N w
        let e := P.edge ⟨v,hvr⟩
        have ht : N.graph.target e = v := P.target ⟨v,hvr⟩
        have hrs : N.graph.DReach w (N.graph.source e) := descendantSelector_parent N w ⟨v,hvr⟩ hv hreach
        have hlt : olderRank N C (N.graph.source e) < n := by
          simpa only [ht,hn] using olderRank_edge_decreases N C e
        obtain ⟨pre,hpre,hsel⟩ := ih _ hlt _ rfl hrs
        refine ⟨pre ++ [e],hpre.append (.cons rfl (by rw [ht]; exact .nil v)),?_⟩
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hsel f hf
        · exact selector_edge_respects N P ⟨v,hvr⟩ f hf
  exact aux (olderRank N C v) v rfl hr

lemma respects_append (N : RootedBinary V E X) (P : IncomingSelector N)
    {es fs : List E} (he : RespectsSelector N P es) (hf : RespectsSelector N P fs) :
    RespectsSelector N P (es ++ fs) := by
  intro e h
  exact (List.mem_append.mp h).elim (he e) (hf e)

/-- A common original ancestor is above a selected meeting for one jointly
realized bank. This is stronger than unrelated one-path realizations. -/
lemma common_ancestor_selected_meeting (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (i j : X) (w : V)
    (hi : N.graph.DReach w (N.leaf i)) (hj : N.graph.DReach w (N.leaf j)) :
    ∃ coin, N.graph.DReach w (bankMeeting N C H coin i j) := by
  let P := descendantSelector N w
  obtain ⟨es,he,hse⟩ := descendant_selected_path N C w hi
  obtain ⟨fs,hf,hsf⟩ := descendant_selected_path N C w hj
  obtain ⟨F⟩ := selected_path_fork N P he hf hse hsf
  let pre := compiledRoute N C P w
  have hpre := (compiledRoute_source_spec N C P w).1
  have hspre := (compiledRoute_source_spec N C P w).2
  obtain ⟨coin,hcoin⟩ := coin_realizes_selector N H P
  have hs (xs : List E) (hx : RespectsSelector N P xs) :
      RespectsSelector N (coinSelector N H coin) xs := by
    intro e hee
    obtain ⟨hr,hh⟩ := hx e hee
    exact ⟨hr,(hcoin _).trans hh⟩
  have hei : (commonRoutes N C H coin).edges i = pre ++ es :=
    selected_path_unique N (coinSelector N H coin)
      (compiledRoute_source_spec N C (coinSelector N H coin) (N.leaf i)).1
      (hpre.append he)
      (compiledRoute_source_spec N C (coinSelector N H coin) (N.leaf i)).2
      (hs _ (respects_append N P hspre hse))
  have hej : (commonRoutes N C H coin).edges j = pre ++ fs :=
    selected_path_unique N (coinSelector N H coin)
      (compiledRoute_source_spec N C (coinSelector N H coin) (N.leaf j)).1
      (hpre.append hf)
      (compiledRoute_source_spec N C (coinSelector N H coin) (N.leaf j)).2
      (hs _ (respects_append N P hspre hsf))
  let G : PathFork N N.root (N.leaf i) (N.leaf j)
      ((commonRoutes N C H coin).edges i) ((commonRoutes N C H coin).edges j) :=
    { vertex := F.vertex, stem := pre ++ F.stem, left := F.left, right := F.right,
      left_eq := by simpa only [List.append_assoc] using hei.trans (congrArg (pre ++ ·) F.left_eq)
      right_eq := by simpa only [List.append_assoc] using hej.trans (congrArg (pre ++ ·) F.right_eq)
      stem_path := hpre.append F.stem_path
      left_path := F.left_path, right_path := F.right_path, separate := F.separate }
  have hm := (bankFork N C H coin i j).vertex_unique N C r G
  refine ⟨coin,?_⟩
  change N.graph.DReach w (bankFork N C H coin i j).vertex
  rw [hm]
  change N.graph.DReach w F.vertex
  exact F.stem_path.directed

lemma calibrated_common_ancestor_above (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (i j : X)
    (coin : Hybrid N → Bool)
    (hc : ∀ a b, bankMeeting N C H a i j = bankMeeting N C H b i j)
    (w : V) (hi : N.graph.DReach w (N.leaf i)) (hj : N.graph.DReach w (N.leaf j)) :
    N.graph.DReach w (bankMeeting N C H coin i j) := by
  obtain ⟨a,ha⟩ := common_ancestor_selected_meeting N C H r i j w hi hj
  rwa [hc a coin] at ha

lemma leaf_no_outgoing (N : RootedBinary V E X) (i : X) (e : E) :
    N.graph.source e ≠ N.leaf i := by
  intro he
  have hz := (N.leaf_degrees i).2
  rw [EdgeGraph.outDegree,Finset.card_eq_zero] at hz
  have hm : e ∈ Finset.univ.filter (fun f : E => N.graph.source f = N.leaf i) := by simp [he]
  rw [hz] at hm
  exact Finset.notMem_empty e hm

lemma leaf_dreach_eq (N : RootedBinary V E X) (i : X) {v : V}
    (hr : N.graph.DReach (N.leaf i) v) : N.leaf i = v := by
  rcases Relation.ReflTransGen.cases_head hr with he | ⟨w,⟨e,hs,ht⟩,hrest⟩
  · exact he
  · exact False.elim (leaf_no_outgoing N i e hs)

lemma bankMeeting_ne_left_leaf (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool) {i j : X} (hij : i ≠ j) :
    bankMeeting N C H coin i j ≠ N.leaf i := by
  intro he
  have hp := (bankFork N C H coin i j).right_path.directed
  change N.graph.DReach (bankMeeting N C H coin i j) (N.leaf j) at hp
  rw [he] at hp
  exact hij (N.leaf.injective (leaf_dreach_eq N i hp))

lemma original_outdegree_le_two (N : RootedBinary V E X) (v : V) :
    N.graph.outDegree v ≤ 2 := by
  by_cases hv : v = N.root
  · simpa only [hv,N.root_degrees.2] using (le_refl (2 : Nat))
  by_cases hl : ∃ x, N.leaf x = v
  · obtain ⟨x,hx⟩ := hl
    rw [← hx,(N.leaf_degrees x).2]
    omega
  rcases N.internal_degrees v hv (by intro x hx; exact hl ⟨x,hx⟩) with ht | hh
  · exact ht.2.le
  · rw [hh.2]
    omega

noncomputable def meetingChildSet (N : RootedBinary V E X) (v : V) (i : X) : Finset E :=
  Finset.univ.filter (fun e => N.graph.source e = v ∧ N.graph.DReach (N.graph.target e) (N.leaf i))

lemma calibrated_child_sets_disjoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (i j : X)
    (coin : Hybrid N → Bool)
    (hc : ∀ a b, bankMeeting N C H a i j = bankMeeting N C H b i j) :
    Disjoint (meetingChildSet N (bankMeeting N C H coin i j) i)
      (meetingChildSet N (bankMeeting N C H coin i j) j) := by
  apply Finset.disjoint_left.mpr
  intro e hi hj
  simp only [meetingChildSet,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
  have ha := calibrated_common_ancestor_above N C H r i j coin hc (N.graph.target e) hi.2 hj.2
  have hb : N.graph.DReach (N.graph.target e) (N.graph.source e) := by simpa only [hi.1] using ha
  exact N.acyclic (N.graph.target e) (Relation.TransGen.tail' hb ⟨e,rfl,rfl⟩)

lemma original_path_has_meeting_child (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (i j : X) (hij : i ≠ j)
    (coin : Hybrid N → Bool)
    (hc : ∀ a b, bankMeeting N C H a i j = bankMeeting N C H b i j)
    {es : List E} (p : EdgePath N.graph N.root (N.leaf i) es) :
    ∃ e ∈ es, e ∈ meetingChildSet N (bankMeeting N C H coin i j) i := by
  obtain ⟨a,ha⟩ := compiledRoute_covers_original_path N C H p
  let F := bankFork N C H a i j
  have hF : F.vertex = bankMeeting N C H coin i j := hc a coin
  have hlist : es = F.stem ++ F.left := by
    rw [← ha]
    exact F.left_eq
  have hnil : ∀ {a b : V}, EdgePath N.graph a b [] → a = b := by
    intro a b hp
    cases hp
    rfl
  have hcons : ∀ {a b : V} {e : E} {xs : List E}, EdgePath N.graph a b (e :: xs) →
      N.graph.source e = a ∧ EdgePath N.graph (N.graph.target e) b xs := by
    intro a b e xs hp
    cases hp with
    | cons hs rest => exact ⟨hs,rest⟩
  have hn : F.left ≠ [] := by
    intro he
    have hp := F.left_path
    have hv : F.vertex = N.leaf i := hnil (by simpa only [he] using hp)
    exact bankMeeting_ne_left_leaf N C H a hij hv
  cases hl : F.left with
  | nil => exact False.elim (hn hl)
  | cons e tail =>
    obtain ⟨hs,htail⟩ := hcons (show EdgePath N.graph F.vertex (N.leaf i) (e :: tail) by
      simpa only [hl] using F.left_path)
    refine ⟨e,?_,?_⟩
    · rw [hlist,hl]
      simp
    · simp only [meetingChildSet,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hs.trans hF,htail.directed⟩

/-- The exact already-checked geometric input is constructed from the actual
observed calibrations. Its all-path fields are not assumed. -/
theorem actual_calibrations_route_meeting_geometry (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (i j : X) (hij : i ≠ j)
    (hi : 18 * combProbability N C H p r i j 3 =
      (3 * combProbability N C H p r i j 2)^3)
    (hj : 18 * combProbability N C H p r j i 3 =
      (3 * combProbability N C H p r j i 2)^3) :
    ∃ v ei ej, G4LiteralLastChildExitCutDraft.RouteMeetingGeometry N i j v ei ej := by
  let coin : Hybrid N → Bool := fun _ => false
  let v := bankMeeting N C H coin i j
  have hc := actual_calibrations_bank_meeting_constant N C H p r i j hi hj
  have hc' := actual_calibrations_bank_meeting_constant N C H p r j i hj hi
  have hv : bankMeeting N C H coin j i = v := bankMeeting_swap N C H r coin j i
  obtain ⟨pi,hpi⟩ := original_tip_route_exists N i
  obtain ⟨pj,hpj⟩ := original_tip_route_exists N j
  obtain ⟨ei,hei,hiSet⟩ := original_path_has_meeting_child N C H i j hij coin hc hpi
  obtain ⟨ej,hej,hjSet⟩ := original_path_has_meeting_child N C H j i hij.symm coin hc' hpj
  rw [hv] at hjSet
  have hd := calibrated_child_sets_disjoint N C H r i j coin hc
  have hne : ei ≠ ej := by
    intro he
    exact Finset.disjoint_left.mp hd hiSet (by simpa only [he] using hjSet)
  have his := (Finset.mem_filter.mp hiSet).2.1
  have hjs := (Finset.mem_filter.mp hjSet).2.1
  let outs := Finset.univ.filter (fun e : E => N.graph.source e = v)
  have hsub : {ei,ej} ⊆ outs := by
    intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · simp [outs,his,v]
    · simp [outs,hjs]
  have hcard : outs.card ≤ ({ei,ej} : Finset E).card := by
    have ho := original_outdegree_le_two N v
    change outs.card ≤ 2 at ho
    simpa [hne] using ho
  have houts : outs = {ei,ej} := (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hI (e : E) (he : e ∈ meetingChildSet N v i) : e = ei := by
    have hs := (Finset.mem_filter.mp he).2.1
    have hm : e ∈ outs := by simp [outs,hs]
    rw [houts] at hm
    rcases Finset.mem_insert.mp hm with hh | hh
    · exact hh
    · have hh' : e = ej := Finset.mem_singleton.mp hh
      exact False.elim (Finset.disjoint_left.mp hd he (by simpa only [hh'] using hjSet))
  have hJ (e : E) (he : e ∈ meetingChildSet N v j) : e = ej := by
    have hs := (Finset.mem_filter.mp he).2.1
    have hm : e ∈ outs := by simp [outs,hs]
    rw [houts] at hm
    rcases Finset.mem_insert.mp hm with hh | hh
    · exact False.elim (Finset.disjoint_left.mp hd (by simpa only [hh] using hiSet) he)
    · exact Finset.mem_singleton.mp hh
  refine ⟨v,ei,ej,⟨hij,hne,his,hjs,?_,?_,?_⟩⟩
  · intro es hp
    obtain ⟨e,he,hs⟩ := original_path_has_meeting_child N C H i j hij coin hc hp
    rwa [hI e hs] at he
  · intro es hp
    obtain ⟨e,he,hs⟩ := original_path_has_meeting_child N C H j i hij.symm coin hc' hp
    rw [hv] at hs
    rwa [hJ e hs] at he
  · exact calibrated_common_ancestor_above N C H r i j coin hc


section Permutations
open GProgram.SourceForest GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourcePoissonKernel G1NonrootBigonKernel
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- Every current root above the meeting carries a population ancestral to
EVERY selected original taxon. This permits label permutations after splitting. -/
def CommonDescendants (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) : Prop :=
  ∀ x y, DescendsTo N (copyLocation s x) (sample y)

lemma commonDescendants_of_colocated (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (h : ∀ x y, copyLocation (state s) x = copyLocation (state s) y) :
    CommonDescendants N sample (state s) := by
  intro x y
  rw [h x y]
  exact s.property.original_descendant y

lemma commonDescendants_destination (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (q : Option (Choice N s)) : CommonDescendants N sample (state (stepDestination N s q)) := by
  intro x y
  rw [actual_step_copy_population]
  exact hs x y

lemma commonDescendants_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : CommonDescendants N sample (state d) := by
  intro x y
  rw [actual_time_copy_population N r t s hd x]
  exact hs x y

lemma commonDescendants_exit (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : CommonDescendants N sample (state s)) (e : E) :
    CommonDescendants N sample (state (exitCode N s e)) := by
  intro x y
  rw [exitCode_copyLocation,exitLocation]
  by_cases hx : copyLocation (state s) x = .edge e
  · rw [if_pos hx]
    have h := hs x y
    rw [hx] at h
    exact (Relation.ReflTransGen.single ⟨e,rfl,rfl⟩).trans h
  · rw [if_neg hx]
    exact hs x y

lemma commonDescendants_ordinary (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : CommonDescendants N sample (state s)) (e : E) :
    CommonDescendants N sample (state (ordinaryCode N s e)) := by
  intro x y
  rw [ordinaryCode_copyLocation,ordinaryLocation]
  by_cases hx : copyLocation (state s) x = .node (N.graph.target e)
  · rw [if_pos hx]
    have h := hs x y
    simpa only [hx,DescendsTo] using h
  · rw [if_neg hx]
    exact hs x y

lemma commonDescendants_root (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    CommonDescendants N sample (state (rootCode N s)) := by
  intro x y
  rw [rootCode_copyLocation,rootLocation]
  by_cases hx : copyLocation (state s) x = .node N.root
  · rw [if_pos hx]
    exact ⟨rfl,N.rooted _⟩
  · rw [if_neg hx]
    exact hs x y

lemma commonDescendants_pulse (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) (coin : AtNode (state s) H.hybrid → Bool) :
    CommonDescendants N sample (state (pulseCode H s coin)) := by
  intro x y
  have hm := actual_pulse_code_location H s coin x
  by_cases hx : copyLocation (state s) x = .node H.hybrid
  · obtain ⟨b,hb⟩ := hm.1 hx
    rw [hb]
    change N.graph.DReach (N.graph.target (H.parent b)) (N.leaf (sample y))
    rw [original_parent_targets_hybrid]
    have h := hs x y
    simpa only [hx,DescendsTo] using h
  · rw [hm.2 hx]
    exact hs x y

lemma commonDescendants_boundary (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N op s).support) : CommonDescendants N sample (state d) := by
  cases op with
  | exit e =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
    exact commonDescendants_exit N s hs e
  | ordinary e h =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
    exact commonDescendants_ordinary N s hs e
  | root =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
    exact commonDescendants_root N s hs
  | common H =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
    exact commonDescendants_pulse N H s hs _
  | independent H gamma =>
    obtain ⟨coin,hcoin,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
    exact commonDescendants_pulse N H s hs coin

lemma commonDescendants_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) : CommonDescendants N sample (state d) := by
  induction ops generalizing s d with
  | nil =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
    exact hs
  | cons op ops ih =>
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply ih z ?_ hdz
    cases op with
    | interval t => exact commonDescendants_time N r t s hs hz
    | boundary b => exact commonDescendants_boundary N b s hs hz

lemma mapLabels_compose {A B D : Type*} (f : A → B) (g : B → D) (t : Genealogy A) :
    mapLabels g (mapLabels f t) = mapLabels (g ∘ f) t := by
  induction t with
  | leaf x => rfl
  | graft a b iha ihb => simp only [mapLabels,iha,ihb]

lemma mapLabels_identity {A : Type*} (t : Genealogy A) : mapLabels id t = t := by
  induction t with
  | leaf x => rfl
  | graft a b iha ihb => simp only [mapLabels,iha,ihb]

lemma mapLabels_inverse (σ : Equiv.Perm Copy) (t : Genealogy Copy) :
    mapLabels σ.symm (mapLabels σ t) = t := by
  rw [mapLabels_compose]
  have h : (σ.symm ∘ σ : Copy → Copy) = id := funext (fun x => σ.symm_apply_apply x)
  rw [h,mapLabels_identity]

noncomputable def permuteTree (σ : Equiv.Perm Copy) (t : WellLabelledTree Copy) :
    WellLabelledTree Copy := ⟨mapLabels σ t.val,mapLabels_wellLabelled σ σ.injective t.val t.property⟩

lemma permuteTree_inverse (σ : Equiv.Perm Copy) (t : WellLabelledTree Copy) :
    permuteTree σ.symm (permuteTree σ t) = t := by
  apply Subtype.ext
  exact mapLabels_inverse σ t.val

/-- This acts on the actual finite snapshot, preserving dead-coordinate data
and the original register, so inverse transport is literal rather than a new
choice of current-root representatives. -/
noncomputable def permuteSnapshot (σ : Equiv.Perm Copy) (s : Snapshot V E Copy) :
    Snapshot V E Copy where
  live := s.live.image σ
  ancestor x := σ (s.ancestor (σ.symm x))
  genealogy x := (s.genealogy (σ.symm x)).map (permuteTree σ)
  population x := s.population (σ.symm x)
  register := s.register

lemma permuteSnapshot_inverse (σ : Equiv.Perm Copy) (s : Snapshot V E Copy) :
    permuteSnapshot σ.symm (permuteSnapshot σ s) = s := by
  apply Snapshot.ext
  · ext x
    simp [permuteSnapshot,Finset.mem_image]
  · funext x
    simp [permuteSnapshot]
  · funext x
    simp only [permuteSnapshot,Equiv.apply_symm_apply,Option.map_map]
    cases s.genealogy x with
    | none => rfl
    | some t => simpa only [Option.map_some,Function.comp_apply] using
        congrArg some (permuteTree_inverse σ t)
  · funext x
    simp [permuteSnapshot]
  · rfl

lemma permuteSnapshot_live (root : V) (σ : Equiv.Perm Copy) (s : Snapshot V E Copy) :
    (decodeSnapshot root (permuteSnapshot σ s)).live = (decodeSnapshot root s).live.image σ := rfl

lemma permuteSnapshot_ancestor (root : V) (σ : Equiv.Perm Copy) (s : Snapshot V E Copy) (x : Copy) :
    (decodeSnapshot root (permuteSnapshot σ s)).ancestor x =
      σ ((decodeSnapshot root s).ancestor (σ.symm x)) := rfl

lemma permuteSnapshot_genealogy (root : V) (σ : Equiv.Perm Copy) (s : Snapshot V E Copy) (x : Copy) :
    (decodeSnapshot root (permuteSnapshot σ s)).genealogy x =
      mapLabels σ ((decodeSnapshot root s).genealogy (σ.symm x)) := by
  cases h : s.genealogy (σ.symm x) with
  | none => simp [decodeSnapshot,permuteSnapshot,h,mapLabels]
  | some t => simp [decodeSnapshot,permuteSnapshot,h,permuteTree]

lemma permuteSnapshot_location (root : V) (σ : Equiv.Perm Copy) (s : Snapshot V E Copy) (x : Copy) :
    (decodeSnapshot root (permuteSnapshot σ s)).location x =
      (decodeSnapshot root s).location (σ.symm x) := rfl

lemma permuteSnapshot_copyLocation (root : V) (σ : Equiv.Perm Copy) (s : Snapshot V E Copy) (x : Copy) :
    copyLocation (decodeSnapshot root (permuteSnapshot σ s)) x =
      copyLocation (decodeSnapshot root s) (σ.symm x) := by
  simp only [copyLocation,permuteSnapshot_ancestor,permuteSnapshot_location,Equiv.symm_apply_apply]

lemma permuteSnapshot_valid (root : V) (σ : Equiv.Perm Copy) (s : Snapshot V E Copy)
    (hs : Valid (decodeSnapshot root s)) : Valid (decodeSnapshot root (permuteSnapshot σ s)) := by
  constructor
  · intro x
    exact Finset.mem_image.mpr ⟨_,hs.ancestor_live (σ.symm x),rfl⟩
  · intro l hl
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    simp only [permuteSnapshot_ancestor,Equiv.symm_apply_apply,hs.representative k hk]
  · intro l hl x
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    rw [permuteSnapshot_genealogy,mapLabels_leaves]
    simp only [Equiv.symm_apply_apply,permuteSnapshot_ancestor]
    constructor
    · intro hx
      obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
      have ha := (hs.leaf_fiber k hk y).mp hy
      subst x
      simpa only [Equiv.symm_apply_apply] using congrArg σ ha
    · intro hx
      have ha : (decodeSnapshot root s).ancestor (σ.symm x) = k := σ.injective hx
      exact Finset.mem_image.mpr ⟨σ.symm x,(hs.leaf_fiber k hk _).mpr ha,σ.apply_symm_apply x⟩
  · intro l hl
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    rw [permuteSnapshot_genealogy,Equiv.symm_apply_apply]
    exact mapLabels_wellLabelled σ σ.injective _ (hs.wellLabelled k hk)

lemma permuteSnapshot_commonDescendants (N : RootedBinary V E X) (sample : Copy → X)
    (σ : Equiv.Perm Copy) (s : Snapshot V E Copy)
    (hs : CommonDescendants N sample (decodeSnapshot N.root s)) :
    CommonDescendants N sample (decodeSnapshot N.root (permuteSnapshot σ s)) := by
  intro x y
  rw [permuteSnapshot_copyLocation]
  exact hs (σ.symm x) y

noncomputable def permuteCode (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) : Code N sample :=
  if hs : CommonDescendants N sample (state s) then
    ⟨permuteSnapshot σ s.val,⟨permuteSnapshot_valid N.root σ s.val (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest),
      fun x => (permuteSnapshot_commonDescendants N sample σ s.val hs) x x⟩⟩
  else s

lemma permuteCode_val (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    (permuteCode N σ s).val = permuteSnapshot σ s.val := by
  simp only [permuteCode,dif_pos hs]

lemma permuteCode_commonDescendants (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    CommonDescendants N sample (state (permuteCode N σ s)) := by
  change CommonDescendants N sample (decodeSnapshot N.root (permuteCode N σ s).val)
  rw [permuteCode_val N σ s hs]
  exact permuteSnapshot_commonDescendants N sample σ s.val hs

lemma permuteCode_inverse (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) : permuteCode N σ.symm (permuteCode N σ s) = s := by
  by_cases hs : CommonDescendants N sample (state s)
  · apply Subtype.ext
    rw [permuteCode_val N σ.symm _ (permuteCode_commonDescendants N σ s hs),
      permuteCode_val N σ s hs,permuteSnapshot_inverse]
  · simp only [permuteCode,dif_neg hs]

noncomputable def permuteCodeEquiv (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) : Code N sample ≃ Code N sample where
  toFun := permuteCode N σ
  invFun := permuteCode N σ.symm
  left_inv := permuteCode_inverse N σ
  right_inv s := by simpa only [Equiv.symm_symm] using permuteCode_inverse (sample := sample) N σ.symm s

lemma permuteCode_live (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    (state (permuteCode N σ s)).live = (state s).live.image σ := by
  change (decodeSnapshot N.root (permuteCode N σ s).val).live = _
  rw [permuteCode_val N σ s hs]
  rfl

lemma permuteCode_location (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (x : Copy) : (state (permuteCode N σ s)).location x = (state s).location (σ.symm x) := by
  change (decodeSnapshot N.root (permuteCode N σ s).val).location x = _
  rw [permuteCode_val N σ s hs]
  rfl

lemma permuteCode_population_member (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (place : Location V E) (x : Copy) :
    σ x ∈ populationRoots (state (permuteCode N σ s)) place ↔
      x ∈ populationRoots (state s) place := by
  simp only [populationRoots,Finset.mem_filter,permuteCode_live N σ s hs,
    permuteCode_location N σ s hs,Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hx,hplace⟩
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    have hxy : y = x := σ.injective he
    exact ⟨hxy ▸ hy,hplace⟩
  · rintro ⟨hx,hplace⟩
    exact ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,hplace⟩

lemma permuteCode_population_pair (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (place : Location V E) (a b : Copy) :
    (σ a,σ b) ∈ (populationRoots (state (permuteCode N σ s)) place).offDiag ↔
      (a,b) ∈ (populationRoots (state s) place).offDiag := by
  simp only [Finset.mem_offDiag,permuteCode_population_member N σ s hs,σ.injective.ne_iff]

/-- Same population and both ordered orientations; no reweighting of an
unordered quotient is hidden in this actual source-choice equivalence. -/
noncomputable def permuteChoiceEquiv (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    Choice N s ≃ Choice N (permuteCode N σ s) where
  toFun p := ⟨p.1,⟨(σ p.2.val.1,σ p.2.val.2),
    (permuteCode_population_pair N σ s hs _ _ _).mpr p.2.property⟩⟩
  invFun p := ⟨p.1,⟨(σ.symm p.2.val.1,σ.symm p.2.val.2),by
    apply (permuteCode_population_pair N σ s hs _ _ _).mp
    simpa only [Equiv.apply_symm_apply] using p.2.property⟩⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

lemma permuteChoice_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) (p : Choice N s) :
    choiceRate N r (permuteCode N σ s) (permuteChoiceEquiv N σ s hs p) =
      choiceRate N r s p := rfl

lemma permuteCode_totalRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    totalRate N r (permuteCode N σ s) = totalRate N r s := by
  unfold totalRate
  exact (Fintype.sum_equiv (permuteChoiceEquiv N σ s hs) _ _
    (fun p => (permuteChoice_rate N r σ s hs p).symm)).symm

lemma permuteChoice_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) (p : Option (Choice N s)) :
    choiceMass N r (permuteCode N σ s) (p.map (permuteChoiceEquiv N σ s hs)) =
      choiceMass N r s p := by
  cases p with
  | none => simp only [Option.map_none,choiceMass,permuteCode_totalRate N r σ s hs]
  | some p => rfl

lemma map_equiv_mass {A B : Type*} [Fintype A] (p : PMF A) (e : A ≃ B) (b : B) :
    (p.map e) b = p (e.symm b) := by
  classical
  rw [PMF.map_apply,tsum_fintype,Finset.sum_eq_single (e.symm b)]
  · simp only [e.apply_symm_apply,ite_true]
  · intro a ha hne
    have h : b ≠ e a := by
      intro he
      apply hne
      simpa only [e.symm_apply_apply] using (congrArg e.symm he).symm
    simp only [if_neg h]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

lemma permuteChoice_pmf (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    (choicePMF N r s).map (Equiv.optionCongr (permuteChoiceEquiv N σ s hs)) =
      choicePMF N r (permuteCode N σ s) := by
  apply PMF.ext
  intro b
  rw [map_equiv_mass]
  let e := Equiv.optionCongr (permuteChoiceEquiv N σ s hs)
  have hm := permuteChoice_mass N r σ s hs (e.symm b)
  have he : (e.symm b).map (permuteChoiceEquiv N σ s hs) = b := e.apply_symm_apply b
  rw [he] at hm
  simpa only [choicePMF,PMF.ofFintype_apply] using congrArg ENNReal.ofReal hm.symm

lemma permuteCode_ancestor (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (x : Copy) : (state (permuteCode N σ s)).ancestor x = σ ((state s).ancestor (σ.symm x)) := by
  change (decodeSnapshot N.root (permuteCode N σ s).val).ancestor x = _
  rw [permuteCode_val N σ s hs]
  rfl

lemma permuteCode_genealogy (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (x : Copy) : (state (permuteCode N σ s)).genealogy x = mapLabels σ ((state s).genealogy (σ.symm x)) := by
  change (decodeSnapshot N.root (permuteCode N σ s).val).genealogy x = _
  rw [permuteCode_val N σ s hs,permuteSnapshot_genealogy]
  rfl

lemma permuteCode_register (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    (state (permuteCode N σ s)).register = (state s).register := by
  change (decodeSnapshot N.root (permuteCode N σ s).val).register = _
  rw [permuteCode_val N σ s hs]
  rfl

lemma actual_choice_merge_valid (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (q : Choice N s) :
    Valid (merge (state s) q.2.val.1 q.2.val.2) :=
  (merge_source_valid N sample (state s) s.property
    (population_pair_is_source_legal (state s) (originalPlace N q.1)
      (originalPlace_not_node N q.1) q.2.property)).forest

lemma permuteCode_destination (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (q : Option (Choice N s)) :
    permuteCode N σ (stepDestination N s q) =
      stepDestination N (permuteCode N σ s) (q.map (permuteChoiceEquiv N σ s hs)) := by
  cases q with
  | none => rfl
  | some q =>
    apply Subtype.ext
    rw [permuteCode_val N σ _ (commonDescendants_destination N s hs (some q))]
    change permuteSnapshot σ (encodeSnapshot (merge (state s) q.2.val.1 q.2.val.2) (actual_choice_merge_valid N s q)) =
      encodeSnapshot (merge (state (permuteCode N σ s)) (σ q.2.val.1) (σ q.2.val.2))
        (actual_choice_merge_valid N (permuteCode N σ s) (permuteChoiceEquiv N σ s hs q))
    apply Snapshot.ext
    · simp only [permuteSnapshot,encodeSnapshot,merge,permuteCode_live N σ s hs]
      exact Finset.image_erase σ.injective _ _
    · funext x
      obtain ⟨y,rfl⟩ := σ.surjective x
      simp only [permuteSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
        permuteCode_ancestor N σ s hs,σ.injective.eq_iff]
      split <;> rfl
    · funext x
      obtain ⟨y,rfl⟩ := σ.surjective x
      have hl : σ y ∈ (state (permuteCode N σ s)).live ↔ y ∈ (state s).live := by
        rw [permuteCode_live N σ s hs]
        simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
      by_cases hy : y ∈ (state s).live.erase q.2.val.2
      · have hy' : σ y ∈ (state (permuteCode N σ s)).live.erase (σ q.2.val.2) := by
          simpa only [Finset.mem_erase,σ.injective.ne_iff,hl] using hy
        simp only [permuteSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
          dif_pos hy,dif_pos hy',Option.map_some]
        apply congrArg some
        apply Subtype.ext
        by_cases ha : y = q.2.val.1
        · subst y
          simp only [permuteTree,if_pos rfl,permuteCode_genealogy N σ s hs,
            Equiv.symm_apply_apply,mapLabels,ite_true]
        · simp only [permuteTree,if_neg ha,if_neg (σ.injective.ne_iff.mpr ha),
            permuteCode_genealogy N σ s hs,Equiv.symm_apply_apply]
      · have hy' : σ y ∉ (state (permuteCode N σ s)).live.erase (σ q.2.val.2) := by
          simpa only [Finset.mem_erase,σ.injective.ne_iff,hl] using hy
        simp only [permuteSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
          dif_neg hy,dif_neg hy',Option.map_none]
    · funext x
      obtain ⟨y,rfl⟩ := σ.surjective x
      have hl : σ y ∈ (state (permuteCode N σ s)).live ↔ y ∈ (state s).live := by
        rw [permuteCode_live N σ s hs]
        simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
      simp only [permuteSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
        Finset.mem_erase,σ.injective.ne_iff,hl,permuteCode_location N σ s hs]
    · exact (permuteCode_register N σ s hs).symm

lemma permuteCode_sourceStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    (sourceStep N r s).map (permuteCode N σ) = sourceStep N r (permuteCode N σ s) := by
  unfold sourceStep
  rw [← permuteChoice_pmf N r σ s hs,PMF.map_comp,PMF.map_comp]
  congr 1
  funext q
  exact permuteCode_destination N σ s hs q

lemma permuteCode_iteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (k : Nat) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    (sourceIteration N r k s).map (permuteCode N σ) =
      sourceIteration N r k (permuteCode N σ s) := by
  induction k generalizing s with
  | zero => simp only [sourceIteration,PMF.pure_map]
  | succ k ih =>
    rw [sourceIteration,PMF.map_bind,sourceIteration,← permuteCode_sourceStep N r σ s hs,
      PMF.bind_map]
    apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
    intro d hd
    obtain ⟨q,hq,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
    exact ih _ (commonDescendants_destination N s hs q)

lemma permuteCode_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (t : ℝ≥0) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    (sourceTimeKernel N r t s).map (permuteCode N σ) =
      sourceTimeKernel N r t (permuteCode N σ s) := by
  rw [sourceTimeKernel,PMF.map_bind,sourceTimeKernel]
  congr 1
  funext k
  exact permuteCode_iteration N r σ k s hs

lemma permuteCode_transport (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (f g : Copy → Location V E) (ev ev' : SourceEvent V E Copy)
    (hv : SourceValid N sample (transport (state s) f ev))
    (hv' : SourceValid N sample (transport (state (permuteCode N σ s)) g ev'))
    (hd : CommonDescendants N sample (state (admittedCode N sample (transport (state s) f ev) hv)))
    (hfg : ∀ x, g (σ x) = f x) :
    permuteCode N σ (admittedCode N sample (transport (state s) f ev) hv) =
      admittedCode N sample (transport (state (permuteCode N σ s)) g ev') hv' := by
  apply Subtype.ext
  rw [permuteCode_val N σ _ hd]
  change permuteSnapshot σ (encodeSnapshot (transport (state s) f ev) hv.forest) =
    encodeSnapshot (transport (state (permuteCode N σ s)) g ev') hv'.forest
  apply Snapshot.ext
  · exact (permuteCode_live N σ s hs).symm
  · funext x
    exact (permuteCode_ancestor N σ s hs x).symm
  · funext x
    obtain ⟨y,rfl⟩ := σ.surjective x
    have hl : σ y ∈ (state (permuteCode N σ s)).live ↔ y ∈ (state s).live := by
      rw [permuteCode_live N σ s hs]
      simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
    by_cases hy : y ∈ (state s).live
    · have hy' := hl.mpr hy
      simp only [permuteSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,
        dif_pos hy,dif_pos hy',Option.map_some]
      apply congrArg some
      apply Subtype.ext
      simpa only [permuteTree,Equiv.symm_apply_apply] using
        (permuteCode_genealogy N σ s hs (σ y)).symm
    · have hy' : σ y ∉ (state (permuteCode N σ s)).live := mt hl.mp hy
      simp only [permuteSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,
        dif_neg hy,dif_neg hy',Option.map_none]
  · funext x
    obtain ⟨y,rfl⟩ := σ.surjective x
    have hl : σ y ∈ (state (permuteCode N σ s)).live ↔ y ∈ (state s).live := by
      rw [permuteCode_live N σ s hs]
      simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
    simp only [permuteSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,hl,hfg]
  · exact (permuteCode_register N σ s hs).symm

lemma permuteCode_exit (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) (e : E) :
    permuteCode N σ (exitCode N s e) = exitCode N (permuteCode N σ s) e := by
  apply permuteCode_transport N σ s hs
  · exact commonDescendants_exit N s hs e
  · intro x
    simp only [permuteCode_location N σ s hs,Equiv.symm_apply_apply]

lemma permuteCode_ordinary (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) (e : E) :
    permuteCode N σ (ordinaryCode N s e) = ordinaryCode N (permuteCode N σ s) e := by
  apply permuteCode_transport N σ s hs
  · exact commonDescendants_ordinary N s hs e
  · intro x
    simp only [permuteCode_location N σ s hs,Equiv.symm_apply_apply]

lemma permuteCode_root (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    permuteCode N σ (rootCode N s) = rootCode N (permuteCode N σ s) := by
  apply permuteCode_transport N σ s hs
  · exact commonDescendants_root N s hs
  · intro x
    simp only [permuteCode_location N σ s hs,Equiv.symm_apply_apply]

lemma permuteCode_node_member (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (v : V) (x : Copy) :
    (σ x ∈ (state (permuteCode N σ s)).live ∧ (state (permuteCode N σ s)).location (σ x) = .node v) ↔
      (x ∈ (state s).live ∧ (state s).location x = .node v) := by
  simpa only [populationRoots,Finset.mem_filter] using
    permuteCode_population_member N σ s hs (.node v) x

noncomputable def permuteNodeEquiv (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (v : V) : AtNode (state s) v ≃ AtNode (state (permuteCode N σ s)) v where
  toFun a := ⟨σ a.val,(permuteCode_node_member N σ s hs v a.val).mpr a.property⟩
  invFun a := ⟨σ.symm a.val,by
    apply (permuteCode_node_member N σ s hs v _).mp
    simpa only [Equiv.apply_symm_apply] using a.property⟩
  left_inv a := by apply Subtype.ext; exact σ.symm_apply_apply a.val
  right_inv a := by apply Subtype.ext; exact σ.apply_symm_apply a.val

lemma permuteCode_pulse (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N)
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    (coin : AtNode (state s) H.hybrid → Bool) :
    permuteCode N σ (pulseCode H s coin) =
      pulseCode H (permuteCode N σ s)
        (GProgram.G7.CoinReindexing.coinTransport (permuteNodeEquiv N σ s hs H.hybrid) coin) := by
  apply permuteCode_transport N σ s hs
  · exact commonDescendants_pulse N H s hs coin
  · intro x
    by_cases hx : x ∈ (state s).live ∧ (state s).location x = .node H.hybrid
    · have hx' := (permuteCode_node_member N σ s hs H.hybrid x).mpr hx
      simp only [dif_pos hx,dif_pos hx',GProgram.G7.CoinReindexing.coinTransport]
      congr 2
      apply congrArg coin
      apply Subtype.ext
      exact σ.symm_apply_apply x
    · have hx' := mt (permuteCode_node_member N σ s hs H.hybrid x).mp hx
      rw [dif_neg hx',dif_neg hx]
      simpa only [Equiv.symm_apply_apply] using permuteCode_location N σ s hs (σ x)

lemma permuteCode_independentPulse (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    (independentPulseKernel H gamma s).map (permuteCode N σ) =
      independentPulseKernel H gamma (permuteCode N σ s) := by
  unfold independentPulseKernel
  rw [← GProgram.G7.CoinReindexing.current_coin_pmf (permuteNodeEquiv N σ s hs H.hybrid) gamma,
    PMF.map_comp,PMF.map_comp]
  congr 1
  funext coin
  exact permuteCode_pulse N H σ s hs coin

/-- Only the all-INDEPENDENT suffix is needed for the new three-root readout.
The preserved original register is inert in every one of these operations. -/
def IndependentBoundary (N : RootedBinary V E X) : BoundaryOperation N → Prop
  | .common _ => False
  | _ => True

lemma permuteCode_boundary (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (hop : IndependentBoundary N op)
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    (boundaryKernel N op s).map (permuteCode N σ) =
      boundaryKernel N op (permuteCode N σ s) := by
  cases op with
  | exit e => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (permuteCode_exit N σ s hs e)
  | ordinary e he => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (permuteCode_ordinary N σ s hs e)
  | root => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (permuteCode_root N σ s hs)
  | independent H gamma => exact permuteCode_independentPulse N H gamma σ s hs
  | common H => exact False.elim hop

def IndependentWord (N : RootedBinary V E X) (ops : List (ProgramStep N)) : Prop :=
  ∀ op ∈ ops, match op with | .interval _ => True | .boundary b => IndependentBoundary N b

lemma permuteCode_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (hops : IndependentWord N ops)
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    (sourceProgram N r ops s).map (permuteCode N σ) =
      sourceProgram N r ops (permuteCode N σ s) := by
  induction ops generalizing s with
  | nil => simp only [sourceProgram,PMF.pure_map]
  | cons op ops ih =>
    have ht : IndependentWord N ops := fun x hx => hops x (List.mem_cons_of_mem _ hx)
    have hh := hops op (List.mem_cons_self ..)
    cases op with
    | interval t =>
      simp only [sourceProgram,PMF.map_bind,sourceProgramStep]
      rw [← permuteCode_time N r σ t s hs,PMF.bind_map]
      apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
      intro d hd
      exact ih ht d (commonDescendants_time N r t s hs hd)
    | boundary b =>
      simp only [sourceProgram,PMF.map_bind,sourceProgramStep]
      rw [← permuteCode_boundary N b hh σ s hs,PMF.bind_map]
      apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
      intro d hd
      exact ih ht d (commonDescendants_boundary N b s hs hd)

open UnifiedLean.Source.SourceEmbeddedJumpLaw UnifiedLean.Source.SourceAncestralCompletion

lemma permuteChoice_jumpMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) (q : Option (Choice N s)) :
    jumpMass N r (permuteCode N σ s) (q.map (permuteChoiceEquiv N σ s hs)) = jumpMass N r s q := by
  cases q with
  | none => simp only [Option.map_none,jumpMass,permuteCode_totalRate N r σ s hs]
  | some q => simp only [Option.map_some,jumpMass,permuteChoice_rate N r σ s hs,
      permuteCode_totalRate N r σ s hs]

lemma permuteChoice_jumpPMF (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    (sourceJumpChoice N r s).map (Equiv.optionCongr (permuteChoiceEquiv N σ s hs)) =
      sourceJumpChoice N r (permuteCode N σ s) := by
  apply PMF.ext
  intro b
  rw [map_equiv_mass]
  let e := Equiv.optionCongr (permuteChoiceEquiv N σ s hs)
  have hm := permuteChoice_jumpMass N r σ s hs (e.symm b)
  have he : (e.symm b).map (permuteChoiceEquiv N σ s hs) = b := e.apply_symm_apply b
  rw [he] at hm
  simpa only [sourceJumpChoice_apply] using congrArg ENNReal.ofReal hm.symm

lemma permuteCode_jumpStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    (sourceJumpStep N r s).map (permuteCode N σ) = sourceJumpStep N r (permuteCode N σ s) := by
  unfold sourceJumpStep
  rw [← permuteChoice_jumpPMF N r σ s hs,PMF.map_comp,PMF.map_comp]
  congr 1
  funext q
  exact permuteCode_destination N σ s hs q

lemma commonDescendants_jump (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : CommonDescendants N sample (state s))
    {d : Code N sample} (hd : d ∈ (sourceJumpStep N r s).support) :
    CommonDescendants N sample (state d) := by
  obtain ⟨q,hq,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  exact commonDescendants_destination N s hs q

lemma permuteCode_completion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (σ : Equiv.Perm Copy) (k : Nat) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) :
    (ancestralCompletion N r k s).map (permuteCode N σ) =
      ancestralCompletion N r k (permuteCode N σ s) := by
  induction k generalizing s with
  | zero => simp only [ancestralCompletion,PMF.pure_map]
  | succ k ih =>
    rw [ancestralCompletion,PMF.map_bind,ancestralCompletion,
      ← permuteCode_jumpStep N r σ s hs,PMF.bind_map]
    apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
    intro d hd
    exact ih _ (commonDescendants_jump N r s hs hd)

/-- Actual natural-INDEPENDENT suffix and finite ancestral completion commute
with the same copy permutation on every supported common-descendant state.
This is a source-kernel statement, before the passive three-cherry quotient. -/
theorem independent_completed_program_permutation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (hops : IndependentWord N ops)
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    ((sourceProgram N r ops s).bind (ancestralCompletion N r (Fintype.card Copy))).map (permuteCode N σ) =
      (sourceProgram N r ops (permuteCode N σ s)).bind (ancestralCompletion N r (Fintype.card Copy)) := by
  rw [PMF.map_bind,← permuteCode_program N r ops hops σ s hs,PMF.bind_map]
  apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
  intro d hd
  exact permuteCode_completion N r σ _ d (commonDescendants_program N r ops s hs hd)

end Permutations
section TripletReadout
open GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

lemma wellLabelled_two_tree (t : Genealogy Copy) (ht : t.WellLabelled)
    (hc : t.leaves.card = 2) :
    ∃ a b : Copy, a ≠ b ∧ t = .graft (.leaf a) (.leaf b) := by
  cases t with
  | leaf x => simp only [Genealogy.leaves,Finset.card_singleton] at hc; omega
  | graft u v =>
    have hu := Finset.card_pos.mpr (genealogy_leaves_nonempty u)
    have hv := Finset.card_pos.mpr (genealogy_leaves_nonempty v)
    have hh : u.leaves.card + v.leaves.card = 2 := by
      simpa only [Genealogy.leaves,Finset.card_union_of_disjoint ht.2.2] using hc
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (show u.leaves.card = 1 by omega)
    obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (show v.leaves.card = 1 by omega)
    have he : a ≠ b := by
      intro hab
      subst b
      exact Finset.disjoint_left.mp ht.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
        (by rw [hb]; exact Finset.mem_singleton_self a)
    exact ⟨a,b,he,by rw [G1OriginalCurrentRootReconstruction.wellLabelled_singleton_tree u ht.1 a ha,
      G1OriginalCurrentRootReconstruction.wellLabelled_singleton_tree v ht.2.1 b hb]⟩

def tripletTree (a b c : Copy) : Genealogy Copy := .graft (.graft (.leaf a) (.leaf b)) (.leaf c)

lemma wellLabelled_three_tree (t : Genealogy Copy) (ht : t.WellLabelled)
    (hc : t.leaves.card = 3) :
    ∃ a b c : Copy, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ UnorderedEquiv t (tripletTree a b c) := by
  cases t with
  | leaf x => simp only [Genealogy.leaves,Finset.card_singleton] at hc; omega
  | graft u v =>
    have hu := Finset.card_pos.mpr (genealogy_leaves_nonempty u)
    have hv := Finset.card_pos.mpr (genealogy_leaves_nonempty v)
    have hh : u.leaves.card + v.leaves.card = 3 := by
      simpa only [Genealogy.leaves,Finset.card_union_of_disjoint ht.2.2] using hc
    have side (u v : Genealogy Copy) (hwu : u.WellLabelled) (hwv : v.WellLabelled)
        (hd : Disjoint u.leaves v.leaves) (hu : u.leaves.card = 2) (hv : v.leaves.card = 1) :
        ∃ a b c : Copy, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ .graft u v = tripletTree a b c := by
      obtain ⟨a,b,hab,rfl⟩ := wellLabelled_two_tree u hwu hu
      obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hv
      have hve := G1OriginalCurrentRootReconstruction.wellLabelled_singleton_tree v hwv c hc
      subst v
      refine ⟨a,b,c,hab,?_,?_,rfl⟩
      · intro h; subst c; exact (Finset.disjoint_left.mp hd (show a ∈ ((Genealogy.leaf a).graft (.leaf b)).leaves from by simp [Genealogy.leaves])) (by simp [Genealogy.leaves])
      · intro h; subst c; exact (Finset.disjoint_left.mp hd (show b ∈ ((Genealogy.leaf a).graft (.leaf b)).leaves from by simp [Genealogy.leaves])) (by simp [Genealogy.leaves])
    by_cases h2 : u.leaves.card = 2
    · obtain ⟨a,b,c,hab,hac,hbc,he⟩ := side u v ht.1 ht.2.1 ht.2.2 h2 (by omega)
      exact ⟨a,b,c,hab,hac,hbc,he ▸ UnorderedEquiv.refl _⟩
    · obtain ⟨a,b,c,hab,hac,hbc,he⟩ := side v u ht.2.1 ht.1 ht.2.2.symm (by omega) (by omega)
      exact ⟨a,b,c,hab,hac,hbc,he ▸ UnorderedEquiv.swap u v⟩

/-- The index is the single taxon outside the cherry. -/
def threeCherry : Fin 3 → UnrankedTree (Fin 3)
  | 0 => toUnranked (tripletTree 1 2 0)
  | 1 => toUnranked (tripletTree 0 2 1)
  | 2 => toUnranked (tripletTree 0 1 2)

lemma triplet_swap (a b c : Copy) :
    toUnranked (tripletTree a b c) = toUnranked (tripletTree b a c) := by
  apply Quotient.sound
  exact UnorderedEquiv.graft (UnorderedEquiv.swap _ _) (UnorderedEquiv.refl _)

lemma threeCherry_covers (t : Genealogy (Fin 3)) (ht : t.WellLabelled)
    (hleaves : t.leaves = Finset.univ) : ∃ j, toUnranked t = threeCherry j := by
  obtain ⟨a,b,c,hab,hac,hbc,he⟩ := wellLabelled_three_tree t ht (by rw [hleaves]; decide)
  have he' : toUnranked t = toUnranked (tripletTree a b c) := Quotient.sound he
  refine ⟨c,he'.trans ?_⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first | exact False.elim (hab rfl) | exact False.elim (hac rfl) | exact False.elim (hbc rfl) |
      rfl | exact triplet_swap _ _ _

open GProgram.G5.Normalization G1ActualWholeUnrootedCutTreeFamily

noncomputable def observedClusters : UnrankedTree Copy → Finset (Finset Copy) :=
  Quotient.lift treeClusters (fun _ _ h => unordered_tree_clusters h)

lemma threeCherry_pair12 (j : Fin 3) :
    ({1,2} : Finset (Fin 3)) ∈ observedClusters (threeCherry j) ↔ j = 0 := by
  fin_cases j <;> simp [threeCherry,observedClusters,toUnranked,tripletTree,
    treeClusters,Genealogy.leaves,Finset.ext_iff] <;> decide

lemma threeCherry_pair02 (j : Fin 3) :
    ({0,2} : Finset (Fin 3)) ∈ observedClusters (threeCherry j) ↔ j = 1 := by
  fin_cases j <;> simp [threeCherry,observedClusters,toUnranked,tripletTree,
    treeClusters,Genealogy.leaves,Finset.ext_iff] <;> decide

lemma threeCherry_injective : Function.Injective threeCherry := by
  intro i j he
  have hc := congrArg observedClusters he
  have h0 : (i = 0 ↔ j = 0) := by
    rw [← threeCherry_pair12,← threeCherry_pair12,hc]
  have h1 : (i = 1 ↔ j = 1) := by
    rw [← threeCherry_pair02,← threeCherry_pair02,hc]
  fin_cases i <;> fin_cases j <;> simp_all

open UnifiedLean.Source.SourceUnrankedCopyProjectivity
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceActualHoldingClocks

lemma triplet_canonical (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    toUnranked (tripletTree a b c) = threeCherry c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first | exact False.elim (hab rfl) | exact False.elim (hac rfl) | exact False.elim (hbc rfl) |
      rfl | exact triplet_swap _ _ _

lemma threeCherry_permutation (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    mapUnranked σ (threeCherry j) = threeCherry (σ j) := by
  fin_cases j <;>
    simp only [threeCherry,mapUnranked_toUnranked,tripletTree,mapLabels] <;>
    apply triplet_canonical <;> apply σ.injective.ne <;> decide

lemma fullForest_image {V E : Type*} (s : State V E Copy) :
    sourceUnrankedForest s Finset.univ =
      Finset.univ.image (fun x => toUnranked (s.genealogy (s.ancestor x))) := by
  ext q
  rw [mem_sourceUnrankedForest,Finset.mem_image]
  simp only [Finset.mem_univ,full_prune,Option.some.injEq,true_and]
  constructor
  · rintro ⟨x,t,ht,hq⟩
    subst t
    exact ⟨x,hq⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,_,rfl,hx⟩

lemma permuteCode_fullForest (N : RootedBinary V E X) {sample : Copy → X}
    (σ : Equiv.Perm Copy) (s : Code N sample) (hs : CommonDescendants N sample (state s)) :
    sourceUnrankedForest (state (permuteCode N σ s)) Finset.univ =
      (sourceUnrankedForest (state s) Finset.univ).image (mapUnranked σ) := by
  rw [fullForest_image,fullForest_image,Finset.image_image]
  ext q
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨σ.symm x,?_⟩
    simpa only [permuteCode_ancestor N σ s hs,permuteCode_genealogy N σ s hs,
      Equiv.symm_apply_apply,mapUnranked_toUnranked] using hx
  · rintro ⟨x,hx⟩
    refine ⟨σ x,?_⟩
    simpa only [permuteCode_ancestor N σ s hs,permuteCode_genealogy N σ s hs,
      Equiv.symm_apply_apply,mapUnranked_toUnranked] using hx

lemma terminal_threeCherry (N : RootedBinary V E X) {sample : Fin 3 → X}
    (s : Code N sample) (hc : liveCard s ≤ 1) :
    ∃ j : Fin 3, sourceUnrankedForest (state s) Finset.univ = {threeCherry j} := by
  let l := (state s).ancestor 0
  have hl : l ∈ (state s).live := (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).ancestor_live 0
  have ha : ∀ x, (state s).ancestor x = l := by
    intro x
    exact (Finset.card_le_one.mp hc) _ ((show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).ancestor_live x) _ hl
  have ht : ((state s).genealogy l).leaves = Finset.univ := by
    ext x
    rw [(show Valid (state s) from s.property.forest).leaf_fiber l hl]
    simp only [ha,Finset.mem_univ]
  obtain ⟨j,hj⟩ := threeCherry_covers ((state s).genealogy l) ((show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).wellLabelled l hl) ht
  refine ⟨j,?_⟩
  rw [fullForest_image]
  simp only [ha,hj]
  exact Finset.image_const Finset.univ_nonempty _

noncomputable def tripleForestMass (N : RootedBinary V E X) {sample : Fin 3 → X}
    (p : PMF (Code N sample)) (j : Fin 3) : ℝ≥0∞ :=
  (p.map (fun s => sourceUnrankedForest (state s) Finset.univ)) {threeCherry j}

lemma threeCherry_mass_sum (N : RootedBinary V E X) {sample : Fin 3 → X}
    (p : PMF (Code N sample)) (hterm : ∀ s ∈ p.support, liveCard s ≤ 1) :
    ∑ j : Fin 3, tripleForestMass N p j = 1 := by
  simp only [tripleForestMass,PMF.map_apply,tsum_fintype]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s, p s := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hp : p s = 0
      · simp only [hp,ite_self,Finset.sum_const_zero]
      · obtain ⟨j,hj⟩ := terminal_threeCherry N s (hterm s ((PMF.mem_support_iff _ _).mpr hp))
        simp only [hj,Finset.singleton_inj,threeCherry_injective.eq_iff]
        simp
    _ = 1 := by simpa only [tsum_fintype] using p.tsum_coe

lemma threeCherry_mass_permutation (N : RootedBinary V E X) {sample : Fin 3 → X}
    (p : PMF (Code N sample)) (hgood : ∀ s ∈ p.support, CommonDescendants N sample (state s))
    (σ : Equiv.Perm (Fin 3)) (hsym : p.map (permuteCode N σ) = p) (j : Fin 3) :
    tripleForestMass N p (σ j) = tripleForestMass N p j := by
  let obs := fun s : Code N sample => sourceUnrankedForest (state s) Finset.univ
  have hi : Function.Injective (mapUnranked σ) :=
    (DotG4.ActualLegalPanelComb.mapUnranked_leftInverse σ σ.symm σ.left_inv).injective
  have hF : Function.Injective (Finset.image (mapUnranked σ)) := Finset.image_injective hi
  change (p.map obs) {threeCherry (σ j)} = (p.map obs) {threeCherry j}
  conv_lhs => rw [← hsym,PMF.map_comp]
  rw [PMF.map_apply,PMF.map_apply,tsum_fintype,tsum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hp : p s = 0
  · simp only [hp,ite_self]
  · have hs := hgood s ((PMF.mem_support_iff _ _).mpr hp)
    have he : ({threeCherry (σ j)} : Finset (UnrankedTree (Fin 3))) =
        ({threeCherry j} : Finset (UnrankedTree (Fin 3))).image (mapUnranked σ) := by
      simp only [Finset.image_singleton,threeCherry_permutation]
    have ho : obs (permuteCode N σ s) = (obs s).image (mapUnranked σ) := permuteCode_fullForest N σ s hs
    simp only [Function.comp_apply,ho,he,hF.eq_iff]
    split_ifs <;> rfl

/-- Three disjoint exhaustive terminal cherry events and actual permutation
invariance give the exact reader. Later independent splitting is permitted. -/
theorem threeCherry_uniform (N : RootedBinary V E X) {sample : Fin 3 → X}
    (p : PMF (Code N sample)) (hterm : ∀ s ∈ p.support, liveCard s ≤ 1)
    (hgood : ∀ s ∈ p.support, CommonDescendants N sample (state s))
    (hsym : ∀ σ : Equiv.Perm (Fin 3), p.map (permuteCode N σ) = p) (j : Fin 3) :
    (tripleForestMass N p j).toReal = (1 : ℝ)/3 := by
  have heq : ∀ i : Fin 3, tripleForestMass N p i = tripleForestMass N p j := by
    intro i
    have h := threeCherry_mass_permutation N p hgood (Equiv.swap j i) (hsym _) j
    simpa only [Equiv.swap_apply_left] using h
  have hsum := congrArg ENNReal.toReal (threeCherry_mass_sum N p hterm)
  rw [ENNReal.toReal_sum (f := fun i => tripleForestMass N p i) (fun i _ => PMF.apply_ne_top _ _)] at hsum
  simp only [ENNReal.toReal_one] at hsum
  simp_rw [heq] at hsum
  norm_num at hsum
  linarith

open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion

noncomputable def colocatedState (place : Location V E) (ρ : V → Bool) : State V E Copy where
  live := Finset.univ
  ancestor := id
  genealogy := Genealogy.leaf
  location := fun _ => place
  register := ρ
  history := []

lemma colocatedState_valid (place : Location V E) (ρ : V → Bool) :
    Valid (colocatedState (Copy := Copy) place ρ) := by
  constructor
  · intro x; exact Finset.mem_univ x
  · intro l hl; rfl
  · intro l hl x; simp only [colocatedState,Genealogy.leaves,Finset.mem_singleton,id_eq]
  · intro l hl; trivial

noncomputable def colocatedCode (N : RootedBinary V E X) (sample : Copy → X)
    (place : Location V E) (ρ : V → Bool) (hplace : ∀ x, DescendsTo N place (sample x)) : Code N sample :=
  admittedCode N sample (colocatedState place ρ) ⟨colocatedState_valid place ρ,hplace⟩

lemma colocatedCode_commonDescendants (N : RootedBinary V E X) (sample : Copy → X)
    (place : Location V E) (ρ : V → Bool) (hplace : ∀ x, DescendsTo N place (sample x)) :
    CommonDescendants N sample (state (colocatedCode N sample place ρ hplace)) := by
  intro x y
  change DescendsTo N (copyLocation (decodeSnapshot N.root (encodeSnapshot (colocatedState place ρ) (colocatedState_valid place ρ))) x) (sample y)
  rw [decode_encode_copyLocation]
  exact hplace y

lemma colocatedCode_permutation (N : RootedBinary V E X) (sample : Copy → X)
    (place : Location V E) (ρ : V → Bool) (hplace : ∀ x, DescendsTo N place (sample x))
    (σ : Equiv.Perm Copy) :
    permuteCode N σ (colocatedCode N sample place ρ hplace) = colocatedCode N sample place ρ hplace := by
  apply Subtype.ext
  rw [permuteCode_val N σ _ (colocatedCode_commonDescendants N sample place ρ hplace)]
  change permuteSnapshot σ (encodeSnapshot (colocatedState place ρ) (colocatedState_valid place ρ)) =
    encodeSnapshot (colocatedState place ρ) (colocatedState_valid place ρ)
  apply Snapshot.ext
  · ext x
    simp only [permuteSnapshot,encodeSnapshot,colocatedState,Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun _ => trivial,fun _ => σ.surjective x⟩
  · funext x; simp only [permuteSnapshot,encodeSnapshot,colocatedState,id_eq,Equiv.apply_symm_apply]
  · funext x
    simp only [permuteSnapshot,encodeSnapshot,colocatedState,Finset.mem_univ,dif_pos,
      Option.map_some]
    apply congrArg some
    apply Subtype.ext
    simp only [permuteTree,mapLabels,Equiv.apply_symm_apply]
  · funext x; simp only [permuteSnapshot,encodeSnapshot,colocatedState,Finset.mem_univ,ite_true]
  · rfl

lemma commonDescendants_completion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample)
    (hs : CommonDescendants N sample (state s)) {d : Code N sample}
    (hd : d ∈ (ancestralCompletion N r n s).support) : CommonDescendants N sample (state d) := by
  induction n generalizing s d with
  | zero =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
    exact hs
  | succ n ih =>
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    exact ih z (commonDescendants_jump N r s hs hz) hdz

/-- The source-level three-singleton entrance reader, conditional only on the
structural ancestral-entry fact supplied by the actual remaining calendar.
No exchangeability or scalar probability is an input field. -/
theorem independent_colocated_triplet_reader (N : RootedBinary V E X)
    (sample : Fin 3 → X) (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : IndependentWord N ops) (place : Location V E) (ρ : V → Bool)
    (hplace : ∀ x, DescendsTo N place (sample x))
    (hroot : ∀ z ∈ (sourceProgram N r ops (colocatedCode N sample place ρ hplace)).support,
      AncestralRoot N z) (j : Fin 3) :
    (tripleForestMass N ((sourceProgram N r ops (colocatedCode N sample place ρ hplace)).bind
      (ancestralCompletion N r (Fintype.card (Fin 3)))) j).toReal = (1 : ℝ)/3 := by
  let s := colocatedCode N sample place ρ hplace
  have hs : CommonDescendants N sample (state s) := colocatedCode_commonDescendants N sample place ρ hplace
  apply threeCherry_uniform N
  · intro d hd
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    exact (ancestral_completion_terminal_support N r _ z (hroot z hz)
      (Finset.card_le_univ _) hdz).2
  · intro d hd
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    exact commonDescendants_completion N r _ z (commonDescendants_program N r ops s hs hz) hdz
  · intro σ
    have he := independent_completed_program_permutation N r ops hops σ s hs
    simpa only [s,colocatedCode_permutation N sample place ρ hplace σ] using he

end TripletReadout

section ActualTripletCut
open GProgram.SourceForest GProgram.G7.NodeActions
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.UnrankedGenealogyObservation
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

lemma step_canonical (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : Canonical s) (q : Option (Choice N s)) :
    Canonical (stepDestination N s q) := by
  cases q with
  | none => exact hs
  | some q =>
    unfold stepDestination
    exact admitted_canonical N sample _ _

lemma iteration_canonical (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) (hs : Canonical s)
    {d : Code N sample} (hd : d ∈ (sourceIteration N r k s).support) : Canonical d := by
  induction k generalizing s d with
  | zero => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact hs
  | succ k ih =>
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    obtain ⟨q,hq,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    exact ih _ (step_canonical N s hs q) hdz

lemma time_canonical (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (hs : Canonical s)
    {d : Code N sample} (hd : d ∈ (sourceTimeKernel N r t s).support) : Canonical d := by
  obtain ⟨k,hk,hkd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact iteration_canonical N r k s hs hkd

lemma boundary_canonical (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample)
    {d : Code N sample} (hd : d ∈ (boundaryKernel N op s).support) : Canonical d := by
  cases op with
  | exit e => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact admitted_canonical N sample _ _
  | ordinary e he => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact admitted_canonical N sample _ _
  | root => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact admitted_canonical N sample _ _
  | common H => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact admitted_canonical N sample _ _
  | independent H gamma =>
    obtain ⟨coin,hc,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
    exact admitted_canonical N sample _ _

lemma program_canonical (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (hs : Canonical s)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) : Canonical d := by
  induction ops generalizing s d with
  | nil => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact hs
  | cons op ops ih =>
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply ih z ?_ hdz
    cases op with
    | interval t => exact time_canonical N r t s hs hz
    | boundary b => exact boundary_canonical N b s hz

lemma canonical_colocated_full_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : Canonical s) (hcard : liveCard s = Fintype.card Copy)
    (place : Location V E) (hloc : ∀ x, copyLocation (state s) x = place)
    (hplace : ∀ x, DescendsTo N place (sample x)) :
    s = colocatedCode N sample place (state s).register hplace := by
  have hl : (state s).live = Finset.univ := Finset.eq_univ_of_card _ hcard
  have ha : ∀ x, (state s).ancestor x = x := fun x =>
    (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).representative x (by rw [hl]; exact Finset.mem_univ x)
  have hg : ∀ x, (state s).genealogy x = .leaf x := by
    intro x
    apply G1OriginalCurrentRootReconstruction.wellLabelled_singleton_tree _
      ((show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).wellLabelled x (by rw [hl]; exact Finset.mem_univ x)) x
    ext y
    rw [(show Valid (state s) from s.property.forest).leaf_fiber x (by rw [hl]; exact Finset.mem_univ x)]
    change (state s).ancestor y = x ↔ y ∈ ({x} : Finset Copy)
    simp only [ha,Finset.mem_singleton]
  apply canonical_ext s _ hs (admitted_canonical N sample _ _)
  apply GProgram.G7.NodeActions.state_ext
  · simpa only [colocatedCode,state,admittedCode,decodeSnapshot,encodeSnapshot,colocatedState] using hl
  · funext x
    simpa only [colocatedCode,state,admittedCode,decodeSnapshot,encodeSnapshot,colocatedState,id_eq] using ha x
  · funext x
    simpa only [colocatedCode,state,admittedCode,decodeSnapshot,encodeSnapshot,colocatedState,
      Finset.mem_univ,dif_pos] using hg x
  · funext x
    have hx := hloc x
    rw [copyLocation,ha] at hx
    simpa only [colocatedCode,state,admittedCode,decodeSnapshot,encodeSnapshot,colocatedState,
      Finset.mem_univ,ite_true] using hx
  · rfl
  · rfl

lemma independentWord_append (N : RootedBinary V E X) (a b : List (ProgramStep N)) :
    IndependentWord N (a ++ b) ↔ IndependentWord N a ∧ IndependentWord N b := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append_left b hx),fun x hx => h x (List.mem_append_right a hx)⟩
  · rintro ⟨ha,hb⟩ x hx
    exact (List.mem_append.mp hx).elim (ha x) (hb x)

lemma independentWord_boundary_map (N : RootedBinary V E X) {A : Type*}
    (f : A → BoundaryOperation N) (hf : ∀ a, IndependentBoundary N (f a)) (xs : List A) :
    IndependentWord N (xs.map (fun a => ProgramStep.boundary (f a))) := by
  intro op hop
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hop
  exact hf a

lemma actual_independent_node (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (v : V) :
    IndependentBoundary N (originalNodeOperation N H gamma (fun _ => false) v) := by
  by_cases hr : v = N.root
  · simp [originalNodeOperation,hr,IndependentBoundary]
  · by_cases hh : N.graph.IsHybrid v <;> simp [originalNodeOperation,hr,hh,IndependentBoundary]

lemma actual_independent_batch (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (a : ℝ) :
    IndependentWord N (boundaryOperations N C H gamma (fun _ => false) a) := by
  unfold boundaryOperations
  apply (independentWord_append N _ _).mpr
  exact ⟨independentWord_boundary_map N (fun e => .exit e) (fun _ => trivial) _,
    independentWord_boundary_map N _ (actual_independent_node N H gamma) _⟩

lemma actual_independent_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (a : ℝ) (dates : List ℝ) :
    IndependentWord N (calendarTail N C H gamma (fun _ => false) a dates) := by
  induction dates generalizing a with
  | nil => intro op hop; cases hop
  | cons b dates ih =>
    intro op hop
    rcases List.mem_cons.mp hop with rfl | hop
    · trivial
    · exact ((independentWord_append N _ _).mpr
        ⟨actual_independent_batch N C H gamma b,ih b⟩) op hop

lemma actual_independent_calendar (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) :
    IndependentWord N (compiledCalendarProgram N C H gamma (fun _ => false)) := by
  unfold compiledCalendarProgram
  cases sortedOriginalDates N C with
  | nil => intro op hop; cases hop
  | cons a dates =>
    apply (independentWord_append N _ _).mpr
    exact ⟨actual_independent_batch N C H gamma a,actual_independent_tail N C H gamma a dates⟩

/-- Actual calendar specialization: the ancestral-entry condition is discharged
from initialized support, with arbitrary original tip ages and literal tied cut.
Only the no-loss/co-location entrance is retained for the later prefix split. -/
theorem actual_independent_cut_triplet_reader (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (ρ : V → Bool) (past future : List (ProgramStep N))
    (hp : compiledCalendarProgram N C H gamma (fun _ => false) = past ++ future)
    (s : Code N sample) (hs : s ∈ (sourceProgram N r past (initialCode N sample ρ)).support)
    (hcard : liveCard s = Fintype.card (Fin 3)) (place : Location V E)
    (hloc : ∀ x, copyLocation (state s) x = place) (j : Fin 3) :
    (tripleForestMass N ((sourceProgram N r future s).bind
      (ancestralCompletion N r (Fintype.card (Fin 3)))) j).toReal = (1 : ℝ)/3 := by
  have hcan : Canonical s := program_canonical N r past _ (admitted_canonical N sample _ _) hs
  have hplace : ∀ x, DescendsTo N place (sample x) := by
    intro x
    have hx : DescendsTo N (copyLocation (state s) x) (sample x) := s.property.original_descendant x
    rwa [hloc x] at hx
  have he := canonical_colocated_full_card N s hcan hcard place hloc hplace
  have hfuture : IndependentWord N future := by
    have h := actual_independent_calendar N C H gamma
    rw [hp,independentWord_append] at h
    exact h.2
  have hroot : ∀ z ∈ (sourceProgram N r future s).support, AncestralRoot N z := by
    intro z hz
    apply initialized_original_calendar_ancestral_support N C sample ρ H gamma (fun _ => false) r
    rw [hp,sourceProgram_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨s,hs,hz⟩
  rw [he] at hroot ⊢
  exact independent_colocated_triplet_reader N sample r future hfuture place (state s).register hplace hroot j

end ActualTripletCut
section IndependentRouteTrace
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.SourceForestKingmanPopulationProjection
open GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceActualHoldingClocks
open DotG34.ActualSerialSurvival
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- Expectation of a nonnegative test; used only to unfold the actual finite
routing recursion. It adds no physical clock or observed private variable. -/
noncomputable def positiveExpectation {A : Type*} (p : PMF A) (f : A → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * f a

lemma positiveExpectation_pure {A : Type*} (a : A) (f : A → ℝ≥0∞) :
    positiveExpectation (PMF.pure a) f = f a := by
  classical
  simp [positiveExpectation,PMF.pure_apply]

lemma positiveExpectation_bind {A B : Type*} (p : PMF A) (q : A → PMF B) (f : B → ℝ≥0∞) :
    positiveExpectation (p.bind q) f = positiveExpectation p (fun a => positiveExpectation (q a) f) := by
  unfold positiveExpectation
  simp only [PMF.bind_apply,← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  exact mul_assoc _ _ _

lemma positiveExpectation_map {A B : Type*} (p : PMF A) (g : A → B) (f : B → ℝ≥0∞) :
    positiveExpectation (p.map g) f = positiveExpectation p (f ∘ g) := by
  rw [PMF.map,positiveExpectation_bind]
  simp only [positiveExpectation_pure,Function.comp_def]

lemma positiveExpectation_mul {A : Type*} (p : PMF A) (c : ℝ≥0∞) (f : A → ℝ≥0∞) :
    positiveExpectation p (fun a => c * f a) = c * positiveExpectation p f := by
  unfold positiveExpectation
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  dsimp only
  ac_rfl

/-- The whole finite no-merger routing trace, including the state before each
operation and the final state. Original current-owner Bernoulli kernels are
used literally; intervals leave the trace state unchanged. -/
noncomputable def routingTrace (N : RootedBinary V E X) {sample : Copy → X} :
    List (ProgramStep N) → Code N sample → PMF (List (Code N sample))
  | [],s => PMF.pure [s]
  | .interval _ :: ops,s => (routingTrace N ops s).map (List.cons s)
  | .boundary b :: ops,s =>
      ((boundaryKernel N b s).bind (routingTrace N ops)).map (List.cons s)

noncomputable def traceExposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N) → List (Code N sample) → ℝ
  | [],_ => 0
  | _,[] => 0
  | .interval t :: ops,s::states => totalRate N r s * (t : ℝ) + traceExposure N r ops states
  | .boundary _ :: ops,_::states => traceExposure N r ops states

lemma traceExposure_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (states : List (Code N sample)) :
    0 ≤ traceExposure N r ops states := by
  induction ops generalizing states with
  | nil => exact le_rfl
  | cons op ops ih =>
    cases states with
    | nil => exact le_rfl
    | cons s states =>
      cases op with
      | boundary b => exact ih states
      | interval t => exact add_nonneg (mul_nonneg (totalRate_nonnegative N r s) t.property) (ih states)

lemma routingTrace_shape (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) {states : List (Code N sample)}
    (h : states ∈ (routingTrace N ops s).support) :
    ∃ tail, states = s::tail ∧ states.length = ops.length+1 := by
  induction ops generalizing s states with
  | nil =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp h
    exact ⟨[],rfl,rfl⟩
  | cons op ops ih =>
    cases op with
    | interval t =>
      obtain ⟨tail,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
      obtain ⟨rest,he,hlen⟩ := ih s ht
      exact ⟨tail,rfl,by simp only [List.length_cons]; omega⟩
    | boundary b =>
      obtain ⟨tail,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
      obtain ⟨d,hd,hdt⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      obtain ⟨rest,he,hlen⟩ := ih d hdt
      exact ⟨tail,rfl,by simp only [List.length_cons]; omega⟩

/-- Actual compiler no-loss mass is the exponential average over its own
routing traces, proved from accepted weightedRoute, not from a new mixture
assumption or a separately constructed two-route clock model. -/
theorem actual_no_loss_trace_mixture (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ((sourceProgram N r ops s).map liveCard) (liveCard s) =
      positiveExpectation (routingTrace N ops s)
        (fun states => ENNReal.ofReal (Real.exp (-traceExposure N r ops states))) := by
  rw [actual_no_loss_event]
  induction ops generalizing s with
  | nil =>
    simp only [DotG34.ActualSerialSurvival.weightedRoute,routingTrace,positiveExpectation_pure,traceExposure,neg_zero,Real.exp_zero,ENNReal.ofReal_one]
    exact (PMF.pure s).tsum_coe
  | cons op ops ih =>
    cases op with
    | interval t =>
      change (∑' d, sourceTimeKernel N r t s s * DotG34.ActualSerialSurvival.weightedRoute N r ops s d) = _
      rw [ENNReal.tsum_mul_left,ih,actual_holding_weight,routingTrace,positiveExpectation_map]
      change ENNReal.ofReal (Real.exp (-(totalRate N r s * (t : ℝ)))) *
        positiveExpectation (routingTrace N ops s) (fun states => ENNReal.ofReal (Real.exp (-traceExposure N r ops states))) =
        positiveExpectation (routingTrace N ops s) (fun states => ENNReal.ofReal (Real.exp (-(totalRate N r s * (t : ℝ) + traceExposure N r ops states))))
      try simp only [neg_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact (positiveExpectation_mul _ _ _).symm
    | boundary b =>
      change (∑' d, ∑' m, boundaryKernel N b s m * DotG34.ActualSerialSurvival.weightedRoute N r ops m d) = _
      rw [ENNReal.tsum_comm,routingTrace,positiveExpectation_map]
      change (∑' m, ∑' d, boundaryKernel N b s m * DotG34.ActualSerialSurvival.weightedRoute N r ops m d) =
        positiveExpectation ((boundaryKernel N b s).bind (routingTrace N ops))
          (fun states => ENNReal.ofReal (Real.exp (-traceExposure N r ops states)))
      rw [positiveExpectation_bind]
      unfold positiveExpectation
      apply tsum_congr
      intro d
      rw [ENNReal.tsum_mul_left,ih]
      rfl

open GProgram.G5.SafePrefixRouteBridge

/-- Only routing operations read these original sites. -/
def boundarySite (N : RootedBinary V E X) : BoundaryOperation N → Option V
  | .independent H _ => some H.hybrid
  | .common H => some H.hybrid
  | _ => none

def wordSites (N : RootedBinary V E X) : List (ProgramStep N) → List V
  | [] => []
  | .interval _ :: ops => wordSites N ops
  | .boundary b :: ops => (boundarySite N b).toList ++ wordSites N ops

noncomputable def positionTrace (N : RootedBinary V E X) (reg : V → Bool) :
    List (ProgramStep N) → Location V E → List (Location V E)
  | [],loc => [loc]
  | .interval _ :: ops,loc => loc :: positionTrace N reg ops loc
  | .boundary b :: ops,loc => loc :: positionTrace N reg ops (fixedBoundaryLocation N b reg loc)

lemma fixedBoundaryLocation_agrees (N : RootedBinary V E X) (b : BoundaryOperation N)
    (a c : V → Bool) (h : ∀ v ∈ (boundarySite N b).toList, a v = c v) (loc : Location V E) :
    fixedBoundaryLocation N b a loc = fixedBoundaryLocation N b c loc := by
  cases b with
  | exit e => rfl
  | ordinary e he => rfl
  | root => rfl
  | independent H gamma => simp only [fixedBoundaryLocation,h H.hybrid (by simp [boundarySite])]
  | common H => simp only [fixedBoundaryLocation,h H.hybrid (by simp [boundarySite])]

lemma positionTrace_agrees (N : RootedBinary V E X) (a b : V → Bool)
    (ops : List (ProgramStep N)) (h : ∀ v ∈ wordSites N ops, a v = b v) (loc : Location V E) :
    positionTrace N a ops loc = positionTrace N b ops loc := by
  induction ops generalizing loc with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | interval t => simp only [positionTrace,ih h]
    | boundary q =>
      have hh : ∀ v ∈ (boundarySite N q).toList, a v = b v :=
        fun v hv => h v (List.mem_append_left _ hv)
      have ht : ∀ v ∈ wordSites N ops, a v = b v :=
        fun v hv => h v (List.mem_append_right _ hv)
      simp only [positionTrace,fixedBoundaryLocation_agrees N q a b hh,ih ht]

lemma positionTrace_update_unused (N : RootedBinary V E X) (reg : V → Bool)
    (ops : List (ProgramStep N)) (v : V) (hv : v ∉ wordSites N ops) (bit : Bool) (loc : Location V E) :
    positionTrace N (Function.update reg v bit) ops loc = positionTrace N reg ops loc := by
  apply positionTrace_agrees
  intro u hu
  have hne : u ≠ v := by intro he; exact hv (he ▸ hu)
  exact Function.update_of_ne hne _ _

lemma independent_boundary_copy_bit (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval) (s : Code N sample)
    {d : Code N sample} (hd : d ∈ (independentPulseKernel H gamma s).support) (x : Copy) :
    ∃ bit : Bool, ∀ reg : V → Bool, reg H.hybrid = bit →
      copyLocation (state d) x = fixedBoundaryLocation N (.independent H gamma) reg (copyLocation (state s) x) := by
  obtain ⟨coin,hcoin,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  have h := UnifiedLean.Source.SourceBoundaryLocations.actual_pulse_code_location H s coin x
  by_cases hx : copyLocation (state s) x = .node H.hybrid
  · obtain ⟨bit,hbit⟩ := h.1 hx
    refine ⟨bit,fun reg hreg => ?_⟩
    simpa only [fixedBoundaryLocation,ordinaryLocation,hx,hreg,if_pos rfl,ite_true] using hbit
  · refine ⟨false,fun reg hreg => ?_⟩
    simpa only [fixedBoundaryLocation,ordinaryLocation,if_neg hx] using h.2 hx

/-- One supported no-merger trace induces one consistent original-site
register for each copy. The register is a proof witness for that copy's route,
not a shared latent bank imposed on independent roots. -/
theorem routingTrace_copy_selector (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (hops : IndependentWord N ops) (hn : (wordSites N ops).Nodup)
    (s : Code N sample) {states : List (Code N sample)}
    (hstates : states ∈ (routingTrace N ops s).support) (x : Copy) :
    ∃ reg : V → Bool, states.map (fun d => copyLocation (state d) x) =
      positionTrace N reg ops (copyLocation (state s) x) := by
  induction ops generalizing s states with
  | nil =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hstates
    exact ⟨fun _ => false,rfl⟩
  | cons op ops ih =>
    have ht : IndependentWord N ops := fun q hq => hops q (List.mem_cons_of_mem _ hq)
    cases op with
    | interval t =>
      obtain ⟨tail,htail,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hstates
      obtain ⟨reg,hreg⟩ := ih ht hn s htail
      exact ⟨reg,by simpa only [List.map_cons,positionTrace,hreg]⟩
    | boundary b =>
      obtain ⟨tail,htail,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hstates
      obtain ⟨d,hd,hdt⟩ := (PMF.mem_support_bind_iff _ _ _).mp htail
      have hnt : (wordSites N ops).Nodup := (List.nodup_append.mp hn).2.1
      obtain ⟨reg,hreg⟩ := ih ht hnt d hdt
      cases b with
      | common H => exact False.elim (hops _ (List.mem_cons_self ..))
      | independent H gamma =>
        have hsite : H.hybrid ∉ wordSites N ops := (List.nodup_cons.mp hn).1
        obtain ⟨bit,hbit⟩ := independent_boundary_copy_bit N H gamma s hd x
        let reg' := Function.update reg H.hybrid bit
        refine ⟨reg',?_⟩
        simp only [List.map_cons,positionTrace]
        rw [← hbit reg' (Function.update_self ..),positionTrace_update_unused N reg ops H.hybrid hsite bit]
        exact congrArg (List.cons (copyLocation (state s) x)) hreg
      | exit e =>
        obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
        refine ⟨reg,?_⟩
        simpa only [List.map_cons,positionTrace,hreg,UnifiedLean.Source.SourceBoundaryLocations.exitCode_copyLocation,
          fixedBoundaryLocation]
      | ordinary e he =>
        obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
        refine ⟨reg,?_⟩
        simpa only [List.map_cons,positionTrace,hreg,UnifiedLean.Source.SourceBoundaryLocations.ordinaryCode_copyLocation,
          fixedBoundaryLocation]
      | root =>
        obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
        refine ⟨reg,?_⟩
        simpa only [List.map_cons,positionTrace,hreg,UnifiedLean.Source.SourceBoundaryLocations.rootCode_copyLocation,
          fixedBoundaryLocation]

open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open GProgram.G7.CalendarFrontierOrder GProgram.G7.OrderedFrontierProduct GProgram.G7.OriginalEdgeGathering

lemma wordSites_append (N : RootedBinary V E X) (a b : List (ProgramStep N)) :
    wordSites N (a ++ b) = wordSites N a ++ wordSites N b := by
  induction a with
  | nil => rfl
  | cons op ops ih => cases op <;> simp only [List.cons_append,wordSites,ih,List.append_assoc]

lemma wordSites_boundary_map (N : RootedBinary V E X) {A : Type*}
    (f : A → BoundaryOperation N) (xs : List A) :
    wordSites N (xs.map (fun a => ProgramStep.boundary (f a))) = xs.filterMap (fun a => boundarySite N (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : boundarySite N (f a) <;>
      simp only [List.map_cons,wordSites,List.filterMap_cons,h,Option.toList,ih,List.nil_append,List.cons_append]

noncomputable def hybridAtomSite (N : RootedBinary V E X) : Atom V E → Option V
  | .exit _ => none
  | .node v => if v = N.root then none else if N.graph.IsHybrid v then some v else none

lemma originalNode_boundarySite (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (v : V) :
    boundarySite N (originalNodeOperation N H gamma common v) = hybridAtomSite N (.node v) := by
  by_cases hr : v = N.root
  · simp only [originalNodeOperation,hybridAtomSite,dif_pos hr,if_pos hr,boundarySite]
  · by_cases hh : N.graph.IsHybrid v
    · have hv := H.original_site (⟨v,hh⟩ : Hybrid N)
      cases hc : common ⟨v,hh⟩ <;>
        simp [originalNodeOperation,hybridAtomSite,hr,hh,hc,boundarySite,hv]
    · simp [originalNodeOperation,hybridAtomSite,hr,hh,boundarySite]

lemma actual_batch_wordSites (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) :
    wordSites N (boundaryOperations N C H gamma common a) =
      (boundaryAtoms N C a).filterMap (hybridAtomSite N) := by
  simp only [boundaryOperations,boundaryAtoms,wordSites_append,wordSites_boundary_map,
    List.filterMap_append,List.filterMap_map,boundarySite,hybridAtomSite]
  congr 1
  apply List.filterMap_congr
  intro v hv
  exact originalNode_boundarySite N H gamma common v

lemma actual_tail_wordSites (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) (dates : List ℝ) :
    wordSites N (calendarTail N C H gamma common a dates) =
      (dates.flatMap (boundaryAtoms N C)).filterMap (hybridAtomSite N) := by
  induction dates generalizing a with
  | nil => rfl
  | cons b dates ih => simp only [calendarTail,wordSites,wordSites_append,actual_batch_wordSites,
      ih,List.flatMap_cons,List.filterMap_append]

lemma actual_calendar_wordSites (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) :
    wordSites N (compiledCalendarProgram N C H gamma common) =
      (calendarAtoms N C).filterMap (hybridAtomSite N) := by
  unfold compiledCalendarProgram calendarAtoms
  cases hd : sortedOriginalDates N C with
  | nil => rfl
  | cons a dates => simp only [wordSites_append,actual_batch_wordSites,actual_tail_wordSites,
      List.flatMap_cons,List.filterMap_append]

/-- Unmodified original calendar schedules each original hybrid once, even
when unrelated vertices have tied dates. The existing atom census is reused. -/
theorem actual_calendar_sites_nodup (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) :
    (wordSites N (compiledCalendarProgram N C H gamma common)).Nodup := by
  rw [actual_calendar_wordSites]
  apply List.Nodup.filterMap _ (calendarAtoms_nodup N C)
  intro a b v ha hb
  have node_of_mem (q : Atom V E) (h : v ∈ hybridAtomSite N q) : q = .node v := by
    cases q with
    | exit e => simp [hybridAtomSite] at h
    | node u =>
      simp only [hybridAtomSite] at h
      split_ifs at h with hr hh
      · simp at h
      · have he : u = v := by simpa using h
        exact congrArg Atom.node he
      · simp at h
  exact (node_of_mem a ha).trans (node_of_mem b hb).symm

/-- Every actual independent literal prefix keeps all interval-bearing copy
positions in one per-copy selector witness. Original banks may differ by copy. -/
theorem actual_independent_prefix_trace_selector (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (sample : Copy → X) (ρ : V → Bool) (past future : List (ProgramStep N))
    (hp : compiledCalendarProgram N C H gamma (fun _ => false) = past ++ future)
    {states : List (Code N sample)}
    (hs : states ∈ (routingTrace N past (initialCode N sample ρ)).support) (x : Copy) :
    ∃ reg : V → Bool, states.map (fun d => copyLocation (state d) x) =
      positionTrace N reg past (.node (N.leaf (sample x))) := by
  have hi := actual_independent_calendar N C H gamma
  have hn := actual_calendar_sites_nodup N C H gamma (fun _ => false)
  rw [hp,independentWord_append] at hi
  rw [hp,wordSites_append] at hn
  obtain ⟨reg,hreg⟩ := routingTrace_copy_selector N past hi.1 (List.nodup_append.mp hn).1 _ hs x
  refine ⟨reg,?_⟩
  simpa only [DotG4.ActualBankFirstMeeting.initial_copy_location] using hreg

noncomputable def singleLocationRate (N : RootedBinary V E X) (r : PositivePairRates E)
    (loc : Location V E) : ℝ := ∑ i : Option E, if loc = originalPlace N i then pairRate r i else 0

lemma singleLocationRate_nonnegative (N : RootedBinary V E X) (r : PositivePairRates E)
    (loc : Location V E) : 0 ≤ singleLocationRate N r loc := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> first | exact (pairRate_pos r i).le | exact le_rfl

/-- On the literal separated three-copy prefix the only possible real pair
is the two A copies. Pending nodes have zero rate in this exact formula. -/
lemma actual_three_separated_rate (N : RootedBinary V E X) {sample : Fin 3 → X}
    (r : PositivePairRates E) (s : Code N sample) (hc : liveCard s = 3)
    (h02 : copyLocation (state s) 0 ≠ copyLocation (state s) 2)
    (h12 : copyLocation (state s) 1 ≠ copyLocation (state s) 2) :
    totalRate N r s =
      if copyLocation (state s) 0 = copyLocation (state s) 1 then
        singleLocationRate N r (copyLocation (state s) 0) else 0 := by
  have hl : (state s).live = Finset.univ := Finset.eq_univ_of_card _ (by simpa only [liveCard,state,decodeSnapshot,Fintype.card_fin] using hc)
  have ha (x : Fin 3) : (state s).ancestor x = x :=
    (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).representative x (by rw [hl]; exact Finset.mem_univ x)
  have hloc (x : Fin 3) : copyLocation (state s) x = (state s).location x := by rw [copyLocation,ha]
  simp only [hloc] at h02 h12 ⊢
  rw [DotG34.ActualPopulationRate.actual_rate_choose_two]
  have hpop (i : Option E) :
      ((populationRoots (state s) (originalPlace N i)).card.choose 2 : ℝ) =
        if (state s).location 0 = originalPlace N i ∧ (state s).location 1 = originalPlace N i then 1 else 0 := by
    have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
    by_cases h0 : (state s).location 0 = originalPlace N i <;>
      by_cases h1 : (state s).location 1 = originalPlace N i <;>
      by_cases h2 : (state s).location 2 = originalPlace N i
    all_goals first
      | exact False.elim (h02 (h0.trans h2.symm))
      | exact False.elim (h12 (h1.trans h2.symm))
      | simp [populationRoots,hl,hu,Finset.filter_insert,Finset.filter_singleton,h0,h1,h2]
  simp_rw [hpop]
  by_cases he : (state s).location 0 = (state s).location 1
  · rw [if_pos he]
    unfold singleLocationRate
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : (state s).location 0 = originalPlace N i <;> simp [← he,hp]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro i hi
    have hn : ¬((state s).location 0 = originalPlace N i ∧ (state s).location 1 = originalPlace N i) :=
      fun h => he (h.1.trans h.2.symm)
    simp only [if_neg hn,mul_zero]

lemma actual_three_separated_rate_le (N : RootedBinary V E X) {sample : Fin 3 → X}
    (r : PositivePairRates E) (s : Code N sample) (hc : liveCard s = 3)
    (h02 : copyLocation (state s) 0 ≠ copyLocation (state s) 2)
    (h12 : copyLocation (state s) 1 ≠ copyLocation (state s) 2) :
    totalRate N r s ≤ singleLocationRate N r (copyLocation (state s) 0) := by
  rw [actual_three_separated_rate N r s hc h02 h12]
  split_ifs
  · exact le_rfl
  · exact singleLocationRate_nonnegative N r _

noncomputable def locationExposure (N : RootedBinary V E X) (r : PositivePairRates E) :
    List (ProgramStep N) → List (Location V E) → ℝ
  | [],_ => 0
  | _,[] => 0
  | .interval t::ops,loc::locs => singleLocationRate N r loc * (t : ℝ) + locationExposure N r ops locs
  | .boundary _::ops,_::locs => locationExposure N r ops locs

open G1ActualJointProgram G1JointSeparatedSourceGeometry GProgram.G5.ActualRoutingSupport

lemma traceExposure_le_copy_clock (N : RootedBinary V E X) {sample : Fin 3 → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (hc : liveCard s = 3) (ha : SeparatedAgenda N r {0,1} {2} ops s)
    {states : List (Code N sample)} (hs : states ∈ (routingTrace N ops s).support) :
    traceExposure N r ops states ≤
      locationExposure N r ops (states.map (fun d => copyLocation (state d) 0)) := by
  induction ops generalizing s states with
  | nil => exact le_rfl
  | cons op ops ih =>
    have h02 := ha.1 0 (by simp) 2 (by simp)
    have h12 := ha.1 1 (by simp) 2 (by simp)
    cases op with
    | interval t =>
      obtain ⟨tail,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      have htail := ha.2 s (GProgram.G5.OriginalProgramSurvival.actual_epoch_self_in_support N r t s)
      exact add_le_add (mul_le_mul_of_nonneg_right (actual_three_separated_rate_le N r s hc h02 h12) t.property)
        (ih s hc htail ht)
    | boundary b =>
      obtain ⟨tail,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      obtain ⟨d,hd,hdt⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      exact ih d ((boundary_live_card N b s d hd).trans hc) (ha.2 d hd) hdt

/-- An actual positive interval where A0 is on a merging population but A1
is elsewhere. This is a concrete trace property to be exhibited at a split. -/
noncomputable def TraceStrictSplit (N : RootedBinary V E X) {sample : Fin 3 → X}
    (r : PositivePairRates E) : List (ProgramStep N) → List (Code N sample) → Prop
  | [],_ => False
  | _,[] => False
  | .interval t :: ops,s::states =>
      (0 < (t : ℝ) ∧ copyLocation (state s) 0 ≠ copyLocation (state s) 1 ∧
        0 < singleLocationRate N r (copyLocation (state s) 0)) ∨ TraceStrictSplit N r ops states
  | .boundary _ :: ops,_::states => TraceStrictSplit N r ops states

lemma traceExposure_lt_copy_clock (N : RootedBinary V E X) {sample : Fin 3 → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (hc : liveCard s = 3) (ha : SeparatedAgenda N r {0,1} {2} ops s)
    {states : List (Code N sample)} (hs : states ∈ (routingTrace N ops s).support)
    (hstrict : TraceStrictSplit N r ops states) :
    traceExposure N r ops states <
      locationExposure N r ops (states.map (fun d => copyLocation (state d) 0)) := by
  induction ops generalizing s states with
  | nil => exact False.elim hstrict
  | cons op ops ih =>
    have h02 := ha.1 0 (by simp) 2 (by simp)
    have h12 := ha.1 1 (by simp) 2 (by simp)
    cases op with
    | interval t =>
      obtain ⟨tail,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      have htail := ha.2 s (GProgram.G5.OriginalProgramSurvival.actual_epoch_self_in_support N r t s)
      rcases hstrict with ⟨htpos,hne,hpos⟩ | hstrict
      · have hr : totalRate N r s = 0 := by rw [actual_three_separated_rate N r s hc h02 h12,if_neg hne]
        have hlt : totalRate N r s * (t : ℝ) < singleLocationRate N r (copyLocation (state s) 0) * (t : ℝ) := by
          rw [hr,zero_mul]
          exact mul_pos hpos htpos
        exact add_lt_add_of_lt_of_le hlt (traceExposure_le_copy_clock N r ops s hc htail ht)
      · exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_right (actual_three_separated_rate_le N r s hc h02 h12) t.property)
          (ih s hc htail ht hstrict)
    | boundary b =>
      obtain ⟨tail,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      obtain ⟨d,hd,hdt⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      exact ih d ((boundary_live_card N b s d hd).trans hc) (ha.2 d hd) hdt hstrict

/-- Erasing only the routing-mode flag is used inside the deterministic
reference fold. It is not an equality of stochastic COMMON/INDEPENDENT laws. -/
def referenceBoundary (N : RootedBinary V E X) : BoundaryOperation N → BoundaryOperation N
  | .independent H _ => .common H
  | b => b

def referenceStep (N : RootedBinary V E X) : ProgramStep N → ProgramStep N
  | .interval t => .interval t
  | .boundary b => .boundary (referenceBoundary N b)

lemma fixedBoundary_reference (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) :
    fixedRegisterBoundary N (referenceBoundary N b) s = fixedRegisterBoundary N b s := by
  cases b <;> rfl

lemma readoutExposure_reference (N : RootedBinary V E X) {sample : Copy → X}
    (rate : Code N sample → ℝ) (ops : List (ProgramStep N)) (s : Code N sample) :
    readoutExposure N rate (ops.map (referenceStep N)) s = readoutExposure N rate ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [List.map_cons,referenceStep,readoutExposure,fixedBoundary_reference,ih]

lemma reference_originalNode (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (v : V) :
    referenceBoundary N (originalNodeOperation N H gamma common v) =
      originalNodeOperation N H gamma (fun _ => true) v := by
  by_cases hr : v = N.root
  · simp [originalNodeOperation,hr,referenceBoundary]
  · by_cases hh : N.graph.IsHybrid v
    · cases hc : common ⟨v,hh⟩ <;> simp [originalNodeOperation,hr,hh,hc,referenceBoundary]
    · simp [originalNodeOperation,hr,hh,referenceBoundary]

lemma reference_batch (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (a : ℝ) :
    (boundaryOperations N C H gamma common a).map (referenceStep N) =
      boundaryOperations N C H gamma (fun _ => true) a := by
  simp only [boundaryOperations,List.map_append,List.map_map,Function.comp_def]
  apply congrArg₂ List.append
  · rfl
  · apply List.map_congr_left
    intro v hv
    change ProgramStep.boundary (referenceBoundary N (originalNodeOperation N H gamma common v)) = _
    rw [reference_originalNode]

lemma reference_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (a : ℝ) (dates : List ℝ) :
    (calendarTail N C H gamma common a dates).map (referenceStep N) =
      calendarTail N C H gamma (fun _ => true) a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b dates ih => simp only [calendarTail,List.map_cons,List.map_append,
      referenceStep,reference_batch,ih]

lemma reference_calendar (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    (compiledCalendarProgram N C H gamma common).map (referenceStep N) =
      compiledCalendarProgram N C H gamma (fun _ => true) := by
  unfold compiledCalendarProgram
  cases sortedOriginalDates N C with
  | nil => rfl
  | cons a dates => simp only [List.map_append,reference_batch,reference_tail]

lemma readoutExposure_calendar_mode (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (rate : Code N sample → ℝ) (s : Code N sample) :
    readoutExposure N rate (compiledCalendarProgram N C H gamma common) s =
      readoutExposure N rate (compiledCalendarProgram N C H gamma (fun _ => true)) s := by
  rw [← reference_calendar N C H gamma common,readoutExposure_reference]

lemma locationExposure_positionTrace (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (reg : V → Bool)
    (hreg : (state s).register = reg) (x : Copy) :
    locationExposure N r ops (positionTrace N reg ops (copyLocation (state s) x)) =
      readoutExposure N (fun d => singleLocationRate N r (copyLocation (state d) x)) ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | interval t => simp only [positionTrace,locationExposure,readoutExposure,ih s hreg]
    | boundary b =>
      simp only [positionTrace,locationExposure,readoutExposure]
      have hl := fixedRegisterBoundary_copyLocation N b s x
      rw [hreg] at hl
      rw [← hl]
      exact ih _ ((fixedRegisterBoundary_register N b s).trans hreg)

lemma boundarySite_isHybrid (N : RootedBinary V E X) (b : BoundaryOperation N)
    {v : V} (hv : v ∈ (boundarySite N b).toList) : N.graph.IsHybrid v := by
  cases b with
  | exit e => simp [boundarySite] at hv
  | ordinary e he => simp [boundarySite] at hv
  | root => simp [boundarySite] at hv
  | common H => have he : v = H.hybrid := by simpa [boundarySite] using hv
                simpa only [he] using H.isHybrid
  | independent H gamma => have he : v = H.hybrid := by simpa [boundarySite] using hv
                           simpa only [he] using H.isHybrid

lemma wordSites_isHybrid (N : RootedBinary V E X) (ops : List (ProgramStep N))
    {v : V} (hv : v ∈ wordSites N ops) : N.graph.IsHybrid v := by
  induction ops with
  | nil => simp [wordSites] at hv
  | cons op ops ih =>
    cases op with
    | interval t => exact ih hv
    | boundary b =>
      rcases List.mem_append.mp hv with hh | ht
      · exact boundarySite_isHybrid N b hh
      · exact ih ht

/-- The per-copy selector is converted to an actual original-site bank only
on the sites that the deterministic word reads. No probability law is assigned
to this existential bank witness. -/
lemma positionTrace_original_bank (N : RootedBinary V E X) (reg : V → Bool)
    (ops : List (ProgramStep N)) (loc : Location V E) :
    positionTrace N reg ops loc =
      positionTrace N (originalRegister N (fun h => reg h.1)) ops loc := by
  apply positionTrace_agrees
  intro v hv
  simp only [originalRegister,dif_pos (wordSites_isHybrid N ops hv)]

theorem actual_independent_prefix_trace_bank (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (sample : Copy → X) (ρ : V → Bool) (past future : List (ProgramStep N))
    (hp : compiledCalendarProgram N C H gamma (fun _ => false) = past ++ future)
    {states : List (Code N sample)}
    (hs : states ∈ (routingTrace N past (initialCode N sample ρ)).support) (x : Copy) :
    ∃ coin : Hybrid N → Bool, states.map (fun d => copyLocation (state d) x) =
      positionTrace N (originalRegister N coin) past (.node (N.leaf (sample x))) := by
  obtain ⟨reg,hr⟩ := actual_independent_prefix_trace_selector N C H gamma sample ρ past future hp hs x
  exact ⟨fun h => reg h.1, hr.trans (positionTrace_original_bank N reg past _)⟩

lemma readoutExposure_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (rate : Code N sample → ℝ) (hr : ∀ s, 0 ≤ rate s)
    (ops : List (ProgramStep N)) (s : Code N sample) : 0 ≤ readoutExposure N rate ops s := by
  induction ops generalizing s with
  | nil => exact le_rfl
  | cons op ops ih =>
    cases op with
    | interval t => exact add_nonneg (mul_nonneg (hr s) t.2) (ih s)
    | boundary b => exact ih _

lemma readoutExposure_prefix_le (N : RootedBinary V E X) {sample : Copy → X}
    (rate : Code N sample → ℝ) (hr : ∀ s, 0 ≤ rate s)
    (past future : List (ProgramStep N)) (s : Code N sample) :
    readoutExposure N rate past s ≤ readoutExposure N rate (past ++ future) s := by
  rw [readoutExposure_append]
  exact le_add_of_nonneg_right (readoutExposure_nonnegative N rate hr _ _)

open GProgram.G4.ActualCommonSelectorSupport G1InitializedFrontierPrefix
open G4LiteralLastChildExitCutDraft DotG4.ActualBelowMeetingSupport

lemma separatedRate_nonnegative (N : RootedBinary V E X) (r : PositivePairRates E)
    {sample : Bool → X} (s : Code N sample) : 0 ≤ separatedRate N r s := by
  unfold separatedRate
  split_ifs
  · exact le_rfl
  · exact singleLocationRate_nonnegative N r _

lemma separated_agenda_single_clock (N : RootedBinary V E X) (r : PositivePairRates E)
    {sample : Bool → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (ho : CommonOnlyWord N ops) (ha : SeparatedAgenda N r {true} {false} ops s) :
    readoutExposure N (fun d => singleLocationRate N r (copyLocation (state d) true)) ops s =
      readoutExposure N (separatedRate N r) ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have hsep := ha.1 true (by simp) false (by simp)
    cases op with
    | interval t =>
      have hs := GProgram.G5.OriginalProgramSurvival.actual_epoch_self_in_support N r t s
      have ht := ha.2 s hs
      simp only [readoutExposure,separatedRate,if_neg hsep]
      exact congrArg (fun z => singleLocationRate N r (copyLocation (state s) true) * (t : ℝ) + z)
        (ih s ho ht)
    | boundary b =>
      have hs : fixedRegisterBoundary N b s ∈ (boundaryKernel N b s).support := by
        rw [DotG4.WeightedOrdinaryTreeLaw.common_boundary_pure N b ho.1 s]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      exact ih _ ho.2 (ha.2 _ hs)

lemma reference_stopBeforeTail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (stop a : ℝ) (dates : List ℝ) :
    (stopBeforeTail N C H gamma common stop a dates).map (referenceStep N) =
      stopBeforeTail N C H gamma (fun _ => true) stop a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
    by_cases hb : b = stop
    · simp only [stopBeforeTail,if_pos hb,List.map_cons,List.map_nil,referenceStep]
    · simp only [stopBeforeTail,if_neg hb,List.map_cons,List.map_append,referenceStep,
        reference_batch,ih]

lemma reference_beforeBoundaryProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (stop : ℝ) :
    (beforeBoundaryProgram N C H gamma common stop).map (referenceStep N) =
      beforeBoundaryProgram N C H gamma (fun _ => true) stop := by
  unfold beforeBoundaryProgram
  cases sortedOriginalDates N C with
  | nil => rfl
  | cons a dates =>
    by_cases ha : a = stop
    · simp only [if_pos ha,List.map_nil]
    · simp only [if_neg ha,List.map_append,reference_batch,reference_stopBeforeTail]

lemma reference_literalPrefix (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (ei ej : E) :
    (literalPrefix N C H gamma common v ei ej).map (referenceStep N) =
      literalPrefix N C H gamma (fun _ => true) v ei ej := by
  simp only [literalPrefix,List.map_append,reference_beforeBoundaryProgram,List.map_map]
  rfl

/-- The one-copy clock before the all-path meeting is bounded by the SAME
bank's full directed path clock. The nonnegative suffix is retained rather
than identifying the literal cut with a separately indexed first meeting. -/
lemma literal_single_clock_le_selected_path (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (coin : Hybrid N → Bool) :
    locationExposure N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (positionTrace N (originalRegister N coin)
        (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej) (.node (N.leaf i))) ≤
      selectedDirectedExposure N C H r coin i j := by
  let z := initialCode N (pairSample i j) (originalRegister N coin)
  have hz : copyLocation (state z) true = .node (N.leaf i) := by
    exact DotG4.ActualBankFirstMeeting.initial_copy_location N (pairSample i j) _ true
  rw [← hz,locationExposure_positionTrace N r _ z _ (by rfl) true]
  rw [← readoutExposure_reference N _ _ z,reference_literalPrefix]
  have cut := literal_calendar_cut N C H (originalGamma p) (fun _ => true) v ei ej
  have hw := actual_common_compiled_word_only N C H (originalGamma p)
  rw [cut,commonOnlyWord_append] at hw
  have ha := actual_initialized_literal_agenda N C H (originalGamma p) (fun _ => true)
    (pairSample i j) (originalRegister N coin) r hg {true} {false}
    (by intro x hx; rcases Finset.mem_singleton.mp hx with rfl; rfl)
    (by intro x hx; rcases Finset.mem_singleton.mp hx with rfl; rfl)
  rw [separated_agenda_single_clock N r _ z hw.1 ha]
  calc
    _ ≤ readoutExposure N (separatedRate N r)
        (compiledCalendarProgram N C H (originalGamma p) (fun _ => true)) z := by
      rw [cut]
      exact readoutExposure_prefix_le N _ (separatedRate_nonnegative N r) _ _ z
    _ = bankExclusiveExposure N C H (originalGamma p) r coin i j :=
      (bankExclusiveExposure_eq_whole_separated_clock N C H (originalGamma p) r coin i j).symm
    _ = selectedDirectedExposure N C H r coin i j := actual_bank_cut_eq_selected_path N C H p r coin i j

/-- Every supported actual INDEPENDENT no-loss trace is bounded by the
calibrated directed COMMON exposure. The existential selector is used only
pointwise; the expectation remains the actual routingTrace law. -/
theorem actual_independent_trace_hazard_le (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (sample : Fin 3 → X) (h0 : sample 0 = i) (h1 : sample 1 = i) (h2 : sample 2 = j)
    (ρ : V → Bool) (base : Hybrid N → Bool)
    (hcal : 18 * combProbability N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3)
    {states : List (Code N sample)}
    (hs : states ∈ (routingTrace N (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (initialCode N sample ρ)).support) :
    traceExposure N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej) states ≤
      selectedDirectedExposure N C H r base i j := by
  let ops := literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej
  have ha := actual_initialized_literal_agenda N C H (originalGamma p) (fun _ => false)
    sample ρ r hg {0,1} {2}
    (by intro x hx; rcases (by simpa using hx : x = 0 ∨ x = 1) with rfl | rfl <;> assumption)
    (by intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact h2)
  have hc : liveCard (initialCode N sample ρ) = 3 := by
    change (Finset.univ : Finset (Fin 3)).card = 3
    simp
  obtain ⟨coin,hcoin⟩ := actual_independent_prefix_trace_bank N C H (originalGamma p) sample ρ
    ops (literalSuffix N C H (originalGamma p) (fun _ => false) v ei ej)
    (literal_calendar_cut N C H (originalGamma p) (fun _ => false) v ei ej) hs 0
  rw [h0] at hcoin
  calc
    _ ≤ locationExposure N r ops (states.map (fun d => copyLocation (state d) 0)) :=
      traceExposure_le_copy_clock N r ops _ hc ha hs
    _ = locationExposure N r ops (positionTrace N (originalRegister N coin) ops (.node (N.leaf i))) :=
      congrArg (locationExposure N r ops) hcoin
    _ ≤ selectedDirectedExposure N C H r coin i j := literal_single_clock_le_selected_path N C H p r hg coin
    _ = selectedDirectedExposure N C H r base i j :=
      actual_calibration_selected_path_constant N C H p r i j hcal coin base

/-- A genuine positive-interval split gives a strict calibrated deficit. -/
theorem actual_independent_trace_hazard_lt (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (sample : Fin 3 → X) (h0 : sample 0 = i) (h1 : sample 1 = i) (h2 : sample 2 = j)
    (ρ : V → Bool) (base : Hybrid N → Bool)
    (hcal : 18 * combProbability N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3)
    {states : List (Code N sample)}
    (hs : states ∈ (routingTrace N (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (initialCode N sample ρ)).support)
    (hstrict : TraceStrictSplit N r
      (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej) states) :
    traceExposure N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej) states <
      selectedDirectedExposure N C H r base i j := by
  let ops := literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej
  have ha := actual_initialized_literal_agenda N C H (originalGamma p) (fun _ => false)
    sample ρ r hg {0,1} {2}
    (by intro x hx; rcases (by simpa using hx : x = 0 ∨ x = 1) with rfl | rfl <;> assumption)
    (by intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact h2)
  have hc : liveCard (initialCode N sample ρ) = 3 := by
    change (Finset.univ : Finset (Fin 3)).card = 3
    simp
  obtain ⟨coin,hcoin⟩ := actual_independent_prefix_trace_bank N C H (originalGamma p) sample ρ
    ops (literalSuffix N C H (originalGamma p) (fun _ => false) v ei ej)
    (literal_calendar_cut N C H (originalGamma p) (fun _ => false) v ei ej) hs 0
  rw [h0] at hcoin
  calc
    _ < locationExposure N r ops (states.map (fun d => copyLocation (state d) 0)) :=
      traceExposure_lt_copy_clock N r ops _ hc ha hs hstrict
    _ = locationExposure N r ops (positionTrace N (originalRegister N coin) ops (.node (N.leaf i))) :=
      congrArg (locationExposure N r ops) hcoin
    _ ≤ selectedDirectedExposure N C H r coin i j := literal_single_clock_le_selected_path N C H p r hg coin
    _ = selectedDirectedExposure N C H r base i j :=
      actual_calibration_selected_path_constant N C H p r i j hcal coin base

open GProgram.G5.StrictBoundaryRoutes

/-- A deterministic choice of legal independent current-owner assignments.
Its supporting probability is derived from the original strict parameters. -/
noncomputable def prescribedBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (b : BoundaryOperation N) (s : Code N sample) : Code N sample :=
  match b with
  | .independent H _ => pulseCode H s (fun owner => reg owner.1 H.hybrid)
  | _ => fixedRegisterBoundary N b s

noncomputable def prescribedTrace (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) : List (ProgramStep N) → Code N sample → List (Code N sample)
  | [],s => [s]
  | .interval _ :: ops,s => s :: prescribedTrace N reg ops s
  | .boundary b :: ops,s => s :: prescribedTrace N reg ops (prescribedBoundary N reg b s)

lemma prescribedBoundary_support (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (b : BoundaryOperation N) (hb : StrictBoundary N b) (s : Code N sample) :
    prescribedBoundary N reg b s ∈ (boundaryKernel N b s).support := by
  apply (actual_boundary_support_iff_legal N b hb s _).mpr
  cases b <;> simp only [prescribedBoundary,fixedRegisterBoundary,LegalBoundaryRoute]
  exact ⟨_,rfl⟩

lemma prescribedTrace_support (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (ops : List (ProgramStep N)) (ho : StrictWord N ops) (s : Code N sample) :
    prescribedTrace N reg ops s ∈ (routingTrace N ops s).support := by
  induction ops generalizing s with
  | nil => exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | cons op ops ih =>
    cases op with
    | interval t =>
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_,ih ho s,rfl⟩
    | boundary b =>
      apply (PMF.mem_support_map_iff _ _ _).mpr
      refine ⟨_,?_,rfl⟩
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      exact ⟨_,prescribedBoundary_support N reg b ho.1 s,ih ho.2 _⟩

lemma prescribedBoundary_full_card (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (b : BoundaryOperation N) (hb : StrictBoundary N b) (s : Code N sample)
    (hs : liveCard s = Fintype.card Copy) :
    liveCard (prescribedBoundary N reg b s) = Fintype.card Copy := by
  exact (boundary_live_card N b s _ (prescribedBoundary_support N reg b hb s)).trans hs

lemma prescribedBoundary_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (b : BoundaryOperation N) (hb : IndependentBoundary N b)
    (s : Code N sample) (hs : liveCard s = Fintype.card Copy) (x : Copy) :
    copyLocation (state (prescribedBoundary N reg b s)) x =
      fixedBoundaryLocation N b (reg x) (copyLocation (state s) x) := by
  cases b with
  | exit e => exact fixedRegisterBoundary_copyLocation N (.exit e) s x
  | ordinary e he => exact fixedRegisterBoundary_copyLocation N (.ordinary e he) s x
  | root => exact fixedRegisterBoundary_copyLocation N .root s x
  | common H => exact False.elim hb
  | independent H gamma =>
    have hl : (state s).live = Finset.univ := Finset.eq_univ_of_card _ (by simpa only [liveCard,state,decodeSnapshot] using hs)
    have ha : (state s).ancestor x = x := (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).representative x (by rw [hl]; exact Finset.mem_univ x)
    change copyLocation (state (pulseCode H s (fun owner => reg owner.1 H.hybrid))) x = _
    rw [show copyLocation (state (pulseCode H s (fun owner => reg owner.1 H.hybrid))) x =
        copyLocation (pulse H (state s) (fun owner => reg owner.1 H.hybrid)) x from
      decode_encode_copyLocation N.root _ (pulse_source_valid H sample _ s.property _).forest x]
    by_cases hx : copyLocation (state s) x = .node H.hybrid
    · let owner : AtNode (state s) H.hybrid :=
        ⟨(state s).ancestor x,⟨(show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest).ancestor_live x,hx⟩⟩
      have he := pulse_routes_current_ancestor H (state s) (fun owner => reg owner.1 H.hybrid) owner
      change (pulse H (state s) (fun owner => reg owner.1 H.hybrid)).location ((state s).ancestor x) = _
      simpa only [owner,ha,fixedBoundaryLocation,ordinaryLocation,hx,if_pos rfl,ite_true] using he
    · have hn : ¬((state s).ancestor x ∈ (state s).live ∧
          (state s).location ((state s).ancestor x) = .node H.hybrid) := fun h => hx h.2
      simp only [copyLocation] at hx
      simp only [copyLocation,pulse,transport,dif_neg hn,fixedBoundaryLocation,ordinaryLocation,if_neg hx]

lemma prescribedTrace_copy_positions (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (ops : List (ProgramStep N)) (ho : IndependentWord N ops)
    (hst : StrictWord N ops) (s : Code N sample) (hs : liveCard s = Fintype.card Copy) (x : Copy) :
    (prescribedTrace N reg ops s).map (fun d => copyLocation (state d) x) =
      positionTrace N (reg x) ops (copyLocation (state s) x) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have ht : IndependentWord N ops := fun q hq => ho q (List.mem_cons_of_mem _ hq)
    cases op with
    | interval t =>
      simpa only [prescribedTrace,List.map_cons,positionTrace] using
        (congrArg (List.cons (copyLocation (state s) x)) (ih ht hst s hs))
    | boundary b =>
      have hb : IndependentBoundary N b := ho (.boundary b) (List.mem_cons_self ..)
      simp only [prescribedTrace,List.map_cons,positionTrace]
      rw [ih ht hst.2 _ (prescribedBoundary_full_card N reg b hst.1 s hs),
        prescribedBoundary_copyLocation N reg b hb s hs x]

noncomputable def prescribedEnd (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) : List (ProgramStep N) → Code N sample → Code N sample
  | [],s => s
  | .interval _ :: ops,s => prescribedEnd N reg ops s
  | .boundary b :: ops,s => prescribedEnd N reg ops (prescribedBoundary N reg b s)

lemma prescribedTrace_ne_nil (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (ops : List (ProgramStep N)) (s : Code N sample) :
    prescribedTrace N reg ops s ≠ [] := by
  cases ops with
  | nil => simp [prescribedTrace]
  | cons op ops => cases op <;> intro h <;> cases h

lemma prescribedTrace_last (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (ops : List (ProgramStep N)) (s : Code N sample) :
    (prescribedTrace N reg ops s).getLast? = some (prescribedEnd N reg ops s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [prescribedTrace,prescribedEnd,
      List.getLast?_cons_of_ne_nil (prescribedTrace_ne_nil N reg ops _),ih]

lemma positionTrace_ne_nil (N : RootedBinary V E X) (reg : V → Bool)
    (ops : List (ProgramStep N)) (loc : Location V E) : positionTrace N reg ops loc ≠ [] := by
  cases ops with
  | nil => simp [positionTrace]
  | cons op ops => cases op <;> intro h <;> cases h

lemma positionTrace_last (N : RootedBinary V E X) {sample : Copy → X}
    (reg : V → Bool) (ops : List (ProgramStep N)) (s : Code N sample)
    (hs : (state s).register = reg) (x : Copy) :
    (positionTrace N reg ops (copyLocation (state s) x)).getLast? =
      some (copyLocation (state (fixedRegisterPrefix N ops s)) x) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | interval t =>
      simpa only [positionTrace,fixedRegisterPrefix,
        List.getLast?_cons_of_ne_nil (positionTrace_ne_nil N reg ops _)] using ih s hs
    | boundary b =>
      have hl := fixedRegisterBoundary_copyLocation N b s x
      rw [hs] at hl
      have ht := ih (fixedRegisterBoundary N b s) ((fixedRegisterBoundary_register N b s).trans hs)
      rw [hl] at ht
      simpa only [positionTrace,fixedRegisterPrefix,
        List.getLast?_cons_of_ne_nil (positionTrace_ne_nil N reg ops _)] using ht

/-- Per-copy prescribed routing agrees with its own deterministic original
bank at the end of every literal prefix, as well as at all intermediate steps. -/
lemma prescribedEnd_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (reg : Copy → V → Bool) (ops : List (ProgramStep N)) (ho : IndependentWord N ops)
    (hst : StrictWord N ops) (s : Code N sample) (hs : liveCard s = Fintype.card Copy)
    (x : Copy) {sample' : Copy → X} (z : Code N sample')
    (hz : (state z).register = reg x)
    (hl : copyLocation (state s) x = copyLocation (state z) x) :
    copyLocation (state (prescribedEnd N reg ops s)) x =
      copyLocation (state (fixedRegisterPrefix N ops z)) x := by
  have he := congrArg List.getLast? (prescribedTrace_copy_positions N reg ops ho hst s hs x)
  rw [List.getLast?_map,prescribedTrace_last,Option.map_some,hl,positionTrace_last N _ ops z hz x] at he
  exact Option.some.inj he

lemma prescribedTrace_strictSplit_of_prefix (N : RootedBinary V E X) {sample : Fin 3 → X}
    (r : PositivePairRates E) (reg : Fin 3 → V → Bool) (pre post : List (ProgramStep N))
    (t : ℝ≥0) (s : Code N sample) (ht : 0 < (t : ℝ))
    (he : copyLocation (state (prescribedEnd N reg pre s)) 0 ≠
      copyLocation (state (prescribedEnd N reg pre s)) 1)
    (hr : 0 < singleLocationRate N r (copyLocation (state (prescribedEnd N reg pre s)) 0)) :
    TraceStrictSplit N r (pre ++ .interval t :: post)
      (prescribedTrace N reg (pre ++ .interval t :: post) s) := by
  induction pre generalizing s with
  | nil => exact Or.inl ⟨ht,he,hr⟩
  | cons op pre ih =>
    cases op with
    | interval u => exact Or.inr (ih s he hr)
    | boundary b => exact ih _ he hr

lemma positiveExpectation_const {A : Type*} (p : PMF A) (c : ℝ≥0∞) :
    positiveExpectation p (fun _ => c) = c := by
  rw [positiveExpectation,ENNReal.tsum_mul_right,p.tsum_coe,one_mul]

lemma positiveExpectation_mono_support {A : Type*} (p : PMF A) (f g : A → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a ≤ g a) : positiveExpectation p f ≤ positiveExpectation p g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) (p a)
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff,not_not] using ha
    simp only [hz,zero_mul,le_refl]

lemma positiveExpectation_strict_support {A : Type*} (p : PMF A) (f g : A → ℝ≥0∞)
    (hf : positiveExpectation p f ≠ ⊤) (h : ∀ a ∈ p.support, f a ≤ g a)
    {a : A} (ha : a ∈ p.support) (hlt : f a < g a) :
    positiveExpectation p f < positiveExpectation p g := by
  apply ENNReal.tsum_lt_tsum (i := a) hf
  · intro b
    by_cases hb : b ∈ p.support
    · exact mul_le_mul_right (h b hb) (p b)
    · have hz : p b = 0 := by simpa only [PMF.mem_support_iff,not_not] using hb
      simp only [hz,zero_mul,le_refl]
  · simpa only [mul_comm] using ENNReal.mul_lt_mul_left ((PMF.mem_support_iff _ _).mp ha) (p.apply_ne_top a) hlt

lemma exponential_trace_expectation_le {A : Type*} (p : PMF A) (cost : A → ℝ) (E : ℝ)
    (h : ∀ a ∈ p.support, cost a ≤ E) :
    ENNReal.ofReal (Real.exp (-E)) ≤
      positiveExpectation p (fun a => ENNReal.ofReal (Real.exp (-cost a))) := by
  rw [← positiveExpectation_const p (ENNReal.ofReal (Real.exp (-E)))]
  apply positiveExpectation_mono_support
  intro a ha
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (h a ha)))

lemma exponential_trace_expectation_lt {A : Type*} (p : PMF A) (cost : A → ℝ) (E : ℝ)
    (h : ∀ a ∈ p.support, cost a ≤ E) {a : A} (ha : a ∈ p.support) (hlt : cost a < E) :
    ENNReal.ofReal (Real.exp (-E)) <
      positiveExpectation p (fun a => ENNReal.ofReal (Real.exp (-cost a))) := by
  rw [← positiveExpectation_const p (ENNReal.ofReal (Real.exp (-E)))]
  apply positiveExpectation_strict_support p _ _
  · rw [positiveExpectation_const]
    exact ENNReal.ofReal_ne_top
  · intro b hb
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (h b hb)))
  · exact ha
  · exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
      (Real.exp_lt_exp.mpr (neg_lt_neg hlt))

open GProgram.G5.OriginalEpochChart

lemma fixedRegisterPrefix_reference (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) :
    fixedRegisterPrefix N (ops.map (referenceStep N)) s = fixedRegisterPrefix N ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [List.map_cons,referenceStep,fixedRegisterPrefix,fixedBoundary_reference,ih]

lemma reference_prefixThrough (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (pre : List ℝ) (guard : ℝ) :
    (prefixThrough N C H gamma common pre guard).map (referenceStep N) =
      prefixThrough N C H gamma (fun _ => true) pre guard := by
  unfold prefixThrough
  cases pre ++ [guard] with
  | nil => rfl
  | cons a dates => simp only [List.map_append,reference_batch,reference_tail]

/-- The complete tied-date batch is retained. Each actual current-owner
prescribed route is compared to its own accepted deterministic epoch theorem. -/
lemma prescribed_epoch_selected_edge_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (coins : Copy → Hybrid N → Bool) (ρ : V → Bool)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) (x : Copy) (e : E) :
    let past := prefixThrough N C H (originalGamma p) (fun _ => false) pre guard
    copyLocation (state (prescribedEnd N (fun x => originalRegister N (coins x)) past
      (initialCode N sample ρ))) x = .edge e ↔
      e ∈ (commonRoutes N C H (coins x)).edges (sample x) ∧ C.Active guard e := by
  dsimp only
  let past := prefixThrough N C H (originalGamma p) (fun _ => false) pre guard
  have split := actual_original_epoch_word N C H (originalGamma p) (fun _ => false) pre guard next post hsplit
  have hi := actual_independent_calendar N C H (originalGamma p)
  have ht := actual_compiled_calendar_strict N C H p (fun _ => false)
  rw [split,independentWord_append] at hi
  rw [split,strict_word_append] at ht
  have hc : liveCard (initialCode N sample ρ) = Fintype.card Copy := by
    change (Finset.univ : Finset Copy).card = Fintype.card Copy
    exact Finset.card_univ
  have he := prescribedEnd_copyLocation N (fun y => originalRegister N (coins y)) past hi.1 ht.1
    (initialCode N sample ρ) hc x (initialCode N sample (originalRegister N (coins x)))
    (by rfl) (by simp only [DotG4.ActualBankFirstMeeting.initial_copy_location])
  rw [he,← fixedRegisterPrefix_reference N past,reference_prefixThrough]
  have h := actual_epoch_selected_edge_iff N C sample H p r (coins x) pre post guard next 0 hsplit x e
  simpa only [fixedRegisterPrefix_append,fixedRegisterPrefix] using h

lemma singleLocationRate_edge_positive (N : RootedBinary V E X) (r : PositivePairRates E) (e : E) :
    0 < singleLocationRate N r (.edge e) := by
  have hle : pairRate r (some e) ≤ singleLocationRate N r (.edge e) := by
    unfold singleLocationRate
    have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Option E)))
      (f := fun a => if (Location.edge e : Location V E) = originalPlace N a then pairRate r a else 0)
      (fun a ha => by split_ifs <;> first | exact (pairRate_pos r a).le | exact le_rfl)
      (Finset.mem_univ (some e))
    simpa only [originalPlace,if_pos rfl,ite_true] using hs
  exact (pairRate_pos r (some e)).trans_le hle

lemma stopBeforeTail_through_earlier (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (stop guard a : ℝ) (pre post : List ℝ) (hg : guard ≠ stop)
    (hp : ∀ b ∈ pre, b ≠ stop) :
    stopBeforeTail N C H gamma common stop a (pre ++ guard :: post) =
      calendarTail N C H gamma common a (pre ++ [guard]) ++
        stopBeforeTail N C H gamma common stop guard post := by
  induction pre generalizing a with
  | nil => simp [stopBeforeTail,calendarTail,hg]
  | cons b pre ih =>
    have hb := hp b (by simp)
    have ht := ih b (fun c hc => hp c (by simp [hc]))
    simp only [List.cons_append,stopBeforeTail,if_neg hb,calendarTail,List.append_assoc]
    rw [ht]

lemma beforeBoundaryProgram_after_guard (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (pre post : List ℝ) (guard next stop : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) (hlt : guard < stop) :
    beforeBoundaryProgram N C H gamma common stop =
      prefixThrough N C H gamma common pre guard ++
        stopBeforeTail N C H gamma common stop guard (next :: post) := by
  have ho : (pre ++ guard :: next :: post).Pairwise (· < ·) := by
    rw [← hsplit]; exact UnifiedLean.Source.SourceCalendarTiming.original_dates_strict N C
  have hp : ∀ b ∈ pre, b ≠ stop := fun b hb =>
    ne_of_lt (((List.pairwise_append.mp ho).2.2 b hb guard (by simp)).trans hlt)
  cases pre with
  | nil => simp [beforeBoundaryProgram,prefixThrough,hsplit,ne_of_lt hlt,calendarTail]
  | cons a pre =>
    have ha := hp a (by simp)
    have ht := stopBeforeTail_through_earlier N C H gamma common stop guard a pre (next::post)
      (ne_of_lt hlt) (fun b hb => hp b (by simp [hb]))
    simp only [beforeBoundaryProgram,prefixThrough,hsplit,List.cons_append,if_neg ha]
    rw [ht]
    simp only [List.append_assoc]

/-- A real interval immediately after an earlier complete date batch is
literally contained in the later last-child prefix, including tied operations. -/
lemma literalPrefix_contains_epoch (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (pre post : List ℝ) (guard next : ℝ) (v : V) (ei ej : E)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hlt : guard < C.age v) :
    ∃ tail, literalPrefix N C H gamma common v ei ej =
      prefixThrough N C H gamma common pre guard ++
        .interval (Real.toNNReal (next-guard)) :: tail := by
  rw [literalPrefix,beforeBoundaryProgram_after_guard N C H gamma common pre post guard next (C.age v) hsplit hlt]
  let exits : List (ProgramStep N) := ((G1OriginalCalendarDecomposition.originalExits N C (C.age v)).take (lastChildCutLength N C v ei ej)).map
    (fun e => ProgramStep.boundary (BoundaryOperation.exit e))
  by_cases hn : next = C.age v
  · refine ⟨exits,?_⟩
    simp only [stopBeforeTail,if_pos hn,List.append_assoc,List.singleton_append,exits]
  · refine ⟨(boundaryOperations N C H gamma common next ++
      stopBeforeTail N C H gamma common (C.age v) next post) ++ exits,?_⟩
    simp only [stopBeforeTail,if_neg hn,List.append_assoc,List.cons_append,exits]

/-- Distinct selected original edges at an earlier real epoch produce one
positive actual INDEPENDENT trace. All current-owner choices are drawn from
the strict original pulse kernels; no trace probability is supplied. -/
theorem actual_positive_split_trace (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (sample : Fin 3 → X) (ρ : V → Bool) (coins : Fin 3 → Hybrid N → Bool)
    (pre post : List ℝ) (guard next : ℝ) (v : V) (ei ej e0 e1 : E)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hbefore : guard < C.age v) (hne : e0 ≠ e1)
    (h0 : e0 ∈ (commonRoutes N C H (coins 0)).edges (sample 0) ∧ C.Active guard e0)
    (h1 : e1 ∈ (commonRoutes N C H (coins 1)).edges (sample 1) ∧ C.Active guard e1) :
    ∃ states, states ∈ (routingTrace N
      (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (initialCode N sample ρ)).support ∧
      TraceStrictSplit N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej) states := by
  let regs := fun x => originalRegister N (coins x)
  let ops := literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej
  let s := initialCode N sample ρ
  have hs := actual_compiled_calendar_strict N C H p (fun _ => false)
  rw [literal_calendar_cut N C H (originalGamma p) (fun _ => false) v ei ej,strict_word_append] at hs
  refine ⟨prescribedTrace N regs ops s,prescribedTrace_support N regs ops hs.1 s,?_⟩
  obtain ⟨tail,htail⟩ := literalPrefix_contains_epoch N C H (originalGamma p) (fun _ => false)
    pre post guard next v ei ej hsplit hbefore
  change TraceStrictSplit N r ops (prescribedTrace N regs ops s)
  dsimp only [ops]
  rw [htail]
  have hp0 := (prescribed_epoch_selected_edge_iff N C sample H p r coins ρ pre post guard next hsplit 0 e0).mpr h0
  have hp1 := (prescribed_epoch_selected_edge_iff N C sample H p r coins ρ pre post guard next hsplit 1 e1).mpr h1
  have hd := UnifiedLean.Source.SourceCalendarTiming.actual_consecutive_duration N C hsplit
  apply prescribedTrace_strictSplit_of_prefix
  · rw [hd.2]
    exact sub_pos.mpr hd.1
  · rw [hp0,hp1]
    exact fun he => hne (Location.edge.inj he)
  · rw [hp0]
    exact singleLocationRate_edge_positive N r e0

open G1CutChildPorts

/-- Root-LSA and the original child cut expose every physical hybrid to an
ordered original-taxon pair. This is the existing two-sided bridge theorem. -/
lemma hybrid_exposed_taxa (N : RootedBinary V E X) (hc : CutChild N) (h : Hybrid N) :
    ∃ i j : X, N.graph.DReach h.1 (N.leaf i) ∧ ¬ N.graph.DReach h.1 (N.leaf j) := by
  obtain ⟨e,he,hu⟩ := unique_child_edge N h.property.2
  have hb : N.graph.IsBridge e := hc e (by simpa only [he] using h.property)
  obtain ⟨i,hi⟩ := N.bridge_target_side_contains_taxon hb
  obtain ⟨j,hj⟩ := N.bridge_source_side_contains_taxon e
  refine ⟨i,j,(hybrid_descendant_component N h.property he hb i).mpr hi,?_⟩
  intro hd
  exact N.graph.bridge_sides_disjoint hb hj
    ((hybrid_descendant_component N h.property he hb j).mp hd)

lemma meeting_reaches_right_taxon (N : RootedBinary V E X) {i j : X} {v : V} {ei ej : E}
    (hg : RouteMeetingGeometry N i j v ei ej) : N.graph.DReach v (N.leaf j) := by
  obtain ⟨es,hes⟩ := exists_edgePath_of_directed (N.rooted (N.leaf j))
  exact (Relation.ReflTransGen.single ⟨ej,hg.rightSource,rfl⟩).trans
    (hes.target_reaches_end_of_mem (hg.rightOnEveryPath es hes))

lemma private_ancestor_below_meeting (N : RootedBinary V E X) (C : Calendar N.graph)
    {i j : X} {v h : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (hi : N.graph.DReach h (N.leaf i)) (hj : ¬ N.graph.DReach h (N.leaf j)) :
    C.age h < C.age v := by
  obtain ⟨pre,hpre⟩ := exists_edgePath_of_directed (N.rooted h)
  obtain ⟨post,hpost⟩ := exists_edgePath_of_directed hi
  have hp := hpre.append hpost
  have he := hg.leftOnEveryPath (pre ++ post) hp
  have hvh : N.graph.DReach v h := by
    rcases List.mem_append.mp he with he | he
    · exact (Relation.ReflTransGen.single ⟨ei,hg.leftSource,rfl⟩).trans
        (hpre.target_reaches_end_of_mem he)
    · have hh := GProgram.G5.ComponentCalendar.EdgePath.source_reachable_of_mem hpost he
      rw [hg.leftSource] at hh
      exact False.elim (hj (hh.trans (meeting_reaches_right_taxon N hg)))
  have hne : v ≠ h := by
    intro he
    exact hj (he ▸ meeting_reaches_right_taxon N hg)
  exact proper_descendant_age_lt N C hvh hne

lemma incoming_edge_selected_route (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (e : E) (i : X)
    (hi : N.graph.DReach (N.graph.target e) (N.leaf i)) :
    ∃ coin : Hybrid N → Bool, e ∈ (commonRoutes N C H coin).edges i := by
  obtain ⟨pre,hpre⟩ := exists_edgePath_of_directed (N.rooted (N.graph.source e))
  obtain ⟨post,hpost⟩ := exists_edgePath_of_directed hi
  have hp : EdgePath N.graph N.root (N.leaf i) (pre ++ e :: post) :=
    hpre.append (.cons rfl hpost)
  obtain ⟨coin,hcoin⟩ := compiledRoute_covers_original_path N C H hp
  refine ⟨coin,?_⟩
  change e ∈ compiledRoute N C (coinSelector N H coin) (N.leaf i)
  rw [hcoin]
  exact List.mem_append_right _ (List.mem_cons_self ..)

lemma scheduled_date_has_next (N : RootedBinary V E X) (C : Calendar N.graph)
    (a b : ℝ) (ha : a ∈ sortedOriginalDates N C) (hb : b ∈ sortedOriginalDates N C)
    (hab : a < b) : ∃ pre next post, sortedOriginalDates N C = pre ++ a :: next :: post := by
  obtain ⟨pre,tail,hs⟩ := List.mem_iff_append.mp ha
  cases tail with
  | nil =>
    have ho : (pre ++ [a]).Pairwise (· < ·) := by rw [← hs]; exact UnifiedLean.Source.SourceCalendarTiming.original_dates_strict N C
    rw [hs,List.mem_append,List.mem_singleton] at hb
    rcases hb with hb | hb
    · have hba := (List.pairwise_append.mp ho).2.2 b hb a (by simp)
      exact False.elim (lt_asymm hab hba)
    · subst b
      exact False.elim (lt_irrefl a hab)
  | cons next post => exact ⟨pre,next,post,hs⟩

/-- The two original parent occurrences of an exposed hybrid give the
strict trace witness. Interior inheritance and positive edge durations are
used in actual kernels and the actual calendar, respectively. -/
theorem exposed_hybrid_positive_split (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (h : Hybrid N) (hi : N.graph.DReach h.1 (N.leaf i))
    (hj : ¬ N.graph.DReach h.1 (N.leaf j))
    (sample : Fin 3 → X) (h0 : sample 0 = i) (h1 : sample 1 = i) (ρ : V → Bool) :
    ∃ states, states ∈ (routingTrace N
      (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (initialCode N sample ρ)).support ∧
      TraceStrictSplit N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej) states := by
  let parents := H.parents h
  have ht0 : N.graph.target parents.parent0 = h.1 := parents.target0.trans (H.original_site h)
  have ht1 : N.graph.target parents.parent1 = h.1 := parents.target1.trans (H.original_site h)
  obtain ⟨coin0,hcoin0⟩ := incoming_edge_selected_route N C H parents.parent0 i (by simpa only [ht0] using hi)
  obtain ⟨coin1,hcoin1⟩ := incoming_edge_selected_route N C H parents.parent1 i (by simpa only [ht1] using hi)
  let coins : Fin 3 → Hybrid N → Bool := fun x => if x = 0 then coin0 else coin1
  have hbefore := private_ancestor_below_meeting N C hg hi hj
  obtain ⟨pre,next,post,hsplit⟩ := scheduled_date_has_next N C (C.age h.1) (C.age v)
    (original_date_scheduled N C h.1) (original_date_scheduled N C v) hbefore
  apply actual_positive_split_trace N C H p r sample ρ coins pre post (C.age h.1) next v ei ej
    parents.parent0 parents.parent1 hsplit hbefore parents.different
  · refine ⟨?_,?_⟩
    · simpa only [coins,if_pos rfl,h0] using hcoin0
    · exact ⟨by rw [ht0],by simpa only [ht0] using C.edge_older parents.parent0⟩
  · refine ⟨?_,?_⟩
    · simpa only [coins,show (1 : Fin 3) ≠ 0 from by decide,if_false,h1] using hcoin1
    · exact ⟨by rw [ht1],by simpa only [ht1] using C.edge_older parents.parent1⟩

/-- Strict calibrated no-loss gap at the actual literal meeting prefix.
This is a derived source probability, prior to the completed-cherry readout. -/
theorem exposed_hybrid_actual_no_loss_gap (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (h : Hybrid N) (hi : N.graph.DReach h.1 (N.leaf i))
    (hj : ¬ N.graph.DReach h.1 (N.leaf j))
    (sample : Fin 3 → X) (h0 : sample 0 = i) (h1 : sample 1 = i) (h2 : sample 2 = j)
    (ρ : V → Bool) (base : Hybrid N → Bool)
    (hcal : 18 * combProbability N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3) :
    ENNReal.ofReal (Real.exp (-selectedDirectedExposure N C H r base i j)) <
      ((sourceProgram N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
        (initialCode N sample ρ)).map liveCard) 3 := by
  have hc : liveCard (initialCode N sample ρ) = 3 := by
    change (Finset.univ : Finset (Fin 3)).card = 3
    simp
  have hm := actual_no_loss_trace_mixture N r
    (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej) (initialCode N sample ρ)
  rw [hc] at hm
  rw [hm]
  obtain ⟨states,hs,hstrict⟩ := exposed_hybrid_positive_split N C H p r hg h hi hj sample h0 h1 ρ
  apply exponential_trace_expectation_lt
  · intro states hs
    exact actual_independent_trace_hazard_le N C H p r hg sample h0 h1 h2 ρ base hcal hs
  · exact hs
  · exact actual_independent_trace_hazard_lt N C H p r hg sample h0 h1 h2 ρ base hcal hs hstrict

open DotG34.SpecifiedCombEvent GProgram.G5.SourcePairPersistence
open UnifiedLean.Source.UnrankedGenealogyObservation UnifiedLean.Source.SourceCompletedUnrankedTree

lemma separated_agenda_B_isolated (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (b : Copy) (ops : List (ProgramStep N)) (s : Code N sample)
    (ha : SeparatedAgenda N r (Finset.univ.erase b) {b} ops s)
    (hi : ∀ x, (state s).ancestor x = (state s).ancestor b → x = b)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    ∀ x, (state d).ancestor x = (state d).ancestor b → x = b := by
  induction ops generalizing s with
  | nil =>
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
    exact hi
  | cons op ops ih =>
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply ih z (ha.2 z hz) _ hdz
    intro x hx
    cases op with
    | boundary q =>
      rw [boundary_ancestor_eq N q s z hz] at hx
      exact hi x hx
    | interval t =>
      by_contra hxb
      have he : copyLocation (state z) x = copyLocation (state z) b := congrArg (state z).location hx
      rw [G1NonrootBigonKernel.actual_time_copy_population N r t s hz x,
        G1NonrootBigonKernel.actual_time_copy_population N r t s hz b] at he
      exact ha.1 x (by simp [hxb]) b (by simp) he

lemma program_preserves_bad (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (b x : Copy) (ops : List (ProgramStep N)) (s d : Code N sample)
    (h : codeBad N b x s) (hd : d ∈ (sourceProgram N r ops s).support) : codeBad N b x d := by
  have hstep (s d : Code N sample) (h : codeBad N b x s)
      (hd : d ∈ (sourceStep N r s).support) : codeBad N b x d := by
    obtain ⟨choice,hchoice,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
    cases choice with
    | none => exact h
    | some choice => exact actual_destination_bad N b x s choice h
  have hiter (k : Nat) (s d : Code N sample) (h : codeBad N b x s)
      (hd : d ∈ (sourceIteration N r k s).support) : codeBad N b x d := by
    induction k generalizing s with
    | zero => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact h
    | succ k ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih z (hstep s z h hz) hdz
  induction ops generalizing s with
  | nil => obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd; exact h
  | cons op ops ih =>
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply ih z _ hdz
    cases op with
    | interval t =>
      obtain ⟨k,hk,hzk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
      exact hiter k s z h hzk
    | boundary q =>
      have he := congrFun (GProgram.G5.OriginalProgramSurvival.actual_boundary_selected_genealogy
        N Finset.univ q s z hz) x
      have ht : (state z).genealogy ((state z).ancestor x) = (state s).genealogy ((state s).ancestor x) := by
        simpa only [selectedView,selectedGenealogy,Finset.mem_univ,if_true,full_prune,Option.some.injEq] using he
      simpa only [codeBad,ht] using h

lemma completed_program_bad (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (b x : Copy) (ops : List (ProgramStep N)) (s d : Code N sample)
    (h : codeBad N b x s)
    (hd : d ∈ ((sourceProgram N r ops s).bind (ancestralCompletion N r (Fintype.card Copy))).support) :
    codeBad N b x d := by
  obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_completion_supported_bad N r b x _ z d (program_preserves_bad N r b x ops s z h hz) hdz

lemma threeCherry_zero_no_bad : ¬ badOnUnranked (2 : Fin 3) (threeCherry 0) := by
  change ¬ hasBad (2 : Fin 3) (tripletTree 1 2 0)
  simp [hasBad,tripletTree,Genealogy.leaves]

lemma bad_fullForest_ne_crossed (N : RootedBinary V E X) {sample : Fin 3 → X}
    (s : Code N sample) (x : Fin 3) (h : codeBad N 2 x s) :
    sourceUnrankedForest (state s) Finset.univ ≠ {threeCherry 0} := by
  intro he
  have hm : toUnranked ((state s).genealogy ((state s).ancestor x)) ∈
      sourceUnrankedForest (state s) Finset.univ := by
    rw [fullForest_image]
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩
  rw [he,Finset.mem_singleton] at hm
  apply threeCherry_zero_no_bad
  rw [← hm]
  exact h

lemma completed_crossed_mass_of_bad (N : RootedBinary V E X) {sample : Fin 3 → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (x : Fin 3) (h : codeBad N 2 x s) :
    tripleForestMass N ((sourceProgram N r ops s).bind
      (ancestralCompletion N r (Fintype.card (Fin 3)))) 0 = 0 := by
  unfold tripleForestMass
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro d
  by_cases hd : ((sourceProgram N r ops s).bind (ancestralCompletion N r (Fintype.card (Fin 3)))) d = 0
  · simp only [hd,ite_self]
  · have hb := completed_program_bad N r 2 x ops s d h ((PMF.mem_support_iff _ _).mpr hd)
    exact if_neg (Ne.symm (bad_fullForest_ne_crossed N d x hb))

open DotG4.ActualFirstMeetingEntrance DotG4.ActualFirstMeetingCombMass

/-- The actual independent suffix reader has exactly two rows at the
geometric cut: 1/3 with three unmerged roots and zero after an A-only merger. -/
theorem actual_independent_literal_crossed_reader (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (sample : Fin 3 → X) (h0 : sample 0 = i) (h1 : sample 1 = i) (h2 : sample 2 = j)
    (ρ : V → Bool) (s : Code N sample)
    (hs : s ∈ (sourceProgram N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (initialCode N sample ρ)).support) :
    tripleForestMass N ((sourceProgram N r
      (literalSuffix N C H (originalGamma p) (fun _ => false) v ei ej) s).bind
      (ancestralCompletion N r (Fintype.card (Fin 3)))) 0 =
      if liveCard s = 3 then ENNReal.ofReal ((1 : ℝ)/3) else 0 := by
  have hi : ∀ x ∈ ({0,1} : Finset (Fin 3)), sample x = i := by
    intro x hx
    rcases (by simpa using hx : x = 0 ∨ x = 1) with rfl | rfl <;> assumption
  have hj : ∀ x ∈ ({2} : Finset (Fin 3)), sample x = j := by
    intro x hx
    have he : x = 2 := by simpa using hx
    subst x
    exact h2
  by_cases hc : liveCard s = 3
  · rw [if_pos hc]
    have hl := actual_initialized_literal_colocates N C H (originalGamma p) (fun _ => false)
      sample ρ r hg {0,1} {2} hi hj hs
    have he := actual_independent_cut_triplet_reader N C sample H (originalGamma p) r ρ
      (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (literalSuffix N C H (originalGamma p) (fun _ => false) v ei ej)
      (literal_calendar_cut N C H (originalGamma p) (fun _ => false) v ei ej) s hs
      (by simpa only [Fintype.card_fin] using hc) (.node v)
      (fun x => hl x (by fin_cases x <;> simp)) 0
    rw [← he,ENNReal.ofReal_toReal]
    exact PMF.apply_ne_top _ _
  · rw [if_neg hc]
    have ha := actual_initialized_literal_agenda N C H (originalGamma p) (fun _ => false)
      sample ρ r hg {0,1} {2} hi hj
    have he : (Finset.univ.erase (2 : Fin 3)) = {0,1} := by decide
    have hb := separated_agenda_B_isolated N r (2 : Fin 3) _ (initialCode N sample ρ)
      (by simpa only [he] using ha) (fun x hx => hx) hs
    rcases isolated_flat_or_bad (state s) (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest) 2 hb with hf | ⟨x,hbad⟩
    · have hcard := (flat_iff_full_card (state s) (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest)).mp hf
      exact False.elim (hc (by simpa only [liveCard,state,decodeSnapshot,Fintype.card_fin] using hcard))
    · exact completed_crossed_mass_of_bad N r _ s x hbad

lemma tripleForestMass_bind (N : RootedBinary V E X) {sample : Fin 3 → X}
    (p : PMF (Code N sample)) (q : Code N sample → PMF (Code N sample)) (j : Fin 3) :
    tripleForestMass N (p.bind q) j = positiveExpectation p (fun s => tripleForestMass N (q s) j) := by
  unfold tripleForestMass positiveExpectation
  rw [PMF.map_bind,PMF.bind_apply]

/-- Actual full-calendar INDEPENDENT crossed cherry, before natural-bank
averaging: its probability is one third of the actual prefix no-loss mass. -/
theorem actual_independent_crossed_no_loss_formula (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (sample : Fin 3 → X) (h0 : sample 0 = i) (h1 : sample 1 = i) (h2 : sample 2 = j)
    (ρ : V → Bool) :
    tripleForestMass N ((sourceProgram N r
      (compiledCalendarProgram N C H (originalGamma p) (fun _ => false))
      (initialCode N sample ρ)).bind (ancestralCompletion N r (Fintype.card (Fin 3)))) 0 =
      ((sourceProgram N r (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
        (initialCode N sample ρ)).map liveCard) 3 * ENNReal.ofReal ((1 : ℝ)/3) := by
  rw [literal_calendar_cut N C H (originalGamma p) (fun _ => false) v ei ej,
    UnifiedLean.Source.SourceCalendarPhysicalSupport.sourceProgram_append,PMF.bind_bind,tripleForestMass_bind]
  unfold positiveExpectation
  rw [PMF.map_apply,← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro s
  by_cases hs : (sourceProgram N r
      (literalPrefix N C H (originalGamma p) (fun _ => false) v ei ej)
      (initialCode N sample ρ)) s = 0
  · simp only [hs,zero_mul,ite_self]
  · dsimp only
    rw [actual_independent_literal_crossed_reader N C H p r hg sample h0 h1 h2 ρ s
      ((PMF.mem_support_iff _ _).mpr hs)]
    by_cases hc : liveCard s = 3
    · simp only [hc,if_true]
    · simp only [hc,Ne.symm hc,if_false,mul_zero,zero_mul]

noncomputable def tripleSample (i j : X) : Fin 3 → X := fun x => if x = 2 then j else i

noncomputable def naturalCrossedMass (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Hybrid N → Bool) (i j : X) : ℝ≥0∞ :=
  naturalCompletedUnrankedLaw N C (tripleSample i j) H p common r {threeCherry 0}

noncomputable def independentCrossedProbability (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) : ℝ := (naturalCrossedMass N C H p r (fun _ => false) i j).toReal

lemma naturalCrossedMass_average (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Hybrid N → Bool) (i j : X) :
    naturalCrossedMass N C H p r common i j = positiveExpectation (originalRegisterMeasure N p).toPMF
      (fun coin => tripleForestMass N ((sourceProgram N r
        (compiledCalendarProgram N C H (originalGamma p) common)
        (initialCode N (tripleSample i j) (originalRegister N coin))).bind
        (ancestralCompletion N r (Fintype.card (Fin 3)))) 0) := by
  unfold naturalCrossedMass naturalCompletedUnrankedLaw naturalCompletedLaw naturalCalendarLaw originalRegisterPMF
  rw [PMF.bind_map,PMF.bind_bind,PMF.map_bind,PMF.bind_apply]
  rfl

/-- The exposed original hybrid gives a strict gap in the actual naturally
averaged completed crossed-cherry observation. No arbitrary-readout COMMON
suffix theorem is applied to independent routing. -/
theorem exposed_hybrid_natural_crossed_gap (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (h : Hybrid N) (hi : N.graph.DReach h.1 (N.leaf i))
    (hj : ¬ N.graph.DReach h.1 (N.leaf j))
    (hcal : 18 * combProbability N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3) :
    combProbability N C H p r i j 2 < independentCrossedProbability N C H p r i j := by
  let base : Hybrid N → Bool := fun _ => false
  let E := selectedDirectedExposure N C H r base i j
  let c : ℝ≥0∞ := ENNReal.ofReal ((1 : ℝ)/3)
  have hc0 : c ≠ 0 := by simp [c]
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfixed (coin : Hybrid N → Bool) :
      ENNReal.ofReal (Real.exp (-E)) * c < tripleForestMass N
        ((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => false))
          (initialCode N (tripleSample i j) (originalRegister N coin))).bind
          (ancestralCompletion N r (Fintype.card (Fin 3)))) 0 := by
    rw [actual_independent_crossed_no_loss_formula N C H p r hg (tripleSample i j)
      (by simp [tripleSample]) (by simp [tripleSample]) (by simp [tripleSample])]
    have hx := exposed_hybrid_actual_no_loss_gap N C H p r hg h hi hj (tripleSample i j)
      (by simp [tripleSample]) (by simp [tripleSample]) (by simp [tripleSample])
      (originalRegister N coin) base hcal
    simpa only [mul_comm] using ENNReal.mul_lt_mul_left hc0 hcT hx
  have hmass : ENNReal.ofReal (Real.exp (-E)) * c < naturalCrossedMass N C H p r (fun _ => false) i j := by
    rw [naturalCrossedMass_average,← positiveExpectation_const (originalRegisterMeasure N p).toPMF
      (ENNReal.ofReal (Real.exp (-E)) * c)]
    apply positiveExpectation_strict_support
    · rw [positiveExpectation_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcT
    · intro coin hcoin
      exact (hfixed coin).le
    · exact strict_original_register_coin N p base
    · exact hfixed base
  have hcal' := actual_cubic_observation_forces_constant N C H p r i j hcal base
  rw [realSurvival_eq_selected_path] at hcal'
  have he : Real.exp (-E) * ((1 : ℝ)/3) = combProbability N C H p r i j 2 := by
    dsimp only [E]
    linarith
  have he' : ENNReal.ofReal (Real.exp (-E)) * c =
      ENNReal.ofReal (combProbability N C H p r i j 2) := by
    rw [show c = ENNReal.ofReal ((1 : ℝ)/3) from rfl,← ENNReal.ofReal_mul (Real.exp_pos _).le,he]
  rw [he'] at hmass
  have hreal := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
    (show naturalCrossedMass N C H p r (fun _ => false) i j ≠ ⊤ from PMF.apply_ne_top _ _)).mpr hmass
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ combProbability N C H p r i j 2 from ENNReal.toReal_nonneg),independentCrossedProbability] using hreal

lemma threeCherry_zero_eq_specified : threeCherry 0 =
    toUnranked (comb (2 : Fin 3) [1,0]) := by
  simpa only [threeCherry,comb,List.foldl_cons,List.foldl_nil,tripletTree] using
    triplet_swap (1 : Fin 3) 2 0

/-- Exact one-event comparison across the two named copy carriers. Both
sides use the already proved same-bank specified-comb formula. -/
lemma natural_common_crossed_eq_comb (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E) (i j : X) :
    (naturalCrossedMass N C H p r (fun _ => true) i j).toReal = combProbability N C H p r i j 2 := by
  unfold naturalCrossedMass DotG4.ActualObservableBankCertificate.combProbability
  rw [threeCherry_zero_eq_specified,
    DotG4.ActualLegalPanelComb.enumerated_natural_comb_moment N C H p r i j (tripleSample i j)
      2 (by simp [tripleSample]) (by intro x hx; simp [tripleSample,hx]) [1,0]
      (by intro x; fin_cases x <;> simp) (by decide) (by decide) (by decide),
    actual_natural_completed_comb_moment N C H p r i j 2 (by decide)]
  rfl

def NoHybrids (N : RootedBinary V E X) : Prop := ∀ v, ¬ N.graph.IsHybrid v

def PairedNaturalCalibration (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E) : Prop :=
  ∀ i j, i ≠ j →
    (18 * combProbability N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3) ∧
    independentCrossedProbability N C H p r i j = combProbability N C H p r i j 2

lemma noHybrids_bank_unique (N : RootedBinary V E X) (h : NoHybrids N)
    (a b : Hybrid N → Bool) : a = b := by
  funext v
  exact False.elim (h v.1 v.property)

lemma noHybrids_cubic_calibration (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (h : NoHybrids N) (i j : X) :
    18 * combProbability N C H p r i j 3 = (3 * combProbability N C H p r i j 2)^3 := by
  let base : Hybrid N → Bool := fun _ => false
  have he (coin : Hybrid N → Bool) : realSurvival N C H p r i j coin = realSurvival N C H p r i j base := by
    rw [noHybrids_bank_unique N h coin base]
  have hm := actual_observed_moment N C H p r i j 2 (by decide)
  simp_rw [he] at hm
  rw [← Finset.sum_mul,coinWeight_sum,one_mul] at hm
  have hc : realSurvival N C H p r i j base = 3 * combProbability N C H p r i j 2 := by
    norm_num [observedMoment,combCoefficient,Nat.choose] at hm
    linarith
  apply (actual_cubic_observation_iff_constant N C H p r i j).mpr
  intro coin
  exact (he coin).trans hc

lemma noHybrids_modes_equal (N : RootedBinary V E X) (h : NoHybrids N) :
    (fun _ : Hybrid N => false) = (fun _ : Hybrid N => true) := by
  funext v
  exact False.elim (h v.1 v.property)

/-- Formal source composition of the accepted paired natural ordinary-tree
certificate. All probabilities are actual completed one-comb observations. -/
theorem actual_paired_natural_calibration_iff_noHybrids (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (hc : CutChild N) :
    PairedNaturalCalibration N C H p r ↔ NoHybrids N := by
  constructor
  · intro hcal v hv
    let h : Hybrid N := ⟨v,hv⟩
    obtain ⟨i,j,hi,hj⟩ := hybrid_exposed_taxa N hc h
    have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
    obtain ⟨meeting,ei,ej,hg⟩ := actual_calibrations_route_meeting_geometry N C H p r i j hij
      (hcal i j hij).1 (hcal j i hij.symm).1
    have hgap := exposed_hybrid_natural_crossed_gap N C H p r hg h hi hj (hcal i j hij).1
    rw [(hcal i j hij).2] at hgap
    exact lt_irrefl _ hgap
  · intro h i j hij
    refine ⟨noHybrids_cubic_calibration N C H p r h i j,?_⟩
    unfold independentCrossedProbability
    rw [noHybrids_modes_equal N h]
    exact natural_common_crossed_eq_comb N C H p r i j

open DotG4.WeightedOrdinaryTreeLaw DotG4.WholeProfileDetermination

noncomputable def ordinaryWeight (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) : CladeWeights X :=
  weightedNormalize N C H r (fun _ => false)

lemma ordinaryWeight_laminar [Nonempty X] (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) : LaminarWeights (ordinaryWeight N C H r) :=
  positiveTreeWeights_laminar _ (weightedNormalize_positiveTree N C H r (fun _ => false))

lemma ordinaryWeight_survival (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (h : NoHybrids N) (i j : X) :
    directedSurvival (ordinaryWeight N C H r) i j = 3 * combProbability N C H p r i j 2 := by
  have hc := actual_cubic_observation_forces_constant N C H p r i j
    (noHybrids_cubic_calibration N C H p r h i j) (fun _ => false)
  rw [realSurvival_eq_selected_path] at hc
  simpa only [ordinaryWeight,directedSurvival,weightedNormalize_directedExposure] using hc

lemma ordinary_natural_full_law (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (h : NoHybrids N) (sample : Copy → X) (common : Hybrid N → Bool) :
    naturalCompletedUnrankedLaw N C sample H p common r =
      ordinaryCompletedTreeLaw (ordinaryWeight N C H r) sample := by
  have hm : common = (fun _ => true) := noHybrids_bank_unique N h _ _
  rw [hm]
  unfold naturalCompletedUnrankedLaw naturalCompletedLaw naturalCalendarLaw originalRegisterPMF
  rw [PMF.bind_map,PMF.bind_bind,PMF.map_bind]
  have hk (coin : Hybrid N → Bool) :
      (((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true))
        (initialCode N sample (originalRegister N coin))).bind
        (ancestralCompletion N r (Fintype.card Copy))).map
        (fun d => sourceUnrankedForest (state d) Finset.univ)) =
        ordinaryCompletedTreeLaw (ordinaryWeight N C H r) sample := by
    rw [actual_common_completed_weighted_tree_law,noHybrids_bank_unique N h coin (fun _ => false)]
    rfl
  simpa only [Function.comp_apply,hk] using
    PMF.bind_const (originalRegisterMeasure N p).toPMF (ordinaryCompletedTreeLaw (ordinaryWeight N C H r) sample)

variable {V' E' : Type*} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']

/-- Directed cherry coordinates recover the normalized ordinary weight
function, including zero-resolution aggregation; no physical isomorphism is
assumed or needed for equality of every later full genealogy law. -/
theorem ordinary_weights_eq_of_cherries [Nontrivial X]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (hn : NoHybrids N)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E') (hn' : NoHybrids N')
    (hc : ∀ i j, i ≠ j → combProbability N' C' H' p' r' i j 2 = combProbability N C H p r i j 2) :
    ordinaryWeight N' C' H' r' = ordinaryWeight N C H r := by
  apply directedSurvival_injective_on_laminar _ _ (ordinaryWeight_laminar N' C' H' r')
    (ordinaryWeight_laminar N C H r)
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [directedSurvival,directedExposure_self,neg_zero,Real.exp_zero]
  · rw [ordinaryWeight_survival N' C' H' p' r' hn',ordinaryWeight_survival N C H p r hn,hc i j hij]

/-- End-to-end ordinary-target BOTH response consequence for the three
finite paired scalar families. The legal all-taxon query implementation is
bound separately below; rivals have arbitrary finite original carriers. -/
theorem actual_ordinary_target_paired_all_future [Nontrivial X]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (hn : NoHybrids N)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E') (hcut' : CutChild N')
    (hc : ∀ i j, i ≠ j → combProbability N' C' H' p' r' i j 2 = combProbability N C H p r i j 2)
    (hd : ∀ i j, i ≠ j → combProbability N' C' H' p' r' i j 3 = combProbability N C H p r i j 3)
    (hu : ∀ i j, i ≠ j → independentCrossedProbability N' C' H' p' r' i j =
      independentCrossedProbability N C H p r i j) :
    ∀ (Copy : Type*) [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
      (common : Hybrid N → Bool) (common' : Hybrid N' → Bool),
      naturalCompletedUnrankedLaw N' C' sample H' p' common' r' =
        naturalCompletedUnrankedLaw N C sample H p common r := by
  have ht : PairedNaturalCalibration N C H p r := by
    intro i j hij
    refine ⟨noHybrids_cubic_calibration N C H p r hn i j,?_⟩
    unfold independentCrossedProbability
    rw [noHybrids_modes_equal N hn]
    exact natural_common_crossed_eq_comb N C H p r i j
  have hr : PairedNaturalCalibration N' C' H' p' r' := by
    intro i j hij
    constructor
    · rw [hc i j hij,hd i j hij]
      exact (ht i j hij).1
    · rw [hc i j hij,hu i j hij]
      exact (ht i j hij).2
  have hn' := (actual_paired_natural_calibration_iff_noHybrids N' C' H' p' r' hcut').mp hr
  have hw := ordinary_weights_eq_of_cherries N C H p r hn N' C' H' p' r' hn' hc
  intro Copy _ _ sample common common'
  rw [ordinary_natural_full_law N' C' H' p' r' hn',ordinary_natural_full_law N C H p r hn,hw]

end IndependentRouteTrace

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3824: section EnumeratedCopyTransport"
  (← IO.getStderr).flush
section EnumeratedCopyTransport
open GProgram.SourceForest GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceEmbeddedJumpLaw UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCompletedUnrankedTree UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceUnrankedCopyProjectivity
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3837: noncomputable def renameTree"
  (← IO.getStderr).flush
/-- Pure finite label transport needed to identify an enumerated selected
three-copy carrier. No source-law equality is a field of this construction. -/
noncomputable def renameTree (e : A ≃ B) (t : WellLabelledTree A) : WellLabelledTree B :=
  ⟨mapLabels e t.val,mapLabels_wellLabelled e e.injective t.val t.property⟩

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3840: noncomputable def renameSnapshot"
  (← IO.getStderr).flush
noncomputable def renameSnapshot (e : A ≃ B) (s : Snapshot V E A) : Snapshot V E B where
  live := s.live.image e
  ancestor x := e (s.ancestor (e.symm x))
  genealogy x := (s.genealogy (e.symm x)).map (renameTree e)
  population x := s.population (e.symm x)
  register := s.register

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3847: lemma renameSnapshot_genealogy"
  (← IO.getStderr).flush
lemma renameSnapshot_genealogy (root : V) (e : A ≃ B) (s : Snapshot V E A) (x : B) :
    (decodeSnapshot root (renameSnapshot e s)).genealogy x =
      mapLabels e ((decodeSnapshot root s).genealogy (e.symm x)) := by
  cases h : s.genealogy (e.symm x) with
  | none => simp [decodeSnapshot,renameSnapshot,h,mapLabels]
  | some t => simp [decodeSnapshot,renameSnapshot,h,renameTree]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3854: lemma renameSnapshot_copyLocation"
  (← IO.getStderr).flush
lemma renameSnapshot_copyLocation (root : V) (e : A ≃ B) (s : Snapshot V E A) (x : B) :
    copyLocation (decodeSnapshot root (renameSnapshot e s)) x =
      copyLocation (decodeSnapshot root s) (e.symm x) := by
  simp only [copyLocation,decodeSnapshot,renameSnapshot,Equiv.symm_apply_apply]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3859: lemma renameSnapshot_valid"
  (← IO.getStderr).flush
lemma renameSnapshot_valid (root : V) (e : A ≃ B) (s : Snapshot V E A)
    (hs : Valid (decodeSnapshot root s)) : Valid (decodeSnapshot root (renameSnapshot e s)) := by
  constructor
  · intro x
    exact Finset.mem_image.mpr ⟨_,hs.ancestor_live (e.symm x),rfl⟩
  · intro l hl
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    simpa only [decodeSnapshot,renameSnapshot,Equiv.symm_apply_apply] using
      congrArg e (hs.representative k hk)
  · intro l hl x
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    rw [renameSnapshot_genealogy,mapLabels_leaves]
    simp only [Equiv.symm_apply_apply,decodeSnapshot,renameSnapshot]
    constructor
    · intro hx
      obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
      have ha := (hs.leaf_fiber k hk y).mp hy
      subst x
      simpa only [decodeSnapshot,Equiv.symm_apply_apply] using congrArg e ha
    · intro hx
      have ha : (decodeSnapshot root s).ancestor (e.symm x) = k := e.injective hx
      exact Finset.mem_image.mpr ⟨e.symm x,(hs.leaf_fiber k hk _).mpr ha,e.apply_symm_apply x⟩
  · intro l hl
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
    rw [renameSnapshot_genealogy,Equiv.symm_apply_apply]
    exact mapLabels_wellLabelled e e.injective _ (hs.wellLabelled k hk)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3886: noncomputable def renameCode"
  (← IO.getStderr).flush
noncomputable def renameCode (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : Code N (sample ∘ e.symm) :=
  ⟨renameSnapshot e s.val,⟨renameSnapshot_valid N.root e s.val (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest),by
    intro x
    rw [renameSnapshot_copyLocation]
    exact s.property.original_descendant (e.symm x)⟩⟩

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3893: lemma renameCode_live"
  (← IO.getStderr).flush
lemma renameCode_live (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : (state (renameCode N e s)).live = (state s).live.image e := rfl
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3895: lemma renameCode_ancestor"
  (← IO.getStderr).flush
lemma renameCode_ancestor (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (x : B) :
    (state (renameCode N e s)).ancestor x = e ((state s).ancestor (e.symm x)) := rfl
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3898: lemma renameCode_location"
  (← IO.getStderr).flush
lemma renameCode_location (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (x : B) :
    (state (renameCode N e s)).location x = (state s).location (e.symm x) := rfl
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3901: lemma renameCode_register"
  (← IO.getStderr).flush
lemma renameCode_register (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : (state (renameCode N e s)).register = (state s).register := rfl
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3903: lemma renameCode_genealogy"
  (← IO.getStderr).flush
lemma renameCode_genealogy (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (x : B) :
    (state (renameCode N e s)).genealogy x = mapLabels e ((state s).genealogy (e.symm x)) :=
  renameSnapshot_genealogy N.root e s.val x

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3908: lemma renameCode_population_member"
  (← IO.getStderr).flush
lemma renameCode_population_member (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (place : Location V E) (x : A) :
    e x ∈ populationRoots (state (renameCode N e s)) place ↔ x ∈ populationRoots (state s) place := by
  simp only [populationRoots,Finset.mem_filter,renameCode_live,renameCode_location,Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hx,hplace⟩
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    exact ⟨e.injective he ▸ hy,hplace⟩
  · rintro ⟨hx,hplace⟩
    exact ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,hplace⟩

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3919: lemma renameCode_population_pair"
  (← IO.getStderr).flush
lemma renameCode_population_pair (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (place : Location V E) (a b : A) :
    (e a,e b) ∈ (populationRoots (state (renameCode N e s)) place).offDiag ↔
      (a,b) ∈ (populationRoots (state s) place).offDiag := by
  simp only [Finset.mem_offDiag,renameCode_population_member,e.injective.ne_iff]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3925: noncomputable def renameChoiceEquiv"
  (← IO.getStderr).flush
noncomputable def renameChoiceEquiv (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : Choice N s ≃ Choice N (renameCode N e s) where
  toFun p := ⟨p.1,⟨(e p.2.val.1,e p.2.val.2),(renameCode_population_pair N e s _ _ _).mpr p.2.property⟩⟩
  invFun p := ⟨p.1,⟨(e.symm p.2.val.1,e.symm p.2.val.2),by
    apply (renameCode_population_pair N e s _ _ _).mp
    simpa only [Equiv.apply_symm_apply] using p.2.property⟩⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3934: lemma renameCode_totalRate"
  (← IO.getStderr).flush
lemma renameCode_totalRate (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    totalRate N r (renameCode N e s) = totalRate N r s := by
  unfold totalRate
  exact (Fintype.sum_equiv (renameChoiceEquiv N e s) _ _ (fun p => rfl)).symm

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3940: lemma rename_globalRateBound"
  (← IO.getStderr).flush
lemma rename_globalRateBound (r : PositivePairRates E) (e : A ≃ B) :
    globalRateBound (Copy := B) r = globalRateBound (Copy := A) r := by
  simp only [globalRateBound,Fintype.card_congr e]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3944: lemma renameChoice_mass"
  (← IO.getStderr).flush
lemma renameChoice_mass (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) (q : Option (Choice N s)) :
    choiceMass N r (renameCode N e s) (q.map (renameChoiceEquiv N e s)) = choiceMass N r s q := by
  cases q <;> simp only [Option.map_none,Option.map_some,choiceMass,renameCode_totalRate,
    rename_globalRateBound r e,choiceRate,renameChoiceEquiv] <;> rfl

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3950: lemma renameChoice_pmf"
  (← IO.getStderr).flush
lemma renameChoice_pmf (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (choicePMF N r s).map (Equiv.optionCongr (renameChoiceEquiv N e s)) = choicePMF N r (renameCode N e s) := by
  apply PMF.ext
  intro b
  rw [map_equiv_mass]
  let q := Equiv.optionCongr (renameChoiceEquiv N e s)
  have hm := renameChoice_mass N r e s (q.symm b)
  have he : (q.symm b).map (renameChoiceEquiv N e s) = b := q.apply_symm_apply b
  rw [he] at hm
  simpa only [choicePMF,PMF.ofFintype_apply] using congrArg ENNReal.ofReal hm.symm

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 3962: lemma renameCode_destination"
  (← IO.getStderr).flush
lemma renameCode_destination (N : RootedBinary V E X) {sample : A → X}
    (σ : A ≃ B) (s : Code N sample)
    (q : Option (Choice N s)) :
    renameCode N σ (stepDestination N s q) =
      stepDestination N (renameCode N σ s) (q.map (renameChoiceEquiv N σ s)) := by
  cases q with
  | none => rfl
  | some q =>
    run_tac do
      IO.eprintln "PAIRED_INNER_DIAGNOSTIC step 1"
      (← IO.getStderr).flush
    apply Subtype.ext
    run_tac do
      IO.eprintln "PAIRED_INNER_DIAGNOSTIC step 2"
      (← IO.getStderr).flush
    change renameSnapshot σ (encodeSnapshot (merge (state s) q.2.val.1 q.2.val.2) (actual_choice_merge_valid N s q)) =
      encodeSnapshot (merge (state (renameCode N σ s)) (σ q.2.val.1) (σ q.2.val.2))
        (actual_choice_merge_valid N (renameCode N σ s) (renameChoiceEquiv N σ s q))
    run_tac do
      IO.eprintln "PAIRED_INNER_DIAGNOSTIC step 3"
      (← IO.getStderr).flush
    apply Snapshot.ext
    · run_tac do
        IO.eprintln "PAIRED_INNER_DIAGNOSTIC field 4"
        (← IO.getStderr).flush
      simp only [renameSnapshot,encodeSnapshot,merge,renameCode_live N σ s]
      exact Finset.image_erase σ.injective _ _
    · run_tac do
        IO.eprintln "PAIRED_INNER_DIAGNOSTIC field 5"
        (← IO.getStderr).flush
      funext x
      obtain ⟨y,rfl⟩ := σ.surjective x
      simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
        renameCode_ancestor N σ s,σ.injective.eq_iff]
      split <;> rfl
    · run_tac do
        IO.eprintln "PAIRED_INNER_DIAGNOSTIC field 6"
        (← IO.getStderr).flush
      funext x
      obtain ⟨y,rfl⟩ := σ.surjective x
      have hl : σ y ∈ (state (renameCode N σ s)).live ↔ y ∈ (state s).live := by
        rw [renameCode_live N σ s]
        simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
      by_cases hy : y ∈ (state s).live.erase q.2.val.2
      · have hy' : σ y ∈ (state (renameCode N σ s)).live.erase (σ q.2.val.2) := by
          simpa only [Finset.mem_erase,σ.injective.ne_iff,hl] using hy
        simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
          dif_pos hy,dif_pos hy',Option.map_some]
        apply congrArg some
        run_tac do
          IO.eprintln "PAIRED_INNER_DIAGNOSTIC step 7"
          (← IO.getStderr).flush
        apply Subtype.ext
        by_cases ha : y = q.2.val.1
        · subst y
          simp only [renameTree,if_pos rfl,renameCode_genealogy N σ s,
            Equiv.symm_apply_apply,mapLabels,ite_true]
        · simp only [renameTree,if_neg ha,if_neg (σ.injective.ne_iff.mpr ha),
            renameCode_genealogy N σ s,Equiv.symm_apply_apply]
      · have hy' : σ y ∉ (state (renameCode N σ s)).live.erase (σ q.2.val.2) := by
          simpa only [Finset.mem_erase,σ.injective.ne_iff,hl] using hy
        simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
          dif_neg hy,dif_neg hy',Option.map_none]
    · run_tac do
        IO.eprintln "PAIRED_INNER_DIAGNOSTIC field 8"
        (← IO.getStderr).flush
      funext x
      obtain ⟨y,rfl⟩ := σ.surjective x
      have hl : σ y ∈ (state (renameCode N σ s)).live ↔ y ∈ (state s).live := by
        rw [renameCode_live N σ s]
        simp only [Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
      simp only [renameSnapshot,encodeSnapshot,merge,Equiv.symm_apply_apply,
        Finset.mem_erase,σ.injective.ne_iff,hl,renameCode_location N σ s]
    · run_tac do
        IO.eprintln "PAIRED_INNER_DIAGNOSTIC field 9"
        (← IO.getStderr).flush
      rfl
    run_tac do
      IO.eprintln "PAIRED_INNER_DIAGNOSTIC after final register proof"
      (← IO.getStderr).flush


run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4014: lemma renameCode_sourceStep"
  (← IO.getStderr).flush
lemma renameCode_sourceStep (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (sourceStep N r s).map (renameCode N e) = sourceStep N r (renameCode N e s) := by
  unfold sourceStep
  rw [← renameChoice_pmf N r e s,PMF.map_comp,PMF.map_comp]
  congr 1
  funext q
  exact renameCode_destination N e s q

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4023: lemma renameCode_iteration"
  (← IO.getStderr).flush
lemma renameCode_iteration (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (k : Nat) (s : Code N sample) :
    (sourceIteration N r k s).map (renameCode N e) = sourceIteration N r k (renameCode N e s) := by
  induction k generalizing s with
  | zero => simp only [sourceIteration,PMF.pure_map]
  | succ k ih =>
    rw [sourceIteration,PMF.map_bind,sourceIteration,← renameCode_sourceStep N r e s,PMF.bind_map]
    congr 1
    funext d
    exact ih d

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4034: lemma rename_globalClockRate"
  (← IO.getStderr).flush
lemma rename_globalClockRate (r : PositivePairRates E) (e : A ≃ B) :
    globalClockRate (Copy := B) r = globalClockRate (Copy := A) r := by
  apply Subtype.ext
  exact rename_globalRateBound r e

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4039: lemma renameCode_time"
  (← IO.getStderr).flush
lemma renameCode_time (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (renameCode N e) = sourceTimeKernel N r t (renameCode N e s) := by
  rw [sourceTimeKernel,PMF.map_bind,sourceTimeKernel,rename_globalClockRate r e]
  congr 1
  funext k
  exact renameCode_iteration N r e k s

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4047: lemma renameCode_transport"
  (← IO.getStderr).flush
lemma renameCode_transport (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (f : A → Location V E) (g : B → Location V E)
    (ev : SourceEvent V E A) (ev' : SourceEvent V E B)
    (hv : SourceValid N sample (transport (state s) f ev))
    (hv' : SourceValid N (sample ∘ e.symm) (transport (state (renameCode N e s)) g ev'))
    (hfg : ∀ x, g (e x) = f x) :
    renameCode N e (admittedCode N sample (transport (state s) f ev) hv) =
      admittedCode N (sample ∘ e.symm) (transport (state (renameCode N e s)) g ev') hv' := by
  run_tac do
    IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 1"
    (← IO.getStderr).flush
  apply Subtype.ext
  run_tac do
    IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 2"
    (← IO.getStderr).flush
  change renameSnapshot e (encodeSnapshot (transport (state s) f ev) hv.forest) =
    encodeSnapshot (transport (state (renameCode N e s)) g ev') hv'.forest
  run_tac do
    IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 3"
    (← IO.getStderr).flush
  apply Snapshot.ext
  · run_tac do
      IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 4"
      (← IO.getStderr).flush
    exact (renameCode_live N e s).symm
  · run_tac do
      IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 5"
      (← IO.getStderr).flush
    funext x
    exact (renameCode_ancestor N e s x).symm
  · run_tac do
      IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 6"
      (← IO.getStderr).flush
    funext x
    obtain ⟨y,rfl⟩ := e.surjective x
    have hl : e y ∈ (state (renameCode N e s)).live ↔ y ∈ (state s).live := by
      rw [renameCode_live]
      simp only [Finset.mem_image,e.injective.eq_iff,exists_eq_right]
    by_cases hy : y ∈ (state s).live
    · have hy' := hl.mpr hy
      simp only [renameSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,
        dif_pos hy,dif_pos hy',Option.map_some]
      apply congrArg some
      run_tac do
        IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 7"
        (← IO.getStderr).flush
      apply Subtype.ext
      simpa only [renameTree,Equiv.symm_apply_apply] using (renameCode_genealogy N e s (e y)).symm
    · have hy' : e y ∉ (state (renameCode N e s)).live := mt hl.mp hy
      simp only [renameSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,
        dif_neg hy,dif_neg hy',Option.map_none]
  · run_tac do
      IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 8"
      (← IO.getStderr).flush
    funext x
    obtain ⟨y,rfl⟩ := e.surjective x
    have hl : e y ∈ (state (renameCode N e s)).live ↔ y ∈ (state s).live := by
      rw [renameCode_live]
      simp only [Finset.mem_image,e.injective.eq_iff,exists_eq_right]
    simp only [renameSnapshot,encodeSnapshot,transport,Equiv.symm_apply_apply,hl,hfg]
  · run_tac do
      IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC 9"
      (← IO.getStderr).flush
    rfl
  run_tac do
    IO.eprintln "PAIRED_TRANSPORT_DIAGNOSTIC after final proof"
    (← IO.getStderr).flush


run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4085: lemma renameCode_exit"
  (← IO.getStderr).flush
lemma renameCode_exit (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (edge : E) :
    renameCode N e (exitCode N s edge) = exitCode N (renameCode N e s) edge := by
  apply renameCode_transport N e s
  intro x
  simp only [renameCode_location,Equiv.symm_apply_apply]
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4091: lemma renameCode_ordinary"
  (← IO.getStderr).flush
lemma renameCode_ordinary (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) (edge : E) :
    renameCode N e (ordinaryCode N s edge) = ordinaryCode N (renameCode N e s) edge := by
  apply renameCode_transport N e s
  intro x
  simp only [renameCode_location,Equiv.symm_apply_apply]
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4097: lemma renameCode_root"
  (← IO.getStderr).flush
lemma renameCode_root (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) : renameCode N e (rootCode N s) = rootCode N (renameCode N e s) := by
  apply renameCode_transport N e s
  intro x
  simp only [renameCode_location,Equiv.symm_apply_apply]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4103: lemma renameCode_node_member"
  (← IO.getStderr).flush
lemma renameCode_node_member (N : RootedBinary V E X) {sample : A → X}
    (σ : A ≃ B) (s : Code N sample)
    (v : V) (x : A) :
    (σ x ∈ (state (renameCode N σ s)).live ∧ (state (renameCode N σ s)).location (σ x) = .node v) ↔
      (x ∈ (state s).live ∧ (state s).location x = .node v) := by
  simpa only [populationRoots,Finset.mem_filter] using
    renameCode_population_member N σ s (.node v) x

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4111: noncomputable def renameNodeEquiv"
  (← IO.getStderr).flush
noncomputable def renameNodeEquiv (N : RootedBinary V E X) {sample : A → X}
    (σ : A ≃ B) (s : Code N sample)
    (v : V) : AtNode (state s) v ≃ AtNode (state (renameCode N σ s)) v where
  toFun a := ⟨σ a.val,(renameCode_node_member N σ s v a.val).mpr a.property⟩
  invFun a := ⟨σ.symm a.val,by
    apply (renameCode_node_member N σ s v _).mp
    simpa only [Equiv.apply_symm_apply] using a.property⟩
  left_inv a := by apply Subtype.ext; exact σ.symm_apply_apply a.val
  right_inv a := by apply Subtype.ext; exact σ.apply_symm_apply a.val

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4121: lemma renameCode_pulse"
  (← IO.getStderr).flush
lemma renameCode_pulse (N : RootedBinary V E X) {sample : A → X}
    (H : GProgram.G2.OriginalHybridParents N)
    (σ : A ≃ B) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) :
    renameCode N σ (pulseCode H s coin) =
      pulseCode H (renameCode N σ s)
        (GProgram.G7.CoinReindexing.coinTransport (renameNodeEquiv N σ s H.hybrid) coin) := by
  apply renameCode_transport N σ s
  intro x
  by_cases hx : x ∈ (state s).live ∧ (state s).location x = .node H.hybrid
  · have hx' := (renameCode_node_member N σ s H.hybrid x).mpr hx
    simp only [dif_pos hx,dif_pos hx',GProgram.G7.CoinReindexing.coinTransport]
    congr 2
    apply congrArg coin
    apply Subtype.ext
    exact σ.symm_apply_apply x
  · have hx' := mt (renameCode_node_member N σ s H.hybrid x).mp hx
    rw [dif_neg hx',dif_neg hx]
    simpa only [Equiv.symm_apply_apply] using renameCode_location N σ s (σ x)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4141: lemma renameCode_independentPulse"
  (← IO.getStderr).flush
lemma renameCode_independentPulse (N : RootedBinary V E X) {sample : A → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (σ : A ≃ B) (s : Code N sample) :
    (independentPulseKernel H gamma s).map (renameCode N σ) =
      independentPulseKernel H gamma (renameCode N σ s) := by
  unfold independentPulseKernel
  rw [← GProgram.G7.CoinReindexing.current_coin_pmf (renameNodeEquiv N σ s H.hybrid) gamma,
    PMF.map_comp,PMF.map_comp]
  congr 1
  funext coin
  exact renameCode_pulse N H σ s coin

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4153: lemma renameCode_boundary"
  (← IO.getStderr).flush
lemma renameCode_boundary (N : RootedBinary V E X) {sample : A → X}
    (op : BoundaryOperation N) (hop : IndependentBoundary N op) (e : A ≃ B) (s : Code N sample) :
    (boundaryKernel N op s).map (renameCode N e) = boundaryKernel N op (renameCode N e s) := by
  cases op with
  | exit edge => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (renameCode_exit N e s edge)
  | ordinary edge he => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (renameCode_ordinary N e s edge)
  | root => simpa only [boundaryKernel,PMF.pure_map] using congrArg PMF.pure (renameCode_root N e s)
  | independent H gamma => exact renameCode_independentPulse N H gamma e s
  | common H => exact False.elim hop

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4163: lemma renameCode_program"
  (← IO.getStderr).flush
lemma renameCode_program (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (hops : IndependentWord N ops)
    (e : A ≃ B) (s : Code N sample) :
    (sourceProgram N r ops s).map (renameCode N e) = sourceProgram N r ops (renameCode N e s) := by
  induction ops generalizing s with
  | nil => simp only [sourceProgram,PMF.pure_map]
  | cons op ops ih =>
    have ht : IndependentWord N ops := fun x hx => hops x (List.mem_cons_of_mem _ hx)
    have hh := hops op (List.mem_cons_self ..)
    cases op with
    | interval t =>
      simp only [sourceProgram,PMF.map_bind,sourceProgramStep]
      rw [← renameCode_time N r e t s,PMF.bind_map]
      congr 1
      funext d
      exact ih ht d
    | boundary b =>
      simp only [sourceProgram,PMF.map_bind,sourceProgramStep]
      rw [← renameCode_boundary N b hh e s,PMF.bind_map]
      congr 1
      funext d
      exact ih ht d

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4186: lemma renameChoice_jumpMass"
  (← IO.getStderr).flush
lemma renameChoice_jumpMass (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) (q : Option (Choice N s)) :
    jumpMass N r (renameCode N e s) (q.map (renameChoiceEquiv N e s)) = jumpMass N r s q := by
  cases q <;> simp only [Option.map_none,Option.map_some,jumpMass,renameCode_totalRate,choiceRate,renameChoiceEquiv] <;> rfl

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4191: lemma renameChoice_jumpPMF"
  (← IO.getStderr).flush
lemma renameChoice_jumpPMF (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (sourceJumpChoice N r s).map (Equiv.optionCongr (renameChoiceEquiv N e s)) =
      sourceJumpChoice N r (renameCode N e s) := by
  apply PMF.ext
  intro b
  rw [map_equiv_mass]
  let q := Equiv.optionCongr (renameChoiceEquiv N e s)
  have hm := renameChoice_jumpMass N r e s (q.symm b)
  have he : (q.symm b).map (renameChoiceEquiv N e s) = b := q.apply_symm_apply b
  rw [he] at hm
  simpa only [sourceJumpChoice,PMF.ofFintype_apply] using congrArg ENNReal.ofReal hm.symm

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4204: lemma renameCode_jumpStep"
  (← IO.getStderr).flush
lemma renameCode_jumpStep (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (s : Code N sample) :
    (sourceJumpStep N r s).map (renameCode N e) = sourceJumpStep N r (renameCode N e s) := by
  unfold sourceJumpStep
  rw [← renameChoice_jumpPMF N r e s,PMF.map_comp,PMF.map_comp]
  congr 1
  funext q
  exact renameCode_destination N e s q

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4213: lemma renameCode_completion"
  (← IO.getStderr).flush
lemma renameCode_completion (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (e : A ≃ B) (fuel : Nat) (s : Code N sample) :
    (ancestralCompletion N r fuel s).map (renameCode N e) =
      ancestralCompletion N r fuel (renameCode N e s) := by
  induction fuel generalizing s with
  | zero => simp only [ancestralCompletion,PMF.pure_map]
  | succ fuel ih =>
    rw [ancestralCompletion,PMF.map_bind,ancestralCompletion,← renameCode_jumpStep N r e s,PMF.bind_map]
    congr 1
    funext d
    exact ih d

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4225: lemma renameCode_completed_program"
  (← IO.getStderr).flush
lemma renameCode_completed_program (N : RootedBinary V E X) {sample : A → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (hops : IndependentWord N ops)
    (e : A ≃ B) (s : Code N sample) :
    ((sourceProgram N r ops s).bind (ancestralCompletion N r (Fintype.card A))).map (renameCode N e) =
      (sourceProgram N r ops (renameCode N e s)).bind (ancestralCompletion N r (Fintype.card B)) := by
  rw [PMF.map_bind,← renameCode_program N r ops hops e s,PMF.bind_map]
  congr 1
  funext d
  rw [renameCode_completion,Fintype.card_congr e]

open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4237: lemma renameCode_initial"
  (← IO.getStderr).flush
lemma renameCode_initial (N : RootedBinary V E X) (sample : A → X) (e : A ≃ B) (ρ : V → Bool) :
    renameCode N e (initialCode N sample ρ) = initialCode N (sample ∘ e.symm) ρ := by
  apply Subtype.ext
  apply Snapshot.ext
  · simp [renameCode,renameSnapshot,initialCode,admittedCode,encodeSnapshot,initial]
  · funext x
    simp [renameCode,renameSnapshot,initialCode,admittedCode,encodeSnapshot,initial]
  · funext x
    simp only [renameCode,renameSnapshot,initialCode,admittedCode,encodeSnapshot,initial,
      Finset.mem_univ,dif_pos,Option.map_some]
    apply congrArg some
    apply Subtype.ext
    simp [renameTree,mapLabels]
  · rfl
  · rfl

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4253: lemma renameCode_fullForest"
  (← IO.getStderr).flush
lemma renameCode_fullForest (N : RootedBinary V E X) {sample : A → X}
    (e : A ≃ B) (s : Code N sample) :
    sourceUnrankedForest (state (renameCode N e s)) Finset.univ =
      (sourceUnrankedForest (state s) Finset.univ).image (mapUnranked e) := by
  rw [fullForest_image,fullForest_image,Finset.image_image]
  ext t
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply,
    renameCode_genealogy,renameCode_ancestor,Equiv.symm_apply_apply,mapUnranked_toUnranked]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨e.symm x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨e x,by simpa only [Equiv.symm_apply_apply] using hx⟩

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4270: theorem independent_completed_copy_enumeration"
  (← IO.getStderr).flush
/-- The actual completed independent source law is equivariant under this
explicit copy enumeration, including initialization, original register,
current-owner pulses, ordered mergers and rate-free completion. -/
theorem independent_completed_copy_enumeration (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : A → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (e : A ≃ B) (coin : Hybrid N → Bool) :
    ((((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => false))
      (initialCode N sample (originalRegister N coin))).bind
      (ancestralCompletion N r (Fintype.card A))).map
      (fun s => sourceUnrankedForest (state s) Finset.univ)).map
      (fun F => F.image (mapUnranked e)) =
    ((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => false))
      (initialCode N (sample ∘ e.symm) (originalRegister N coin))).bind
      (ancestralCompletion N r (Fintype.card B))).map
      (fun s => sourceUnrankedForest (state s) Finset.univ) := by
  rw [← renameCode_initial N sample e,
    ← renameCode_completed_program N r _ (actual_independent_calendar N C H (originalGamma p)) e,
    PMF.map_comp,PMF.map_comp]
  congr 1
  funext s
  exact (renameCode_fullForest N e s).symm

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4290: theorem natural_independent_copy_enumeration"
  (← IO.getStderr).flush
/-- One original bank average, unchanged by the selected-copy enumeration. -/
theorem natural_independent_copy_enumeration (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : A → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (e : A ≃ B) :
    (naturalCompletedUnrankedLaw N C sample H p (fun _ => false) r).map
      (fun F => F.image (mapUnranked e)) =
      naturalCompletedUnrankedLaw N C (sample ∘ e.symm) H p (fun _ => false) r := by
  unfold naturalCompletedUnrankedLaw naturalCompletedLaw naturalCalendarLaw originalRegisterPMF
  rw [PMF.bind_map,PMF.bind_bind,PMF.map_bind,PMF.map_bind,
    PMF.bind_map,PMF.bind_bind,PMF.map_bind]
  congr 1
  funext coin
  exact independent_completed_copy_enumeration N C sample H p r e coin

end EnumeratedCopyTransport

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4305: section SharedLegalQueries"
  (← IO.getStderr).flush
section SharedLegalQueries
open UnifiedLean.Source.UniformizedSourceStep G1CutChildPorts
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceUnrankedCopyProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceUnrankedAllPanels GProgram.G2.LiteralTimedObservationPruning
open DotG4.ActualLegalPanelComb DotG34.SpecifiedCombEvent
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4317: lemma actual_selected_independent_crossed"
  (← IO.getStderr).flush
/-- The all-taxon observed forest is pruned by an explicit passive function;
its selected three-copy event is identified by a proved source enumeration. -/
lemma actual_selected_independent_crossed (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (sample : Copy → X) (keep : Finset Copy) (e : Fin 3 ≃ SelectedCopy keep) (i j : X)
    (he : ∀ a, sample (e a).val = tripleSample i j a) :
    ((naturalCompletedUnrankedLaw N C sample H p (fun _ => false) r).map (pruneForest keep))
      ((({threeCherry 0} : Finset (UnrankedTree (Fin 3))).image (mapUnranked e)).image
        (mapUnranked Subtype.val)) = naturalCrossedMass N C H p r (fun _ => false) i j := by
  have hobs : (naturalCompletedUnrankedLaw N C sample H p (fun _ => false) r).map (pruneForest keep) =
      (naturalCompletedUnrankedLaw N C (selectedSample sample keep) H p (fun _ => false) r).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
    calc
      _ = (naturalCompletedLaw N C sample H p (fun _ => false) r).map
          (fun s => sourceUnrankedForest (state s) keep) := by
        unfold naturalCompletedUnrankedLaw
        rw [PMF.map_comp]
        congr 1
        funext s
        exact prune_source_forest (state s) (show GProgram.SourceForest.Valid (UnifiedLean.Source.UniformizedSourceStep.state s) from s.property.forest) keep
      _ = _ := actual_complete_unranked_all_panel_projectivity N C sample keep H p (fun _ => false) r
  have hs : tripleSample i j ∘ e.symm = selectedSample sample keep := by
    funext x
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,selectedSample] using (he (e.symm x)).symm
  have hn := natural_independent_copy_enumeration N C (tripleSample i j) H p r e
  rw [hs] at hn
  rw [hobs,pmf_map_injective_mass _ _
    (Finset.image_injective (selected_mapUnranked_injective keep (e 0))),← hn]
  have hinj : Function.Injective (mapUnranked e) :=
    (mapUnranked_leftInverse e e.symm (fun x => e.symm_apply_apply x)).injective
  rw [pmf_map_injective_mass _ _ (Finset.image_injective hinj)]
  rfl

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4348: noncomputable def sharedSample"
  (← IO.getStderr).flush
noncomputable def sharedSample (i : X) (m : Nat) : X ⊕ Fin m → X := Sum.elim id (fun _ => i)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4350: def sharedEmbedding"
  (← IO.getStderr).flush
def sharedEmbedding (i j : X) (m : Nat) : Fin m ⊕ Bool → X ⊕ Fin m
  | .inl a => .inr a
  | .inr true => .inl i
  | .inr false => .inl j

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4355: lemma sharedEmbedding_injective"
  (← IO.getStderr).flush
lemma sharedEmbedding_injective (i j : X) (hij : i ≠ j) (m : Nat) :
    Function.Injective (sharedEmbedding i j m) := by
  intro a b h
  cases a with
  | inl a => cases b <;> simp_all [sharedEmbedding]
  | inr a => cases b with
    | inl b => simp [sharedEmbedding] at h
    | inr b => cases a <;> cases b <;> simp_all [sharedEmbedding,Ne.symm hij]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4364: noncomputable def sharedKeep"
  (← IO.getStderr).flush
noncomputable def sharedKeep (i j : X) (m : Nat) : Finset (X ⊕ Fin m) :=
  Finset.univ.image (sharedEmbedding i j m)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4367: noncomputable def sharedSelected"
  (← IO.getStderr).flush
noncomputable def sharedSelected (i j : X) (m : Nat) (a : Fin m ⊕ Bool) : SelectedCopy (sharedKeep i j m) :=
  ⟨sharedEmbedding i j m a,Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩⟩
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4369: noncomputable def sharedB"
  (← IO.getStderr).flush
noncomputable def sharedB (i j : X) (m : Nat) : SelectedCopy (sharedKeep i j m) :=
  sharedSelected i j m (.inr false)
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4371: noncomputable def sharedA"
  (← IO.getStderr).flush
noncomputable def sharedA (i j : X) (m : Nat) : List (SelectedCopy (sharedKeep i j m)) :=
  (List.finRange m).map (fun a => sharedSelected i j m (.inl a)) ++ [sharedSelected i j m (.inr true)]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4374: lemma sharedSelected_injective"
  (← IO.getStderr).flush
lemma sharedSelected_injective (i j : X) (hij : i ≠ j) (m : Nat) :
    Function.Injective (sharedSelected i j m) := by
  intro a b h
  exact sharedEmbedding_injective i j hij m (congrArg Subtype.val h)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4379: lemma shared_cover"
  (← IO.getStderr).flush
lemma shared_cover (i j : X) (m : Nat) (x : SelectedCopy (sharedKeep i j m)) :
    x = sharedB i j m ∨ x ∈ sharedA i j m := by
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp x.property
  have hx : x = sharedSelected i j m a := Subtype.ext he.symm
  rw [hx]
  cases a with
  | inl a => exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨a,List.mem_finRange a,rfl⟩))
  | inr a => cases a <;> simp [sharedB,sharedA]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4388: lemma shared_A_samples"
  (← IO.getStderr).flush
lemma shared_A_samples (i j : X) (hij : i ≠ j) (m : Nat)
    (x : SelectedCopy (sharedKeep i j m)) (hx : x ≠ sharedB i j m) : sharedSample i m x.val = i := by
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp x.property
  have hxe : x = sharedSelected i j m a := Subtype.ext he.symm
  rw [hxe]
  cases a with
  | inl a => rfl
  | inr a => cases a with
    | true => rfl
    | false => exact False.elim (hx hxe)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4399: lemma sharedA_nodup"
  (← IO.getStderr).flush
lemma sharedA_nodup (i j : X) (hij : i ≠ j) (m : Nat) : (sharedA i j m).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange m).map ((sharedSelected_injective i j hij m).comp Sum.inl_injective),by simp,?_⟩
  intro x hx y hy he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  have hy' : y = sharedSelected i j m (.inr true) := by simpa using hy
  rw [hy'] at he
  have hf := sharedSelected_injective i j hij m he
  cases hf

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4409: lemma sharedA_excludes_B"
  (← IO.getStderr).flush
lemma sharedA_excludes_B (i j : X) (hij : i ≠ j) (m : Nat) : sharedB i j m ∉ sharedA i j m := by
  intro h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨a,ha,he⟩ := List.mem_map.mp h
    have hf := sharedSelected_injective i j hij m he
    cases hf
  · have he : sharedB i j m = sharedSelected i j m (.inr true) := by simpa using h
    have hf := sharedSelected_injective i j hij m he
    cases hf

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4419: lemma sharedA_length"
  (← IO.getStderr).flush
lemma sharedA_length (i j : X) (m : Nat) : (sharedA i j m).length = m+1 := by simp [sharedA]
run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4420: lemma sharedA_nonempty"
  (← IO.getStderr).flush
lemma sharedA_nonempty (i j : X) (m : Nat) : sharedA i j m ≠ [] := by simp [sharedA]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4422: noncomputable def sharedCombEvent"
  (← IO.getStderr).flush
noncomputable def sharedCombEvent (i j : X) (m : Nat) : Finset (UnrankedTree (X ⊕ Fin m)) :=
  {toUnranked (comb (sharedB i j m).val ((sharedA i j m).map Subtype.val))}

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4425: lemma sharedSample_surjective"
  (← IO.getStderr).flush
lemma sharedSample_surjective (i : X) (m : Nat) : Function.Surjective (sharedSample i m) :=
  fun x => ⟨Sum.inl x,rfl⟩

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4428: lemma actual_shared_common_comb"
  (← IO.getStderr).flush
lemma actual_shared_common_comb (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) (m : Nat) :
    (((naturalCompletedUnrankedLaw N C (sharedSample i m) H p (fun _ => true) r).map
      (pruneForest (sharedKeep i j m))) (sharedCombEvent i j m)).toReal =
      combProbability N C H p r i j (m+1) := by
  unfold sharedCombEvent combProbability
  rw [actual_full_panel_selected_comb_moment N C H p r i j (sharedSample i m)
    (sharedSample_surjective i m) (sharedKeep i j m) (sharedB i j m) rfl
    (shared_A_samples i j hij m) (sharedA i j m) (shared_cover i j m)
    (sharedA_nodup i j hij m) (sharedA_excludes_B i j hij m) (sharedA_nonempty i j m),
    sharedA_length,actual_natural_completed_comb_moment N C H p r i j (m+1) (by omega)]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4441: noncomputable def sharedTripleMap"
  (← IO.getStderr).flush
noncomputable def sharedTripleMap (i j : X) : Fin 3 → SelectedCopy (sharedKeep i j 1)
  | 0 => sharedSelected i j 1 (.inr true)
  | 1 => sharedSelected i j 1 (.inl 0)
  | 2 => sharedSelected i j 1 (.inr false)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4446: lemma sharedTripleMap_bijective"
  (← IO.getStderr).flush
lemma sharedTripleMap_bijective (i j : X) (hij : i ≠ j) :
    Function.Bijective (sharedTripleMap i j) := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hf := sharedSelected_injective i j hij 1 h
    all_goals cases hf
  · intro x
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp x.property
    have hx : sharedSelected i j 1 a = x := Subtype.ext he
    cases a with
    | inl a => fin_cases a; exact ⟨1,hx⟩
    | inr a => cases a with
      | false => exact ⟨2,hx⟩
      | true => exact ⟨0,hx⟩

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4462: noncomputable def sharedTripleEquiv"
  (← IO.getStderr).flush
noncomputable def sharedTripleEquiv (i j : X) (hij : i ≠ j) : Fin 3 ≃ SelectedCopy (sharedKeep i j 1) :=
  Equiv.ofBijective (sharedTripleMap i j) (sharedTripleMap_bijective i j hij)

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4465: lemma sharedTriple_sample"
  (← IO.getStderr).flush
lemma sharedTriple_sample (i j : X) (hij : i ≠ j) (a : Fin 3) :
    sharedSample i 1 (sharedTripleEquiv i j hij a).val = tripleSample i j a := by
  fin_cases a <;> rfl

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4469: lemma sharedTriple_event"
  (← IO.getStderr).flush
lemma sharedTriple_event (i j : X) (hij : i ≠ j) :
    ((({threeCherry 0} : Finset (UnrankedTree (Fin 3))).image
      (mapUnranked (sharedTripleEquiv i j hij))).image (mapUnranked Subtype.val)) =
      sharedCombEvent i j 1 := by
  rw [threeCherry_zero_eq_specified]
  simp only [Finset.image_singleton,mapUnranked_toUnranked,mapLabels_comb,List.map_cons,List.map_nil]
  rfl

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4477: lemma actual_shared_independent_crossed"
  (← IO.getStderr).flush
lemma actual_shared_independent_crossed (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    (((naturalCompletedUnrankedLaw N C (sharedSample i 1) H p (fun _ => false) r).map
      (pruneForest (sharedKeep i j 1))) (sharedCombEvent i j 1)).toReal =
      independentCrossedProbability N C H p r i j := by
  have h := actual_selected_independent_crossed N C H p r (sharedSample i 1)
    (sharedKeep i j 1) (sharedTripleEquiv i j hij) i j (sharedTriple_sample i j hij)
  rw [sharedTriple_event] at h
  exact congrArg ENNReal.toReal h

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4490: def pairedQueryExtras"
  (← IO.getStderr).flush
/-- Three full-law requests per taxon: COMMON with one extra, COMMON with two
extras, and INDEPENDENT with one extra. No request depends on the other taxon. -/
def pairedQueryExtras (q : Fin 3) : Nat := if q = 1 then 2 else 1

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4492: def pairedQueryMode"
  (← IO.getStderr).flush
def pairedQueryMode (q : Fin 3) : Bool := if q = 2 then false else true

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4494: noncomputable def pairedQueryLaw"
  (← IO.getStderr).flush
noncomputable def pairedQueryLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i : X) (q : Fin 3) : PMF (Finset (UnrankedTree (X ⊕ Fin (pairedQueryExtras q)))) :=
  naturalCompletedUnrankedLaw N C (sharedSample i (pairedQueryExtras q)) H p
    (fun _ => pairedQueryMode q) r

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4500: lemma pairedQuery_all_taxa"
  (← IO.getStderr).flush
lemma pairedQuery_all_taxa (i : X) (q : Fin 3) :
    Function.Surjective (sharedSample i (pairedQueryExtras q)) := sharedSample_surjective i _

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4503: lemma pairedQuery_copy_budget"
  (← IO.getStderr).flush
lemma pairedQuery_copy_budget (q : Fin 3) :
    Fintype.card (X ⊕ Fin (pairedQueryExtras q)) ≤ Fintype.card X + 2 := by
  fin_cases q <;> simp [pairedQueryExtras]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4507: lemma pairedQuery_menu_budget : Fintype.card"
  (← IO.getStderr).flush
lemma pairedQuery_menu_budget : Fintype.card (X × Fin 3) = 3 * Fintype.card X := by
  simp [Nat.mul_comm]

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4512: noncomputable def pairedQueryReadout"
  (← IO.getStderr).flush
/-- A scalar reader of a full shared query; pruning is a function of the
observed unranked forest and does not expose a latent route or bank. -/
noncomputable def pairedQueryReadout (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (q : Fin 3) : ℝ :=
  (((pairedQueryLaw N C H p r i q).map (pruneForest (sharedKeep i j (pairedQueryExtras q))))
    (sharedCombEvent i j (pairedQueryExtras q))).toReal

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4518: def LegalPairedCertificate"
  (← IO.getStderr).flush
def LegalPairedCertificate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E) : Prop :=
  ∀ i j, i ≠ j →
    18 * pairedQueryReadout N C H p r i j 1 = (3 * pairedQueryReadout N C H p r i j 0)^3 ∧
    pairedQueryReadout N C H p r i j 2 = pairedQueryReadout N C H p r i j 0

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4524: lemma pairedQueryReadout_zero"
  (← IO.getStderr).flush
lemma pairedQueryReadout_zero (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    pairedQueryReadout N C H p r i j 0 = combProbability N C H p r i j 2 := by
  exact actual_shared_common_comb N C H p r i j hij 1

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4530: lemma pairedQueryReadout_one"
  (← IO.getStderr).flush
lemma pairedQueryReadout_one (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    pairedQueryReadout N C H p r i j 1 = combProbability N C H p r i j 3 := by
  exact actual_shared_common_comb N C H p r i j hij 2

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4536: lemma pairedQueryReadout_two"
  (← IO.getStderr).flush
lemma pairedQueryReadout_two (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (hij : i ≠ j) :
    pairedQueryReadout N C H p r i j 2 = independentCrossedProbability N C H p r i j := by
  exact actual_shared_independent_crossed N C H p r i j hij

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4544: theorem actual_legal_paired_certificate_iff_noHybrids"
  (← IO.getStderr).flush
/-- Physical ordinary-tree recognition by the actual legal shared full laws.
No calibrated geometry, route mixture or exchangeable-reader value is an input. -/
theorem actual_legal_paired_certificate_iff_noHybrids
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (hcut : CutChild N) :
    LegalPairedCertificate N C H p r ↔ NoHybrids N := by
  have he : LegalPairedCertificate N C H p r ↔ PairedNaturalCalibration N C H p r := by
    unfold LegalPairedCertificate PairedNaturalCalibration
    apply forall_congr'; intro i
    apply forall_congr'; intro j
    apply imp_congr_right; intro hij
    rw [pairedQueryReadout_zero N C H p r i j hij,pairedQueryReadout_one N C H p r i j hij,
      pairedQueryReadout_two N C H p r i j hij]
  exact he.trans (actual_paired_natural_calibration_iff_noHybrids N C H p r hcut)

variable {V' E' : Type*} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4559: lemma pairedQuery_equal_scalar_data"
  (← IO.getStderr).flush
lemma pairedQuery_equal_scalar_data
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E')
    (hq : ∀ i q, pairedQueryLaw N' C' H' p' r' i q = pairedQueryLaw N C H p r i q) :
    (∀ i j, i ≠ j → combProbability N' C' H' p' r' i j 2 = combProbability N C H p r i j 2) ∧
    (∀ i j, i ≠ j → combProbability N' C' H' p' r' i j 3 = combProbability N C H p r i j 3) ∧
    (∀ i j, i ≠ j → independentCrossedProbability N' C' H' p' r' i j =
      independentCrossedProbability N C H p r i j) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    have h := congrArg (fun μ => ((μ.map (pruneForest (sharedKeep i j 1))) (sharedCombEvent i j 1)).toReal) (hq i 0)
    simpa only [pairedQueryLaw,pairedQueryExtras,pairedQueryMode,ite_false,ite_true,
      actual_shared_common_comb N C H p r i j hij 1,
      actual_shared_common_comb N' C' H' p' r' i j hij 1] using h
  · intro i j hij
    have h := congrArg (fun μ => ((μ.map (pruneForest (sharedKeep i j 2))) (sharedCombEvent i j 2)).toReal) (hq i 1)
    simpa only [pairedQueryLaw,pairedQueryExtras,pairedQueryMode,ite_false,ite_true,
      actual_shared_common_comb N C H p r i j hij 2,
      actual_shared_common_comb N' C' H' p' r' i j hij 2] using h
  · intro i j hij
    have h := congrArg (fun μ => ((μ.map (pruneForest (sharedKeep i j 1))) (sharedCombEvent i j 1)).toReal) (hq i 2)
    simpa only [pairedQueryLaw,pairedQueryExtras,pairedQueryMode,ite_false,ite_true,
      actual_shared_independent_crossed N C H p r i j hij,
      actual_shared_independent_crossed N' C' H' p' r' i j hij] using h

run_cmd Lean.Elab.Command.liftIO do
  IO.eprintln "PAIRED_COPY_DIAGNOSTIC before clean line 4589: theorem actual_ordinary_target_shared_queries_all_future"
  (← IO.getStderr).flush
/-- The inherited ordinary-target contract: the three shared all-taxon laws per
taxon force every future natural response in BOTH modes, against arbitrary
finite rival graph carriers. The query budget is proved above, not assumed. -/
theorem actual_ordinary_target_shared_queries_all_future
    (hn4 : 4 ≤ Fintype.card X)
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (hn : NoHybrids N)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E') (hcut' : CutChild N')
    (hq : ∀ i q, pairedQueryLaw N' C' H' p' r' i q = pairedQueryLaw N C H p r i q) :
    ∀ (Copy : Type*) [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
      (common : Hybrid N → Bool) (common' : Hybrid N' → Bool),
      naturalCompletedUnrankedLaw N' C' sample H' p' common' r' =
        naturalCompletedUnrankedLaw N C sample H p common r := by
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨hc,hd,hu⟩ := pairedQuery_equal_scalar_data N C H p r N' C' H' p' r' hq
  exact actual_ordinary_target_paired_all_future N C H p r hn N' C' H' p' r' hcut' hc hd hu

end SharedLegalQueries

end DotG4.PairedNaturalTreeCertificate

set_option stderrAsMessages true
