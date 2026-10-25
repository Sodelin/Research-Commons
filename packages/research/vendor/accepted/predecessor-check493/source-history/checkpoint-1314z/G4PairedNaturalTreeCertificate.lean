import G4WholeProfileDetermination
import G4ActualBelowMeetingSupport
import G5NativeOriginalRouteCoverage

/-!
# Actual paired natural ordinary-tree certificate

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED source development.
Formalization of the independently accepted paired natural certificate and
one-bit geometric proof. The single intended endpoint includes actual natural
INDEPENDENT readout and all-future BOTH responses; the present file is partial.
No new mathematical result, build acceptance or general G4 closure is claimed.
-/
namespace DotG4.PairedNaturalTreeCertificate
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.NonbridgeRoutes
open GProgram.G5.AttainedChronology GProgram.G5.ComponentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open DotG4.ActualObservableBankCertificate DotG4.ActualNaturalCombMoments
open DotG4.ActualSelectedPathExposure DotG4.ActualBankFirstMeeting
open scoped Classical BigOperators ENNReal
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
      have hef : e = f := selected_edges_eq_away N P Q h hPQ hp hq
        List.mem_cons_self List.mem_cons_self (ht.trans htf.symm)
        (havoid e List.mem_cons_self)
      subst f
      obtain ⟨us,hus,hup⟩ := ih tail
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
  induction p generalizing fs with
  | nil =>
    cases q with
    | nil => rfl
    | cons ht hf tail => exact False.elim (original_edge_target_not_root N _ ht)
  | @cons a z e es ht he rest ih =>
    cases q with
    | nil => exact False.elim (original_edge_target_not_root N e ht)
    | @cons _ _ f fs htf hf tail =>
      have hef : e = f := selected_edges_eq_away N P Q h hPQ hp hq
        List.mem_cons_self List.mem_cons_self (ht.trans htf.symm)
        (havoid e List.mem_cons_self)
      subst f
      congr 1
      exact ih tail (fun d hd => hp d (List.mem_cons_of_mem e hd))
        (fun d hd => hq d (List.mem_cons_of_mem e hd))
        (fun d hd => havoid d (List.mem_cons_of_mem e hd))

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
  obtain ⟨pre,post,hlist,hpre,hpost⟩ := p.split_at_original_edge he
  refine ⟨pre,post,by simpa only [List.append_assoc,List.singleton_append] using hlist,
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
  rw [F.left_eq,F.right_eq,List.mem_append,List.mem_append]
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
  left_eq := by rw [F.left_eq,List.append_assoc]
  right_eq := by rw [F.right_eq,List.append_assoc]
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
  obtain ⟨pre,post,hlist,hpre,hpost⟩ := hpa.split_at_original_edge he
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
  · simpa only [List.append_assoc,List.singleton_append] using hlist
  · simpa only [List.reverse_reverse,List.reverse_append] using congrArg List.reverse htail
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
    rw [he]
    exact List.mem_append.mpr (Or.inl hee)
  have selB (x : X) (pre post : List E)
      (he : (commonRoutes N C H b).edges x = pre ++ post) :
      RespectsSelector N (coinSelector N H b) pre := by
    intro e hee
    apply (compiledRoute_source_spec N C (coinSelector N H b) (N.leaf x)).2 e
    rw [he]
    exact List.mem_append.mpr (Or.inl hee)
  have heA := selected_path_unique N (coinSelector N H a) haiP hajP
    (selA i ai pi hai) (selA j aj pj haj)
  have heB := selected_path_unique N (coinSelector N H b) hbiP hbjP
    (selB i bi pi hbi) (selB j bj pj hbj)
  obtain ⟨F⟩ := selected_path_fork N (coinSelector N H a) hpi hpj hpiS hpjS
  have FA : PathFork N N.root (N.leaf i) (N.leaf j)
      ((commonRoutes N C H a).edges i) ((commonRoutes N C H a).edges j) := by
    exact { vertex := F.vertex, stem := ai ++ F.stem, left := F.left, right := F.right
      left_eq := by rw [hai,F.left_eq,List.append_assoc]
      right_eq := by rw [haj,← heA,F.right_eq,List.append_assoc]
      stem_path := haiP.append F.stem_path
      left_path := F.left_path, right_path := F.right_path, separate := F.separate }
  have FB : PathFork N N.root (N.leaf i) (N.leaf j)
      ((commonRoutes N C H b).edges i) ((commonRoutes N C H b).edges j) := by
    exact { vertex := F.vertex, stem := bi ++ F.stem, left := F.left, right := F.right
      left_eq := by rw [hbi,F.left_eq,List.append_assoc]
      right_eq := by rw [hbj,← heB,F.right_eq,List.append_assoc]
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

end DotG4.PairedNaturalTreeCertificate
