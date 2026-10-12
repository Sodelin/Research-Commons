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
  · exact ⟨e,ht,by simpa only [hs] using hu⟩

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
  simp only [descendantSelector,dif_pos ⟨hv,hr⟩]
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
  have G : PathFork N N.root (N.leaf i) (N.leaf j)
      ((commonRoutes N C H coin).edges i) ((commonRoutes N C H coin).edges j) :=
    { vertex := F.vertex, stem := pre ++ F.stem, left := F.left, right := F.right
      left_eq := by rw [hei,F.left_eq,List.append_assoc]
      right_eq := by rw [hej,F.right_eq,List.append_assoc]
      stem_path := hpre.append F.stem_path
      left_path := F.left_path, right_path := F.right_path, separate := F.separate }
  have hm := (bankFork N C H coin i j).vertex_unique N C r G
  exact ⟨coin,hm.symm ▸ F.stem_path.directed⟩

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
  · simpa only [hv,N.root_degrees.2]
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
  have hn : F.left ≠ [] := by
    intro he
    have hp := F.left_path
    rw [he] at hp
    cases hp
    exact bankMeeting_ne_left_leaf N C H a hij rfl
  cases hl : F.left with
  | nil => exact False.elim (hn hl)
  | cons e tail =>
    have hp := F.left_path
    rw [hl] at hp
    cases hp with
    | cons hs htail =>
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
    · simp [outs,his]
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
  | some t => rfl

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
      simpa only [Equiv.symm_apply_apply,ha]
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
    ⟨permuteSnapshot σ s.val,⟨permuteSnapshot_valid N.root σ s.val s.property.forest,
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
  right_inv := by simpa using permuteCode_inverse (sample := sample) N σ.symm

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
    change permuteSnapshot σ (encodeSnapshot (merge (state s) q.2.val.1 q.2.val.2) _) =
      encodeSnapshot (merge (state (permuteCode N σ s)) (σ q.2.val.1) (σ q.2.val.2)) _
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
            Equiv.symm_apply_apply,mapLabels]
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
  change permuteSnapshot σ (encodeSnapshot (transport (state s) f ev) _) =
    encodeSnapshot (transport (state (permuteCode N σ s)) g ev') _
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
      simp only [dif_pos hx,dif_pos hx',GProgram.G7.CoinReindexing.coinTransport,
        permuteNodeEquiv,Equiv.symm_apply_apply]
    · have hx' := mt (permuteCode_node_member N σ s hs H.hybrid x).mp hx
      simp only [dif_neg hx,dif_neg hx',permuteCode_location N σ s hs,Equiv.symm_apply_apply]

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
      rw [sourceProgram,PMF.map_bind,sourceProgram,← permuteCode_time N r σ t s hs,PMF.bind_map]
      apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
      intro d hd
      exact ih ht d (commonDescendants_time N r t s hs hd)
    | boundary b =>
      rw [sourceProgram,PMF.map_bind,sourceProgram,← permuteCode_boundary N b hh σ s hs,PMF.bind_map]
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
end DotG4.PairedNaturalTreeCertificate
