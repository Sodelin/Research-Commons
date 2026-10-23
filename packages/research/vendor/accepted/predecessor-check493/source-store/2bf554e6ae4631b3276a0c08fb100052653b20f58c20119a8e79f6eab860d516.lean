import UnifiedLean.Source.NativeCommonPairGerm

/-!
# Actual original tip/calendar current-port coverage

Contributor: dot / GPT-6.1 Sol, 2026-10-02. Derives the bridge-population or
component-exit description from an arbitrary original tip and a valid original
calendar age. No source port-selection oracle or probability/output law is a
field. This supplies the all-source case geometry needed to assemble the
already checked native fair position/germ endpoints. Current-port geometry is
latent source structure, not newly measured biological information.
-/
namespace UnifiedLean.Source.NativeCurrentPortCompiler
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentSupport GProgram.G5.ParentCalendar
open GProgram.G5.ComponentEntries GProgram.G5.ComponentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeFairCurrentPosition
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma original_leaf_not_edge_source (N : RootedBinary V E X) (x : X) (e : E) :
    N.graph.source e ≠ N.leaf x := by
  intro he
  have hm : e ∈ Finset.univ.filter (fun f : E => N.graph.source f = N.leaf x) := by simp [he]
  have hh := (N.leaf_degrees x).2
  rw [EdgeGraph.outDegree,Finset.card_eq_zero] at hh
  rw [hh] at hm
  exact Finset.notMem_empty e hm

/-- Original degree-one taxon incidence gives an actual edge-occurrence
bridge, with no simplicity/planarity assumption. -/
theorem original_leaf_incoming_bridge (N : RootedBinary V E X) (C : Calendar N.graph)
    {x : X} {e : E} (he : N.graph.target e = N.leaf x) : N.graph.IsBridge e := by
  intro hreach
  rcases Relation.ReflTransGen.cases_tail hreach with hsame | ⟨v,_,f,hne,hinc⟩
  · have ha := C.edge_older e
    rw [hsame] at ha
    exact (lt_irrefl _) ha
  · rcases hinc with ⟨_,ht⟩ | ⟨hs,_⟩
    · have hfe := incoming_equal_of_indegree_le_one N (N.leaf_degrees x).1.le
        (ht.trans he) he
      exact hne hfe
    · exact original_leaf_not_edge_source N x f (hs.trans he)

/-- A tip's bridge-deleted component is the singleton actual taxon vertex. -/
theorem original_leaf_sameBlob_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    {x : X} {v : V} : N.graph.SameBlob v (N.leaf x) ↔ v = N.leaf x := by
  constructor
  · intro hp
    rcases Relation.ReflTransGen.cases_tail hp with hsame | ⟨w,_,e,hnb,hinc⟩
    · exact hsame.symm
    · rcases hinc with ⟨_,ht⟩ | ⟨hs,_⟩
      · exact False.elim (hnb (original_leaf_incoming_bridge N C ht))
      · exact False.elim (original_leaf_not_edge_source N x e hs)
  · rintro rfl
    exact N.graph.sameBlob_refl _

lemma EdgePath.sameBlob_of_all_nonbridge {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : EdgePath G a b es) (hn : ∀ e ∈ es, ¬G.IsBridge e) : G.SameBlob a b := by
  induction p with
  | nil a => exact G.sameBlob_refl a
  | @cons a b e es hs rest ih =>
      have hh := G.nonbridge_sameBlob (hn e List.mem_cons_self)
      rw [hs] at hh
      exact hh.trans (ih (fun f hf => hn f (List.mem_cons_of_mem e hf)))

/-- The first original bridge in an actual path is constructed together with
its nonbridge prefix and descendant suffix. -/
theorem EdgePath.first_original_bridge {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : EdgePath G a b es) (hab : ¬G.SameBlob a b) :
    ∃ pre e post, es = pre ++ e :: post ∧ G.IsBridge e ∧
      EdgePath G a (G.source e) pre ∧ (∀ f ∈ pre, ¬G.IsBridge f) ∧
      EdgePath G (G.target e) b post := by
  induction p with
  | nil a => exact False.elim (hab (G.sameBlob_refl a))
  | @cons a b e es hs rest ih =>
      by_cases he : G.IsBridge e
      · refine ⟨[],e,es,rfl,he,?_,by simp,rest⟩
        rw [hs]
        exact EdgePath.nil a
      · have hnb : ¬G.SameBlob (G.target e) b := by
          intro hb
          have hh := G.nonbridge_sameBlob he
          rw [hs] at hh
          exact hab (hh.trans hb)
        obtain ⟨pre,f,post,hes,hbridge,hpre,hkeep,hpost⟩ := ih hnb
        refine ⟨e::pre,f,post,by simp [hes],hbridge,EdgePath.cons hs hpre,?_,hpost⟩
        intro g hg
        rcases List.mem_cons.mp hg with hge | hg
        · simpa only [hge] using he
        · exact hkeep g hg

/-- Only actual original graph/calendar geometry describes a current case.
No current position, fair law, two-support bound or desired output is a field. -/
def CurrentPortCase (N : RootedBinary V E X) (C : Calendar N.graph) (x : X) (t : ℝ) : Prop :=
  (∃ e : E, N.graph.IsBridge e ∧ N.graph.DReach (N.graph.target e) (N.leaf x) ∧ C.Active t e) ∨
  (∃ exit : E, N.graph.IsBridge exit ∧ N.graph.DReach (N.graph.target exit) (N.leaf x) ∧
    InCurrentComponentInterval N C (N.graph.source exit) t)

/-- Every original tip at every admitted below-root calendar age has an actual
bridge-population or actual component-exit port description. The input does
not provide a selected current port or a hidden probability interface. -/
theorem original_tip_current_port_case (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : X) {t : ℝ} (hl : C.age (N.leaf x) ≤ t) (hu : t < C.age N.root) :
    CurrentPortCase N C x t := by
  obtain ⟨es,hp⟩ := original_tip_route_exists N x
  obtain ⟨f,hf,ha⟩ := EdgePath.active_exists C hp hl hu
  obtain ⟨pre,post,hes,hpre,hpost⟩ := EdgePath.split_at_original_edge hp hf
  by_cases hb : N.graph.IsBridge f
  · exact Or.inl ⟨f,hb,hpost.directed,ha⟩
  · have hnot : ¬N.graph.SameBlob (N.graph.target f) (N.leaf x) := by
      intro hs
      have ht := (original_leaf_sameBlob_iff N C).mp hs
      exact hb (original_leaf_incoming_bridge N C ht)
    obtain ⟨mid,exit,tail,hposteq,hexit,hmid,hnmid,htail⟩ := EdgePath.first_original_bridge hpost hnot
    have hsblob : N.graph.SameBlob (N.graph.source f) (N.graph.source exit) :=
      (N.graph.nonbridge_sameBlob hb).trans (EdgePath.sameBlob_of_all_nonbridge hmid hnmid)
    have hlow : C.age (N.graph.source exit) ≤ t :=
      (C.age_le_of_directed hmid.directed).trans ha.1
    refine Or.inr ⟨exit,hexit,htail.directed,hlow,?_⟩
    by_cases hr : N.graph.SameBlob N.root (N.graph.source exit)
    · exact Or.inl ⟨hr,hu⟩
    · obtain ⟨entry,hentry,hblob⟩ := nonroot_component_has_incoming_bridge N.graph N.root N.rooted _ hr
      have he : IsComponentEntryFor N (N.graph.target entry) (N.graph.source exit) :=
        Or.inr ⟨entry,hentry,rfl,hblob⟩
      have hfblob := hblob.trans (N.graph.sameBlob_symm hsblob)
      have hreach := component_entry_reaches_sameBlob N he hfblob
      exact Or.inr ⟨entry,hentry,hblob,ha.2.trans_le (C.age_le_of_directed hreach)⟩

/-- A component-exit hybrid port obtains its actual parent orientation and
component entry from original registry/calendar facts; no entry oracle. -/
theorem original_current_hybrid_port_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ} {exit : E}
    (he : N.graph.IsBridge exit) (hbelow : N.graph.DReach (N.graph.target exit) (N.leaf x))
    (hh : N.graph.IsHybrid (N.graph.source exit))
    (ht : InCurrentComponentInterval N C (N.graph.source exit) t) :
    Nonempty (CurrentHybridPort N C H x t) := by
  let h : Hybrid N := ⟨N.graph.source exit,hh⟩
  have hport : N.graph.source exit = (H.parents h).hybrid := (H.original_site h).symm
  have hl : C.age (H.parents h).hybrid ≤ t := by rw [←hport]; exact ht.1
  rcases ht.2 with ⟨hroot,hu⟩ | ⟨entry,hentry,hblob,hu⟩
  · refine ⟨⟨h,exit,he,hport,hbelow,N.root,?_,hl,hu⟩⟩
    exact Or.inl ⟨rfl,by rwa [←hport]⟩
  · refine ⟨⟨h,exit,he,hport,hbelow,N.graph.target entry,?_,hl,hu⟩⟩
    exact Or.inr ⟨entry,hentry,rfl,by rwa [←hport]⟩

/-- All current descriptions contain only actual ORIGINAL geometry. -/
inductive NativeCurrentDescription (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x : X) (t : ℝ)
  | bridge (e : E) (he : N.graph.IsBridge e)
      (hbelow : N.graph.DReach (N.graph.target e) (N.leaf x)) (ha : C.Active t e)
  | ordinary (exit : E) (he : N.graph.IsBridge exit)
      (hbelow : N.graph.DReach (N.graph.target exit) (N.leaf x))
      (ho : ¬N.graph.IsHybrid (N.graph.source exit))
      (ht : InCurrentComponentInterval N C (N.graph.source exit) t)
  | hybrid (port : CurrentHybridPort N C H x t)

/-- Description existence is derived uniformly over the full original graph,
not restricted to supplied hybrid ports or a tested finite topology census. -/
theorem original_current_description_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x : X) {t : ℝ}
    (hl : C.age (N.leaf x) ≤ t) (hu : t < C.age N.root) :
    Nonempty (NativeCurrentDescription N C H x t) := by
  rcases original_tip_current_port_case N C x hl hu with
    ⟨e,he,hbelow,ha⟩ | ⟨exit,he,hbelow,ht⟩
  · exact ⟨.bridge e he hbelow ha⟩
  · by_cases hh : N.graph.IsHybrid (N.graph.source exit)
    · obtain ⟨P⟩ := original_current_hybrid_port_exists N C H he hbelow hh ht
      exact ⟨.hybrid P⟩
    · exact ⟨.ordinary exit he hbelow hh ht⟩

/-- A selector is constructed from original parent positions or the proved
constant ordinary/bridge population. No arbitrary current-position fitting. -/
noncomputable def descriptionPositions (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ} :
    NativeCurrentDescription N C H x t → Bool → E
  | .bridge e _ _ _, _ => e
  | .ordinary exit he hbelow ho ht, _ =>
      Classical.choose (native_ordinary_port_constant N C hcut H he hbelow ho ht)
  | .hybrid P, b => currentParentPosition P b

def descriptionSite {N : RootedBinary V E X} {C : Calendar N.graph}
    {H : OriginalParentRegistry N} {x : X} {t : ℝ} :
    NativeCurrentDescription N C H x t → Option (Hybrid N)
  | .bridge _ _ _ _ => none
  | .ordinary _ _ _ _ _ => none
  | .hybrid P => some P.site

noncomputable def descriptionRead (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (coin : Hybrid N → Bool) : E :=
  descriptionPositions N C hcut H D (match descriptionSite D with
    | none => false
    | some h => coin h)

/-- The full original native compiled route uses the constructed selector at
EVERY current bridge/ordinary/hybrid case and every original coin assignment. -/
theorem description_read_native_source_spec (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (coin : X → Hybrid N → Bool) :
    descriptionRead N C hcut H D (coin x) ∈ (compiledRouteFamily N C H coin).edges x ∧
      C.Active t (descriptionRead N C hcut H D (coin x)) := by
  cases D with
  | bridge e he hbelow ha =>
      exact ⟨bridge_mem_every_descendant_route N he ((compiledRouteFamily N C H coin).valid x) hbelow,ha⟩
  | ordinary exit he hbelow ho ht =>
      exact ⟨((Classical.choose_spec (native_ordinary_port_constant N C hcut H he hbelow ho ht)) coin).1,
        ((Classical.choose_spec (native_ordinary_port_constant N C hcut H he hbelow ho ht)) coin).2.1⟩
  | hybrid P =>
      exact native_tip_current_parent_spec N C hcut H coin x P.site
        P.exit_bridge P.port P.below P.component P.lower P.upper

/-- Current-position dependency is now a uniformly constructed ORIGINAL-source
selector for every tip and every valid below-root age, with full case coverage. -/
theorem original_tip_native_selector_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (x : X) {t : ℝ}
    (hl : C.age (N.leaf x) ≤ t) (hu : t < C.age N.root) :
    ∃ D : NativeCurrentDescription N C H x t, ∀ coin : X → Hybrid N → Bool,
      descriptionRead N C hcut H D (coin x) ∈ (compiledRouteFamily N C H coin).edges x ∧
      C.Active t (descriptionRead N C hcut H D (coin x)) := by
  obtain ⟨D⟩ := original_current_description_exists N C H x hl hu
  exact ⟨D,fun coin => description_read_native_source_spec N C hcut H D coin⟩

#print axioms original_current_hybrid_port_exists
#print axioms original_current_description_exists
#print axioms description_read_native_source_spec
#print axioms original_tip_native_selector_exists
#print axioms original_leaf_incoming_bridge
#print axioms original_leaf_sameBlob_iff
#print axioms EdgePath.first_original_bridge
#print axioms original_tip_current_port_case
end UnifiedLean.Source.NativeCurrentPortCompiler
