import G1LiteralHybridParentSuppressionBijection

/-! Actual semidirected switching: keep all undirected edges, choose exactly
ONE marked incoming edge per hybrid, equivalently delete the other of its
TWO actual parent IDs. Both directions to rooted original switchings are
derived from the literal parent-ID equivalence; no target law is an input. -/
namespace G1LiteralSemidirectedSwitchingTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1ActualMarkedSemidirectedGalledAdmission G1LiteralHybridParentSuppressionBijection
open G1RootSubdivisionPlanarAdmission G1FormerRootHybridDirections
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

structure SemidirectedSwitching (N : RootedBinary V E X) (ports : RootPorts N) where
  keep : SuppressedEdge N → Prop
  ordinary : ∀ e, suppressedMark N ports e = .undirected → keep e
  hybrid_unique : ∀ v : SuppressedVertex N, MarkedHybrid N ports v →
    ∃ e, MarkedIncoming N ports e v ∧ keep e ∧
      ∀ f, MarkedIncoming N ports f v → keep f → f = e

noncomputable def originalKeep (N : RootedBinary V E X) (ports : RootPorts N)
    (M : SemidirectedSwitching N ports) (e : E) : Prop :=
  if N.graph.IsHybrid (N.graph.target e) then M.keep (parentImage N ports e) else True

/-- Original switching recovered from actual directed-edge deletion. -/
noncomputable def toRootedSwitching (N : RootedBinary V E X) (ports : RootPorts N)
    (M : SemidirectedSwitching N ports) : N.Switching where
  keep := originalKeep N ports M
  ordinary e hh := by simp [originalKeep,hh]
  hybrid_unique v hh := by
    let v' : SuppressedVertex N := ⟨v,G1RootSuppressionCutChildTransport.actual_hybrid_nonroot N v hh⟩
    obtain ⟨e,he,hkeep,hunique⟩ := M.hybrid_unique v'
      ((actual_marked_hybrid_iff_original N ports v').mpr hh)
    have ht := actual_original_parent_target N ports v' e he
    refine ⟨originalParent N ports e,ht,?_,?_⟩
    · simp [originalKeep,ht,hh,actual_parent_image_original_inverse,hkeep]
    · intro f hf hk
      have hhf : N.graph.IsHybrid (N.graph.target f) := hf ▸ hh
      have him := actual_parent_image_is_marked N ports v' hh f hf
      have hkeepf : M.keep (parentImage N ports f) := by simpa [originalKeep,hhf] using hk
      have hid := hunique (parentImage N ports f) him hkeepf
      have := congrArg (originalParent N ports) hid
      simpa only [actual_original_parent_image_inverse N ports f hhf] using this

noncomputable def suppressedKeep (N : RootedBinary V E X) (ports : RootPorts N) (S : N.Switching) :
    SuppressedEdge N → Prop
  | .inl e => S.keep e.val
  | .inr _ => S.keep ports.first ∧ S.keep ports.second

lemma actual_root_switching_ordinary_kept (N : RootedBinary V E X) (ports : RootPorts N) (S : N.Switching)
    (e : SuppressedEdge N) (hm : suppressedMark N ports e = .undirected) : suppressedKeep N ports S e := by
  cases e with
  | inl e =>
    have hh : ¬ N.graph.IsHybrid (N.graph.target e.val) := by
      by_cases hh : N.graph.IsHybrid (N.graph.target e.val)
      · simp [suppressedMark,hh] at hm
      · exact hh
    exact S.ordinary e.val hh
  | inr e =>
    cases e
    have hh := (actual_suppressed_edge_undirected_iff N ports).mp hm
    exact ⟨S.ordinary ports.first hh.1,S.ordinary ports.second hh.2⟩

/-- A marked parent is kept after suppression exactly when its one original
hybrid-parent ID is kept. The companion ordinary root arc is automatically
retained; it is never wrongly deleted in the rooted lift. -/
lemma actual_marked_parent_keep (N : RootedBinary V E X) (ports : RootPorts N) (S : N.Switching)
    (v : SuppressedVertex N) (e : SuppressedEdge N) (hm : MarkedIncoming N ports e v) :
    suppressedKeep N ports S e ↔ S.keep (originalParent N ports e) := by
  cases e with
  | inl e => rfl
  | inr e =>
    cases e
    rcases hm with ⟨hmark,ht⟩ | ⟨hmark,hs⟩
    · have hh := (actual_suppressed_edge_towards_second_iff N ports).mp hmark
      have hf : ¬ N.graph.IsHybrid (N.graph.target ports.first) := fun h =>
        actual_root_has_at_most_one_hybrid_child N ports ⟨h,hh⟩
      simp [suppressedKeep,originalParent,hf,S.ordinary ports.first hf]
    · have hh := (actual_suppressed_edge_towards_first_iff N ports).mp hmark
      have hs : ¬ N.graph.IsHybrid (N.graph.target ports.second) := fun h =>
        actual_root_has_at_most_one_hybrid_child N ports ⟨hh,h⟩
      simp [suppressedKeep,originalParent,hh,S.ordinary ports.second hs]

/-- Every original rooted switching gives the actual delete-one-per-marked-
hybrid switching of its root-suppressed semidirected partner. -/
noncomputable def toSemidirectedSwitching (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) : SemidirectedSwitching N ports where
  keep := suppressedKeep N ports S
  ordinary := actual_root_switching_ordinary_kept N ports S
  hybrid_unique v hv := by
    have hh := (actual_marked_hybrid_iff_original N ports v).mp hv
    obtain ⟨e,ht,hkeep,hunique⟩ := S.hybrid_unique v.val hh
    have hm := actual_parent_image_is_marked N ports v hh e ht
    refine ⟨parentImage N ports e,hm,?_,?_⟩
    · apply (actual_marked_parent_keep N ports S v _ hm).mpr
      rwa [actual_original_parent_image_inverse N ports e (ht ▸ hh)]
    · intro f hf hk
      have htarget := actual_original_parent_target N ports v f hf
      have hkeepf := (actual_marked_parent_keep N ports S v f hf).mp hk
      have he := hunique (originalParent N ports f) htarget hkeepf
      have := congrArg (parentImage N ports) he
      simpa only [actual_parent_image_original_inverse] using this

#print axioms toRootedSwitching
#print axioms toSemidirectedSwitching
end G1LiteralSemidirectedSwitchingTransport
