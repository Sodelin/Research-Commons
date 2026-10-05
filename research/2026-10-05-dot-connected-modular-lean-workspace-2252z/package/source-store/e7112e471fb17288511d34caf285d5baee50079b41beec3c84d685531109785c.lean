import G1InjectiveHalfArcSubdivision

/-! Subdivide the actual suppressed root edge at its interior midpoint to
recover the given original rooted graph. The midpoint is not a retained
vertex; old parallel curves and original labelled points stay unchanged. -/
namespace G1OriginalRootSubdivisionData
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1OuterLabelledMultigraphCurves G1InjectiveHalfArcSubdivision Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def rootPoint (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) : Plane := D.arc (.inr ()) halfTime
noncomputable def liftPoint (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (v : V) : Plane :=
  if hv : v = N.root then rootPoint N ports D else D.point ⟨v,hv⟩

@[simp] theorem liftPoint_root (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) : liftPoint N ports D N.root = rootPoint N ports D := by
  simp [liftPoint]
@[simp] theorem liftPoint_nonroot (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (v : V) (hv : v ≠ N.root) :
    liftPoint N ports D v = D.point ⟨v,hv⟩ := by simp [liftPoint,hv]

lemma actual_midpoint_not_kept_vertex (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (v : SuppressedVertex N) :
    rootPoint N ports D ≠ D.point v := by
  intro he
  have hi := D.arc_injective (.inr ())
  rcases D.vertex_incidence (.inr ()) v halfTime he with hs | ht
  · have hp : D.arc (.inr ()) halfTime = D.arc (.inr ()) 0 := by
      exact he.trans ((congrArg D.point hs).trans (D.arc (.inr ())).source.symm)
    exact halfTime_ne_zero (hi hp)
  · have hp : D.arc (.inr ()) halfTime = D.arc (.inr ()) 1 := by
      exact he.trans ((congrArg D.point ht).trans (D.arc (.inr ())).target.symm)
    exact halfTime_ne_one (hi hp)

theorem actual_lift_point_injective (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) : Function.Injective (liftPoint N ports D) := by
  intro v w he
  by_cases hv : v = N.root
  · subst v
    by_cases hw : w = N.root
    · exact hw.symm
    · exact False.elim (actual_midpoint_not_kept_vertex N ports D ⟨w,hw⟩ (by simpa [hw] using he))
  · by_cases hw : w = N.root
    · subst w
      exact False.elim (actual_midpoint_not_kept_vertex N ports D ⟨v,hv⟩ (by simpa [hv] using he.symm))
    · exact congrArg Subtype.val (D.point_injective (by simpa [hv,hw] using he))

noncomputable def firstRootArc (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) :
    Path (liftPoint N ports D (N.graph.source ports.first)) (liftPoint N ports D (N.graph.target ports.first)) :=
  (leftHalf (D.arc (.inr ()))).symm.cast
    (by simp [ports.source_first,rootPoint])
    (by simp [liftPoint,N.edge_target_ne_root, suppressedGraph,firstChild])
noncomputable def secondRootArc (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) :
    Path (liftPoint N ports D (N.graph.source ports.second)) (liftPoint N ports D (N.graph.target ports.second)) :=
  (rightHalf (D.arc (.inr ()))).cast
    (by simp [ports.source_second,rootPoint])
    (by simp [liftPoint,N.edge_target_ne_root, suppressedGraph,secondChild])
noncomputable def keptRootArc (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : KeptEdge N) :
    Path (liftPoint N ports D (N.graph.source e.val)) (liftPoint N ports D (N.graph.target e.val)) :=
  (D.arc (.inl e)).cast
    (by simp [liftPoint,e.property,suppressedGraph,keptSource])
    (by simp [liftPoint,N.edge_target_ne_root,suppressedGraph,keptTarget])

noncomputable def liftArc (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : E) :
    Path (liftPoint N ports D (N.graph.source e)) (liftPoint N ports D (N.graph.target e)) := by
  by_cases hf : e = ports.first
  · subst e; exact firstRootArc N ports D
  · by_cases hs : e = ports.second
    · subst e; exact secondRootArc N ports D
    · have hn : N.graph.source e ≠ N.root := by
        intro hroot
        exact (ports.exhaustive e hroot).elim hf hs
      exact keptRootArc N ports D ⟨e,hn⟩

@[simp] theorem liftArc_first (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) :
    liftArc N ports D ports.first = firstRootArc N ports D := by simp [liftArc]
@[simp] theorem liftArc_second (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) :
    liftArc N ports D ports.second = secondRootArc N ports D := by simp [liftArc,Ne.symm ports.different]
@[simp] theorem liftArc_kept (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : KeptEdge N) :
    liftArc N ports D e.val = keptRootArc N ports D e := by
  have hf : e.val ≠ ports.first := fun h => e.property (h ▸ ports.source_first)
  have hs : e.val ≠ ports.second := fun h => e.property (h ▸ ports.source_second)
  simp [liftArc,hf,hs]

#print axioms actual_lift_point_injective
end G1OriginalRootSubdivisionData
