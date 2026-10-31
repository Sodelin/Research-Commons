import CycleBoundaryIDs
import RawPortCycle
import NanuqActualGalledChildBridge

/-! SOURCE-ONLY DRAFT, UNCOMPILED. The old GalledDetour interface here is the
existing rooted admission stage, not an added canonical manuscript premise.
The marked semidirected-to-chosen-partner bridge remains separately tracked. -/
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set
open scoped Graph Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

/-- At a raw hybrid, an incident raw ID must be incoming: an outgoing ID is
an original bridge, whereas BlobEdge retains original nonbridge IDs only. -/
theorem raw_hybrid_incident_incoming (hg : N.graph.GalledDetour)
    (h : BlobVertex N.graph b) (hh : N.graph.IsHybrid h.val)
    (f : BlobEdge N.graph b)
    (hi : (graph (blobCurves D b)).Inc f (vertex (blobCurves D b) h)) :
    N.graph.target f.val=h.val := by
  have hl : (graph (blobCurves D b)).IsLink f
      (vertex (blobCurves D b) ((originalBlob N.graph b).source f))
      (vertex (blobCurves D b) ((originalBlob N.graph b).target f)) := Or.inl ⟨rfl,rfl⟩
  rcases hi.eq_or_eq_of_isLink hl with hs | ht
  · have hs' : h.val=N.graph.source f.val :=
      congrArg Subtype.val (vertex_injective (blobCurves D b) hs)
    exact False.elim (f.property.1 (N.actual_galled_hybrid_child_is_bridge hg f.val (hs' ▸ hh)))
  · exact (congrArg Subtype.val (vertex_injective (blobCurves D b) ht)).symm

/-- Every incoming original ID at a hybrid on this named raw boundary is
on this SAME cycle. Its membership is derived, not assumed as a new gall. -/
theorem raw_cycle_contains_all_hybrid_incoming (hg : N.graph.GalledDetour)
    (h : BlobVertex N.graph b) (hh : N.graph.IsHybrid h.val)
    {e₀ : BlobEdge N.graph b} {u v : Schoenflies.Plane} {es : List (BlobEdge N.graph b)}
    (hc : (graph (blobCurves D b)).IsCycleThrough e₀ u v es)
    (hcover : vertex (blobCurves D b) h ∈ Graph.edgesCover (curve (blobCurves D b)) (e₀::es)) :
    ∀ e : E, N.graph.target e=h.val →
      ∃ f : BlobEdge N.graph b, f.val=e ∧ f∈e₀::es := by
  have hv : vertex (blobCurves D b) h ∈ V(graph (blobCurves D b)) := ⟨h,rfl⟩
  obtain ⟨f,g,hfg,hf,hgmem,hfi,hgi⟩ := cycle_two_incident_ids
    (isDrawing (blobCurves D b)) hc hv hcover
  have hft := raw_hybrid_incident_incoming N D b hg h hh f hfi
  have hgt := raw_hybrid_incident_incoming N D b hg h hh g hgi
  have hval : f.val≠g.val := fun he => hfg (Subtype.ext he)
  let incoming := Finset.univ.filter (fun e : E => N.graph.target e=h.val)
  have hcard : incoming.card=2 := hh.1
  have hsubset : ({f.val,g.val}:Finset E) ⊆ incoming := by
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · subst e; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hft⟩
    · have he' : e=g.val := Finset.mem_singleton.mp he
      subst e; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgt⟩
  have heq : ({f.val,g.val}:Finset E)=incoming :=
    Finset.eq_of_subset_of_card_le hsubset (by simpa [hval] using hcard.le)
  intro e he
  have hem : e∈({f.val,g.val}:Finset E) := heq.symm ▸
    (show e∈incoming from Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  rcases Finset.mem_insert.mp hem with hef | heg
  · exact ⟨f,hef.symm,hf⟩
  · exact ⟨g,(Finset.mem_singleton.mp heg).symm,hgmem⟩

/-- The hybrid's actual outgoing bridge supplies one of the ORIGINAL blob
ports, so the accepted all-port boundary cover applies to that hybrid. -/
theorem hybrid_on_all_port_cover (hg : N.graph.GalledDetour)
    (h : BlobVertex N.graph b) (hh : N.graph.IsHybrid h.val)
    {C : Set Schoenflies.Plane}
    (hports : ∀ p : N.BlobPort b,
      coordinates (D.point (N.originalPortInner b p).val)∈C) :
    vertex (blobCurves D b) h∈C := by
  have hpos : 0<(Finset.univ.filter (fun e : E => N.graph.source e=h.val)).card := by
    change 0<N.graph.outDegree h.val
    rw [hh.2]
    omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
  have hs : N.graph.source e=h.val := (Finset.mem_filter.mp he).2
  have hbridge := N.actual_galled_hybrid_child_is_bridge hg e (hs.symm ▸ hh)
  have hb : N.graph.bridgeQuotient.source ⟨e,hbridge⟩=b := by
    change N.graph.blobOf (N.graph.source e)=b
    rw [hs]
    exact h.property
  let p : N.BlobPort b := ⟨⟨e,hbridge⟩,Or.inl hb⟩
  have hinner : (N.originalPortInner b p).val=h.val :=
    (N.originalPortInner_value_outgoing b p hb).trans hs
  have hp := hports p
  rw [hinner] at hp
  exact hp

/-- Source-facing boundary-ID export for the >=3 raw-vertex case. The old
raw outer-cycle supplier and actual original gall/port facts discharge ALL
cycle-incidence premises. Bigon and singleton adapters remain separate. -/
theorem actual_raw_outer_cycle_all_hybrid_incoming (hg : N.graph.GalledDetour)
    (hb : N.NonleafBlob b) (face : TaxonOuterFace D N.leaf)
    (hthree : ∃ a c d : BlobVertex N.graph b, a≠c ∧ a≠d ∧ c≠d) :
    ∃ (e₀ : BlobEdge N.graph b) (u v : Schoenflies.Plane)
      (es : List (BlobEdge N.graph b)),
      Graph.IsFaceCycle (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside) e₀ u v es ∧
      Schoenflies.IsJordanCurve (Graph.edgesCover (curve (blobCurves D b)) (e₀::es)) ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b)) (coordinates face.outside)=
        Schoenflies.outside (Graph.edgesCover (curve (blobCurves D b)) (e₀::es)) ∧
      (∀ p : N.BlobPort b, coordinates (D.point (N.originalPortInner b p).val)∈
        Graph.edgesCover (curve (blobCurves D b)) (e₀::es)) ∧
      ∀ h : BlobVertex N.graph b, N.graph.IsHybrid h.val →
        ∀ e : E, N.graph.target e=h.val →
          ∃ f : BlobEdge N.graph b, f.val=e ∧ f∈e₀::es := by
  obtain ⟨e₀,u,v,es,hface,hC,houtside,hports⟩ :=
    Nanuq.RawPortFrontier.actual_raw_port_outer_cycle N D b hb face hthree
  refine ⟨e₀,u,v,es,hface,hC,houtside,hports,?_⟩
  intro h hh
  exact raw_cycle_contains_all_hybrid_incoming N D b hg h hh hface.isCycle
    (hybrid_on_all_port_cover N D b hg h hh hports)
end Nanuq.OpenedCore
