import ClosestPathAncestry

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration, execution or kernel check.

Complete shared-separator SUFFICIENCY for the original selected-MAG source
class. The two sources may have different arbitrary latent and selection
carriers. No bounded source, generic MAG realization, collider-order oracle,
common-discriminating-path oracle, or Markov-equivalence premise is used.

Classical attribution: Ali--Richardson--Spirtes (2009), closest-path proof
of sufficiency and Theorem 4.1 (the latter attributed there to Spirtes--
Richardson 1997); Richardson--Spirtes (2002), selected-DAG/MAG representation.
This specialization is not claimed as a new equivalence characterization.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation HPLTarget DiscriminatingStatus WeakInducing

universe u v w v' w'

theorem shared_separators_symmetric {V : Type u} (G H : MarkedGraph V)
    (skeleton : ∀ x y, Adjacent G x y ↔ Adjacent H x y)
    (shared : SharedSeparators G H) : SharedSeparators H G := by
  intro x y distinct nonedge
  obtain ⟨Z, notX, notY, sepG, sepH⟩ :=
    shared x y distinct (fun adjacent => nonedge ((skeleton x y).mp adjacent))
  exact ⟨Z, notX, notY, sepH, sepG⟩

theorem shared_separators_connection_forward {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X) (lawsH : AncestralLaws H)
    (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent H a b)
    (shared : SharedSeparators (mag D) H)
    (Z : X → Prop) (x y : X) (notStart : ¬ Z x) (notEnd : ¬ Z y)
    (connected : ActiveConnection (mag D) Z x y) : ActiveConnection H Z x y := by
  obtain ⟨vertices, closest⟩ := exists_closest (mag D) (mag_single_edges D) Z x y connected
  exact vertex_path_active_connection H singleH Z x y
    (closest_path_transfers D H lawsH singleH skeleton shared Z x y closest notStart notEnd)

/-- Both directions are proved from the SAME shared-separator certificate.
The reverse direction applies the same actual-source theorem to D', rather
than assuming a generic ancestral graph has a suitable source realization. -/
theorem shared_separators_mag_connection_iff
    {X : Type u} {S : Type v} {L : Type w} {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (D' : SourceDAG X S' L')
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent (mag D') a b)
    (shared : SharedSeparators (mag D) (mag D'))
    (Z : X → Prop) (x y : X) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    ActiveConnection (mag D) Z x y ↔ ActiveConnection (mag D') Z x y := by
  constructor
  · exact shared_separators_connection_forward D (mag D') (literal_mag_valid D').1
      (mag_single_edges D') skeleton shared Z x y notStart notEnd
  · exact shared_separators_connection_forward D' (mag D) (literal_mag_valid D).1
      (mag_single_edges D) (fun a b => (skeleton a b).symm)
      (shared_separators_symmetric (mag D) (mag D') skeleton shared) Z x y notStart notEnd

/-- The unchanged original-source consequence: all observed endpoint and
conditioning-set connection statements agree after selection. Selection
vertices stay conditioned and latent vertices stay unobserved in BOTH
original sources. Their two carriers need not coincide or have equal size. -/
theorem shared_separators_selected_source_connection_iff
    {X : Type u} {S : Type v} {L : Type w} {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (D' : SourceDAG X S' L')
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent (mag D') a b)
    (shared : SharedSeparators (mag D) (mag D'))
    (Z : X → Prop) (x y : X) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
      ActiveConnection (arrowGraph D'.arrow) (SelectedCondition Z) (Observed x) (Observed y) :=
  (selected_mag_connection_iff D Z x y notStart notEnd).trans
    ((shared_separators_mag_connection_iff D D' skeleton shared Z x y notStart notEnd).trans
      (selected_mag_connection_iff D' Z x y notStart notEnd).symm)

end RestrictedCausal.VertexActivePaths
