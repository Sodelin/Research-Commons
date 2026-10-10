import G1SplicedSourceAdmission

/-!
# Finite actual nonroot-two-port graph normalization

Contributor: dot, 2026-10-03. The state bundles the literal admitted graph,
its cut-child proof and calendar. Each reduction is the previously derived
actual splice, not a supplied reduced graph. Strong induction on the ACTUAL
vertex carrier produces a finite normalization witness. Synthetic edges
remain decorated and are not assigned invented demographic scalars.
-/
namespace G1ActualGraphNormalization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1CutChildPorts G1ActualTwoPortBlob G1BigonSpliceGraph
open G1SplicedSourceAdmission
open scoped Classical
universe u v w

structure Source (X : Type w) [Fintype X] where
  Vertex : Type u
  Edge : Type v
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  vertexDecidable : DecidableEq Vertex
  edgeDecidable : DecidableEq Edge
  network : @RootedBinary Vertex Edge X vertexFintype edgeFintype _ vertexDecidable
  cutChild : @CutChild Vertex Edge X vertexFintype edgeFintype _ vertexDecidable network
  calendar : Calendar network.graph

attribute [instance] Source.vertexFintype Source.edgeFintype Source.vertexDecidable Source.edgeDecidable

variable {X : Type w} [Fintype X]

noncomputable def admit {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) : Source.{u,v,w} X where
  Vertex := V
  Edge := E
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  vertexDecidable := inferInstance
  edgeDecidable := inferInstance
  network := N
  cutChild := hc
  calendar := C

def Reduced (S : Source X) : Prop :=
  ∀ b : S.network.graph.Blob, b ≠ S.network.graph.blobOf S.network.root →
    Fintype.card (S.network.BlobPort b) ≠ 2

noncomputable def splice (S : Source X) (b : S.network.graph.Blob)
    (hb : b ≠ S.network.graph.blobOf S.network.root)
    (hp : Fintype.card (S.network.BlobPort b) = 2) : Source X :=
  let A := extractedBigon S.network S.cutChild b hb ((actual_quotient_port_card S.network b).symm.trans hp)
  admit (splicedNetwork S.network S.cutChild b hb A)
    (actual_spliced_cut_child S.network S.cutChild b hb A)
    (splicedCalendar S.network S.cutChild b hb A S.calendar)

/-- A step stores only the original offending blob and equality to the
constructed splice. It never takes a desired output graph or law as evidence. -/
inductive Step : Source.{u,v,w} X → Source.{u,v,w} X → Prop
  | splice (S : Source X) (b : S.network.graph.Blob)
      (hb : b ≠ S.network.graph.blobOf S.network.root)
      (hp : Fintype.card (S.network.BlobPort b) = 2) : Step S (splice S b hb hp)

abbrev Steps := Relation.ReflTransGen (Step (X:=X))

theorem actual_step_vertex_decrement {S T : Source X} (h : Step S T) :
    Fintype.card T.Vertex + 2 = Fintype.card S.Vertex := by
  cases h with
  | splice b hb hp =>
      exact actual_splice_vertex_decrement S.network b (extractedBigon S.network S.cutChild b hb ((actual_quotient_port_card S.network b).symm.trans hp))

theorem actual_step_edge_decrement {S T : Source X} (h : Step S T) :
    Fintype.card T.Edge + 3 = Fintype.card S.Edge := by
  cases h with
  | splice b hb hp =>
      exact actual_splice_edge_decrement S.network b (extractedBigon S.network S.cutChild b hb ((actual_quotient_port_card S.network b).symm.trans hp))

theorem actual_step_strictly_smaller {S T : Source X} (h : Step S T) :
    Fintype.card T.Vertex < Fintype.card S.Vertex := by
  have hd := actual_step_vertex_decrement h
  omega

/-- Every actual binary LSA cut-child calendar source reaches a literal
reduced source through finitely many CONSTRUCTED nonroot blob splices. -/
theorem actual_finite_normalization (S : Source.{u,v,w} X) :
    ∃ T : Source X, Steps S T ∧ Reduced T := by
  have aux : ∀ n : ℕ, ∀ S : Source X, Fintype.card S.Vertex = n →
      ∃ T : Source X, Steps S T ∧ Reduced T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn
        by_cases hr : Reduced S
        · exact ⟨S,Relation.ReflTransGen.refl,hr⟩
        · unfold Reduced at hr
          push_neg at hr
          obtain ⟨b,hb,hp⟩ := hr
          let T := splice S b hb hp
          have hs : Step S T := Step.splice S b hb hp
          have ht : Fintype.card T.Vertex < n := hn ▸ actual_step_strictly_smaller hs
          obtain ⟨U,hTU,hU⟩ := ih (Fintype.card T.Vertex) ht T rfl
          exact ⟨U,(Relation.ReflTransGen.single hs).trans hTU,hU⟩
  exact aux _ S rfl

end G1ActualGraphNormalization
