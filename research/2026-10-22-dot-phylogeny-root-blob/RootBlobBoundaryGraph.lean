import RootBlobEdgeSubdivision
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Max

/-!
# From the original two boundary edges to ancestry
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No execution, elaboration or kernel verification.

The input is a hidden, actual-root-containing region with exactly two edge
occurrences crossing its boundary. Ancestry is proved, not assumed. In the
maximal root-2-blob application the number two counts boundary EDGES, not
Brits' broader printed two-boundary-VERTEX condition. No semidirected root
lifting or parallel-collapse convention is asserted by this module.
-/

open RootBlobEdgeIndexed
namespace RootBlobBoundaryGraph
universe v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable (G : Network V E O)

def Arc (u v : V) : Prop := ∃ e, G.source e = u ∧ G.target e = v
def Reaches (u v : V) : Prop := Relation.ReflTransGen (Arc G) u v

theorem rank_mono (hG : GraphAdmitted G) {u v : V} (h : Reaches G u v) :
    G.rank u ≤ G.rank v := by
  induction h with
  | refl => exact le_rfl
  | @tail b c hab hbc ih =>
    obtain ⟨e, hs, ht⟩ := hbc
    exact le_trans ih (le_of_lt (by simpa [hs, ht] using hG.2.2.1 e))

/-- Unique-root admission and strict rank imply actual root reachability. -/
theorem root_reaches (hG : GraphAdmitted G) (v : V) : Reaches G G.root v := by
  have aux : ∀ n : ℕ, ∀ v : V, G.rank v = n → Reaches G G.root v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hr : v = G.root
      · subst v
        exact Relation.ReflTransGen.refl
      · obtain ⟨e, he⟩ := hG.2.2.2.2.1 v hr
        have hl : G.rank (G.source e) < n := by
          simpa [he, hv] using hG.2.2.1 e
        exact (ih _ hl _ rfl).tail ⟨e, rfl, he⟩
  exact aux _ v rfl

/-- Every vertex reaches an observed global sink. This uses finiteness,
not an assumption of terminal independence or a new graph axiom. -/
theorem reaches_observed (hG : GraphAdmitted G) (v : V) :
    ∃ o, Reaches G v (G.observed o) := by
  classical
  let F : Finset V := Finset.univ.filter (Reaches G v)
  have hv : v ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image F G.rank ⟨v, hv⟩
  have hvm : Reaches G v m := (Finset.mem_filter.mp hm).2
  have hsink : ∀ e, G.source e ≠ m := by
    intro e he
    have ht : G.target e ∈ F := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hvm.tail ⟨e, he, rfl⟩⟩
    have hle := hmax _ ht
    have hlt := hG.2.2.1 e
    rw [he] at hlt
    exact (not_lt_of_ge hle) hlt
  obtain ⟨o, ho⟩ := (hG.2.2.2.2.2 m).mp hsink
  exact ⟨o, by simpa [ho] using hvm⟩

def Outgoing (R : Set V) (e : E) : Prop := G.source e ∈ R ∧ G.target e ∉ R
def Incoming (R : Set V) (e : E) : Prop := G.source e ∉ R ∧ G.target e ∈ R
def Boundary (R : Set V) (e : E) : Prop := Outgoing G R e ∨ Incoming G R e

noncomputable def boundaryEdges (R : Set V) : Finset E := by
  classical
  exact Finset.univ.filter (Boundary G R)

/-- An enumerated pair is constructed below from the cardinality condition. -/
structure BoundaryPair (R : Set V) where
  first : E
  second : E
  distinct : first ≠ second
  cover : ∀ e, Boundary G R e ↔ e = first ∨ e = second

noncomputable def boundaryPair_of_card (R : Set V)
    (hc : (boundaryEdges G R).card = 2) : BoundaryPair G R := by
  classical
  let a := Classical.choose (Finset.card_eq_two.mp hc)
  have ha := Classical.choose_spec (Finset.card_eq_two.mp hc)
  let b := Classical.choose ha
  have hb := Classical.choose_spec ha
  have hab : a ≠ b := hb.1
  have hs : boundaryEdges G R = {a, b} := hb.2
  refine ⟨a, b, hab, ?_⟩
  intro e
  have hm : Boundary G R e ↔ e ∈ boundaryEdges G R := by
    simp [boundaryEdges]
  rw [hm, hs]
  simp

/-- An exiting occurrence on a path has the endpoint rank bounds needed
for the directed excursion argument. It need not be a global bridge. -/
theorem exit_on_path (hG : GraphAdmitted G) (R : Set V)
    {u : V} (hu : u ∈ R) : ∀ {v : V}, Reaches G u v → v ∉ R →
      ∃ e, Outgoing G R e ∧ G.rank u ≤ G.rank (G.source e) ∧
        G.rank (G.target e) ≤ G.rank v := by
  intro v h
  induction h with
  | refl =>
    intro hn
    exact False.elim (hn hu)
  | @tail b c hab hbc ih =>
    intro hc
    obtain ⟨e, hs, ht⟩ := hbc
    by_cases hb : b ∈ R
    · refine ⟨e, ⟨by simpa [hs] using hb, by simpa [ht] using hc⟩, ?_, ?_⟩
      · simpa [hs] using rank_mono G hG hab
      · simp [ht]
    · obtain ⟨f, hf, huf, hfb⟩ := ih hb
      refine ⟨f, hf, huf, le_trans hfb ?_⟩
      exact le_of_lt (by simpa [hs, ht] using hG.2.2.1 e)

theorem outgoing_unique_if_incoming {R : Set V} (P : BoundaryPair G R)
    {e f g : E} (he : Incoming G R e) (hf : Outgoing G R f)
    (hg : Outgoing G R g) : f = g := by
  have hef : e ≠ f := by intro h; subst f; exact he.1 hf.1
  have heg : e ≠ g := by intro h; subst g; exact he.1 hg.1
  rcases (P.cover e).mp (Or.inr he) with he0 | he1 <;>
    rcases (P.cover f).mp (Or.inl hf) with hf0 | hf1 <;>
    rcases (P.cover g).mp (Or.inl hg) with hg0 | hg1 <;> aesop

/-- The actual-root/two-edge excursion lemma. This is stronger than the
maximal-blob case, but does not assert that a semidirected sub-blob lifts
to these hypotheses. -/
theorem ancestral_of_two_boundary (hG : GraphAdmitted G) (R : Set V)
    (hroot : G.root ∈ R) (hidden : ∀ o, G.observed o ∉ R)
    (P : BoundaryPair G R) : ∀ e, G.target e ∈ R → G.source e ∈ R := by
  intro e ht
  by_contra hs
  have he : Incoming G R e := ⟨hs, ht⟩
  obtain ⟨f, hf, _, hfu⟩ := exit_on_path G hG R hroot
    (root_reaches G hG (G.source e)) hs
  obtain ⟨o, hpath⟩ := reaches_observed G hG (G.target e)
  obtain ⟨g, hg, hvg, _⟩ := exit_on_path G hG R ht hpath (hidden o)
  have hfg := outgoing_unique_if_incoming G P he hf hg
  subst g
  have he_rank := hG.2.2.1 e
  have hf_rank := hG.2.2.1 f
  omega

/-- Source-level region input. In particular, ancestry and two internal
sinks are NOT fields. Maximality is unnecessary once this literal edge
boundary contract has been checked. -/
structure RootTwoBoundaryRegion where
  vertices : Set V
  root_mem : G.root ∈ vertices
  hidden : ∀ o, G.observed o ∉ vertices
  boundary_card : (boundaryEdges G vertices).card = 2

variable {G}
variable (R : RootTwoBoundaryRegion G)
noncomputable def pair : BoundaryPair G R.vertices :=
  boundaryPair_of_card G R.vertices R.boundary_card

theorem ancestral (hG : GraphAdmitted G) :
    ∀ e, G.target e ∈ R.vertices → G.source e ∈ R.vertices :=
  ancestral_of_two_boundary G hG R.vertices R.root_mem R.hidden R.pair

theorem boundary_outgoing (hG : GraphAdmitted G) {e : E}
    (he : Boundary G R.vertices e) : Outgoing G R.vertices e := by
  rcases he with h | h
  · exact h
  · exact False.elim (h.1 (R.ancestral hG e h.2))

theorem first_outgoing (hG : GraphAdmitted G) :
    Outgoing G R.vertices R.pair.first :=
  R.boundary_outgoing hG ((R.pair.cover _).mpr (Or.inl rfl))

theorem second_outgoing (hG : GraphAdmitted G) :
    Outgoing G R.vertices R.pair.second :=
  R.boundary_outgoing hG ((R.pair.cover _).mpr (Or.inr rfl))

end RootBlobBoundaryGraph
