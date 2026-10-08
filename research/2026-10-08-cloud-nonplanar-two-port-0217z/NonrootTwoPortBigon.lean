import BlobIncidentPorts
import GraphSwitching
import GraphLeaves
import G6BridgeCannotEnterHybrid
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
Actual nonroot two-port blob classification, Cloud structural source lane.
8 October 2026, 02:17 UTC. COMPILER UNCHECKED, outside sole166.

The actual bridge-deleted quotient, original edge occurrences, source degree
fibres and explicit original child-cut premise derive the two-arm bigon.
No supplied decomposition, size bound, bigon witness or target equality.
The preceding HybridChildPorts/BlobIncidentPorts sources remain read-only.
Q/S suppression and the complete nonplanar G6 endpoint are separate.
-/

namespace UnifiedLean.G6.NonrootTwoPortBigon

open Nanuq.Source BlobIncidentPorts
open scoped BigOperators

universe u v w
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

noncomputable def vertices (N : RootedBinary V E X) (b : N.graph.Blob) : Finset V := by
  classical
  exact Finset.univ.filter (fun a => N.graph.blobOf a = b)

@[simp] theorem mem_vertices (N : RootedBinary V E X) (b : N.graph.Blob) (a : V) :
    a ∈ vertices N b ↔ N.graph.blobOf a = b := by
  classical
  simp [vertices]

theorem vertices_nonempty (N : RootedBinary V E X) (b : N.graph.Blob) :
    (vertices N b).Nonempty := by
  classical
  refine Quotient.inductionOn b ?_
  intro a
  exact ⟨a, by simp [vertices, EdgeGraph.blobOf]⟩

theorem leaf_no_outgoing (N : RootedBinary V E X) (x : X) (e : E)
    (he : N.graph.source e = N.leaf x) : False := by
  classical
  have hm : e ∈ Finset.univ.filter (fun f => N.graph.source f = N.leaf x) := by
    simp [he]
  have hp : 0 < N.graph.outDegree (N.leaf x) := Finset.card_pos.mpr ⟨e, hm⟩
  rw [(N.leaf_degrees x).2] at hp
  exact Nat.lt_irrefl 0 hp

/-- Every adjacency at a labelled leaf uses its one actual incoming occurrence. -/
theorem leaf_incidence_unique (N : RootedBinary V E X) (x : X) (e : E)
    (he : N.graph.target e = N.leaf x) {a : V} {f : E}
    (hf : N.graph.Inc f (N.leaf x) a) : f = e := by
  obtain ⟨g, hg, hu⟩ := N.incoming_unique_of_indegree_one (N.leaf_degrees x).1
  rcases hf with ⟨hs, _⟩ | ⟨_, ht⟩
  · exact False.elim (leaf_no_outgoing N x f hs)
  · exact (hu f ht).trans (hu e he).symm

/-- Avoiding the unique incoming occurrence cannot leave its leaf endpoint. -/
theorem leaf_incoming_isBridge (N : RootedBinary V E X) (x : X) (e : E)
    (he : N.graph.target e = N.leaf x) : N.graph.IsBridge e := by
  intro hdetour
  have hclosed : ∀ ⦃a c⦄, N.graph.UStep (fun f => f ≠ e) a c →
      a = N.leaf x → c = N.leaf x := by
    intro a c hstep ha
    obtain ⟨f, hfe, hinc⟩ := hstep
    rw [ha] at hinc
    exact False.elim (hfe (leaf_incidence_unique N x e he hinc))
  have hsame : N.graph.source e = N.leaf x := N.graph.ureach_preserves hclosed
    (N.graph.ureach_symm hdetour) he
  exact N.graph.acyclic_no_loop N.acyclic e (hsame.trans he.symm)

/-- A labelled leaf's actual nonbridge component is its singleton. -/
theorem sameBlob_leaf_eq (N : RootedBinary V E X) (x : X) {a : V}
    (ha : N.graph.SameBlob (N.leaf x) a) : a = N.leaf x := by
  obtain ⟨e, he, _⟩ := N.incoming_unique_of_indegree_one (N.leaf_degrees x).1
  have hb := leaf_incoming_isBridge N x e he
  have hclosed : ∀ ⦃c d⦄, N.graph.UStep (fun f => ¬ N.graph.IsBridge f) c d →
      c = N.leaf x → d = N.leaf x := by
    intro c d hstep hc
    obtain ⟨f, hf, hinc⟩ := hstep
    rw [hc] at hinc
    have hfe := leaf_incidence_unique N x e he hinc
    exact False.elim (hf (hfe.symm ▸ hb))
  exact N.graph.ureach_preserves hclosed ha rfl

theorem outgoing_card_twoport_one (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : Nat.card (IncidentPorts N b) = 2) :
    Nat.card (OutgoingPorts N b) = 1 := by
  have hi := incident_card_nonroot N b hb
  omega

/-- No labelled leaf belongs to an actual nonroot two-port blob. -/
theorem twoport_no_leaf (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : Nat.card (IncidentPorts N b) = 2)
    (x : X) : N.graph.blobOf (N.leaf x) ≠ b := by
  intro hx
  have hz : Nat.card (OutgoingPorts N b) = 0 := by
    apply Nat.card_eq_zero.mpr
    left
    refine ⟨fun e => ?_⟩
    have hs : N.graph.source e.val = N.leaf x := sameBlob_leaf_eq N x
      (Quotient.exact (hx.trans e.property.2.symm))
    exact leaf_no_outgoing N x e.val hs
  have ho := outgoing_card_twoport_one N b hb hp
  omega

/-- A bridge is exactly an occurrence crossing two actual blob classes. -/
theorem isBridge_iff_blob_ne (N : RootedBinary V E X) (e : E) :
    N.graph.IsBridge e ↔ N.graph.blobOf (N.graph.source e) ≠
      N.graph.blobOf (N.graph.target e) := by
  constructor
  · exact N.graph.bridge_blob_ne
  · intro hne
    by_contra hnb
    exact hne (Quotient.sound (N.graph.nonbridge_sameBlob hnb))

/-- Generic actual-edge fibre balance, valid for every finite vertex subset. -/
theorem finite_degree_balance (N : RootedBinary V E X) (s : Finset V) :
    (∑ a ∈ s, N.graph.outDegree a) +
      (Finset.univ.filter (fun e : E => N.graph.target e ∈ s ∧
        N.graph.source e ∉ s)).card =
    (∑ a ∈ s, N.graph.inDegree a) +
      (Finset.univ.filter (fun e : E => N.graph.source e ∈ s ∧
        N.graph.target e ∉ s)).card := by
  classical
  have hs := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
    s N.graph.source
  have ht := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
    s N.graph.target
  change (∑ a ∈ s, N.graph.outDegree a) =
    (Finset.univ.filter (fun e => N.graph.source e ∈ s)).card at hs
  change (∑ a ∈ s, N.graph.inDegree a) =
    (Finset.univ.filter (fun e => N.graph.target e ∈ s)).card at ht
  have hsp := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun e : E => N.graph.source e ∈ s))
    (fun e => N.graph.target e ∈ s)
  have htp := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun e : E => N.graph.target e ∈ s))
    (fun e => N.graph.source e ∈ s)
  simp only [Finset.filter_filter] at hsp
  simp only [Finset.filter_filter] at htp
  have hi : Finset.univ.filter (fun e : E => N.graph.target e ∈ s ∧
      N.graph.source e ∈ s) = Finset.univ.filter (fun e : E =>
      N.graph.source e ∈ s ∧ N.graph.target e ∈ s) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hi] at htp
  omega

theorem incoming_card_cut (N : RootedBinary V E X) (b : N.graph.Blob) :
    Nat.card (IncomingPorts N b) =
      (Finset.univ.filter (fun e : E => N.graph.target e ∈ vertices N b ∧
        N.graph.source e ∉ vertices N b)).card := by
  classical
  apply Nat.subtype_card
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_vertices,
    IncomingPorts]
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨(isBridge_iff_blob_ne N e).mpr ?_, ht⟩
    intro hst
    exact hs (hst.trans ht)
  · rintro ⟨he, ht⟩
    exact ⟨ht, fun hs => N.graph.bridge_blob_ne he (hs.trans ht.symm)⟩

theorem outgoing_card_cut (N : RootedBinary V E X) (b : N.graph.Blob) :
    Nat.card (OutgoingPorts N b) =
      (Finset.univ.filter (fun e : E => N.graph.source e ∈ vertices N b ∧
        N.graph.target e ∉ vertices N b)).card := by
  classical
  apply Nat.subtype_card
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_vertices,
    OutgoingPorts]
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨(isBridge_iff_blob_ne N e).mpr ?_, hs⟩
    intro hst
    exact ht (hst.symm.trans hs)
  · rintro ⟨he, hs⟩
    exact ⟨hs, fun ht => N.graph.bridge_blob_ne he (hs.trans ht.symm)⟩

theorem blob_degree_balance (N : RootedBinary V E X) (b : N.graph.Blob) :
    (∑ a ∈ vertices N b, N.graph.outDegree a) + Nat.card (IncomingPorts N b) =
    (∑ a ∈ vertices N b, N.graph.inDegree a) + Nat.card (OutgoingPorts N b) := by
  rw [incoming_card_cut, outgoing_card_cut]
  exact finite_degree_balance N (vertices N b)

noncomputable def ordinaryVertices (N : RootedBinary V E X) (b : N.graph.Blob) :
    Finset V := by
  classical
  exact (vertices N b).filter (fun a => ¬ N.graph.IsHybrid a)

noncomputable def hybridVertices (N : RootedBinary V E X) (b : N.graph.Blob) :
    Finset V := by
  classical
  exact (vertices N b).filter N.graph.IsHybrid

theorem hybrid_card (N : RootedBinary V E X) (b : N.graph.Blob) :
    Nat.card (HybridsInBlob N b) = (hybridVertices N b).card := by
  classical
  apply Nat.subtype_card
  intro a
  simp [hybridVertices, vertices, HybridsInBlob, and_comm]

theorem ordinary_vertex_degrees (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : Nat.card (IncidentPorts N b) = 2)
    {a : V} (ha : a ∈ ordinaryVertices N b) :
    N.graph.inDegree a = 1 ∧ N.graph.outDegree a = 2 := by
  classical
  have hm : N.graph.blobOf a = b := (mem_vertices N b a).mp
    (Finset.mem_filter.mp ha).1
  have hh : ¬ N.graph.IsHybrid a := (Finset.mem_filter.mp ha).2
  have hr : a ≠ N.root := by
    intro heq
    subst a
    exact hb hm.symm
  have hl : ∀ x, N.leaf x ≠ a := by
    intro x heq
    exact twoport_no_leaf N b hb hp x (by rw [heq]; exact hm)
  rcases N.internal_degrees a hr hl with ht | hhybrid
  · exact ht
  · exact False.elim (hh hhybrid)

/-- The degree sums use the actual ordinary/hybrid partition of the blob. -/
theorem twoport_degree_sums (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : Nat.card (IncidentPorts N b) = 2) :
    (∑ a ∈ vertices N b, N.graph.inDegree a) =
      (ordinaryVertices N b).card + 2 * (hybridVertices N b).card ∧
    (∑ a ∈ vertices N b, N.graph.outDegree a) =
      2 * (ordinaryVertices N b).card + (hybridVertices N b).card := by
  classical
  have hti := Finset.sum_const_nat (s := ordinaryVertices N b) (m := 1)
    (fun a ha => (ordinary_vertex_degrees N b hb hp ha).1)
  have hto := Finset.sum_const_nat (s := ordinaryVertices N b) (m := 2)
    (fun a ha => (ordinary_vertex_degrees N b hb hp ha).2)
  have hhi := Finset.sum_const_nat (s := hybridVertices N b) (m := 2)
    (fun a ha => ((Finset.mem_filter.mp ha).2 : N.graph.IsHybrid a).1)
  have hho := Finset.sum_const_nat (s := hybridVertices N b) (m := 1)
    (fun a ha => ((Finset.mem_filter.mp ha).2 : N.graph.IsHybrid a).2)
  have hpi := Finset.sum_filter_add_sum_filter_not (vertices N b)
    N.graph.IsHybrid N.graph.inDegree
  have hpo := Finset.sum_filter_add_sum_filter_not (vertices N b)
    N.graph.IsHybrid N.graph.outDegree
  change (∑ a ∈ hybridVertices N b, N.graph.inDegree a) +
    (∑ a ∈ ordinaryVertices N b, N.graph.inDegree a) =
    (∑ a ∈ vertices N b, N.graph.inDegree a) at hpi
  change (∑ a ∈ hybridVertices N b, N.graph.outDegree a) +
    (∑ a ∈ ordinaryVertices N b, N.graph.outDegree a) =
    (∑ a ∈ vertices N b, N.graph.outDegree a) at hpo
  constructor <;> omega

/-- No supplied internal count: balance, nonemptiness and actual child ports force one each. -/
theorem ordinary_hybrid_card_one (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (IncidentPorts N b) = 2) :
    (ordinaryVertices N b).card = 1 ∧ (hybridVertices N b).card = 1 := by
  classical
  have hbal := blob_degree_balance N b
  have hin := incoming_card_nonroot_one N b hb
  have hout := outgoing_card_twoport_one N b hb hp
  obtain ⟨hdi, hdo⟩ := twoport_degree_sums N b hb hp
  have hhyb := nonroot_hybrid_card_le_incident_sub_one N hcut b hb
  rw [hybrid_card] at hhyb
  have hpartition := Finset.card_filter_add_card_filter_not (s := vertices N b)
    N.graph.IsHybrid
  change (hybridVertices N b).card + (ordinaryVertices N b).card =
    (vertices N b).card at hpartition
  have hpos : 0 < (vertices N b).card := Finset.card_pos.mpr (vertices_nonempty N b)
  constructor <;> omega

/-- Derived genuine bigon: all vertices, both distinct original arm IDs,
all internal occurrences and the actual external entry/exit orientations. -/
theorem actual_nonroot_two_port_bigon (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (IncidentPorts N b) = 2) :
    ∃ r h : V, ∃ e₀ e₁ : E,
      r ≠ h ∧ (N.graph.inDegree r = 1 ∧ N.graph.outDegree r = 2) ∧
      N.graph.IsHybrid h ∧
      (∀ a, N.graph.blobOf a = b ↔ a = r ∨ a = h) ∧ e₀ ≠ e₁ ∧
      N.graph.source e₀ = r ∧ N.graph.target e₀ = h ∧
      N.graph.source e₁ = r ∧ N.graph.target e₁ = h ∧
      (∀ e, (N.graph.blobOf (N.graph.source e) = b ∧
        N.graph.blobOf (N.graph.target e) = b) ↔ e = e₀ ∨ e = e₁) ∧
      (∀ e, N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.target e) = b →
        N.graph.target e = r) ∧
      (∀ e, N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.source e) = b →
        N.graph.source e = h) := by
  classical
  have hc := ordinary_hybrid_card_one N hcut b hb hp
  obtain ⟨r, hr, hur⟩ := Finset.card_eq_one_iff_existsUnique.mp hc.1
  obtain ⟨h, hh, huh⟩ := Finset.card_eq_one_iff_existsUnique.mp hc.2
  have hrd := ordinary_vertex_degrees N b hb hp hr
  have hrb : N.graph.blobOf r = b := (mem_vertices N b r).mp
    (Finset.mem_filter.mp hr).1
  have hrnh : ¬ N.graph.IsHybrid r := (Finset.mem_filter.mp hr).2
  have hhb : N.graph.blobOf h = b := (mem_vertices N b h).mp
    (Finset.mem_filter.mp hh).1
  have hhyb : N.graph.IsHybrid h := (Finset.mem_filter.mp hh).2
  have hrh : r ≠ h := by
    intro heq
    exact hrnh (heq.symm ▸ hhyb)
  have hv : ∀ a, N.graph.blobOf a = b ↔ a = r ∨ a = h := by
    intro a
    constructor
    · intro hab
      have ham := (mem_vertices N b a).mpr hab
      by_cases hah : N.graph.IsHybrid a
      · exact Or.inr (huh a (Finset.mem_filter.mpr ⟨ham, hah⟩))
      · exact Or.inl (hur a (Finset.mem_filter.mpr ⟨ham, hah⟩))
    · rintro (har | hah)
      · exact har.symm ▸ hrb
      · exact hah.symm ▸ hhb
  have hi : ∀ e, N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.target e) = b →
      N.graph.target e = r := by
    intro e he
    rcases (hv (N.graph.target e)).mp he.2 with htr | hth
    · exact htr
    · exact False.elim (GProgram.G6.BridgeEntry.original_bridge_target_not_hybrid
        N he.1 (hth.symm ▸ hhyb))
  have hou := outgoing_card_twoport_one N b hb hp
  obtain ⟨p, hup⟩ := Nat.card_eq_one_iff_exists.mp hou
  obtain ⟨ch, hch⟩ := HybridChildPorts.hybrid_child_exists N h hhyb
  have hchb : N.graph.IsBridge ch := hcut ch (hch.symm ▸ hhyb)
  have hchmem : N.graph.blobOf (N.graph.source ch) = b := hch.symm ▸ hhb
  have ho : ∀ e, N.graph.IsBridge e ∧ N.graph.blobOf (N.graph.source e) = b →
      N.graph.source e = h := by
    intro e he
    have hec : e = ch := congrArg Subtype.val
      ((hup ⟨e, he⟩).trans (hup ⟨ch, hchb, hchmem⟩).symm)
    exact hec.symm ▸ hch
  have hrt : ∀ e, N.graph.source e = r → N.graph.target e = h := by
    intro e her
    have hnb : ¬ N.graph.IsBridge e := by
      intro he
      have hs := ho e ⟨he, her.symm ▸ hrb⟩
      exact hrh (her.symm.trans hs)
    have htb : N.graph.blobOf (N.graph.target e) = b :=
      (Quotient.sound (N.graph.nonbridge_sameBlob hnb)).symm.trans (her.symm ▸ hrb)
    rcases (hv (N.graph.target e)).mp htb with htr | hth
    · exact False.elim (N.graph.acyclic_no_loop N.acyclic e (her.trans htr.symm))
    · exact hth
  have hrc : (Finset.univ.filter (fun e : E => N.graph.source e = r)).card = 2 := hrd.2
  obtain ⟨e₀, e₁, hne, heq⟩ := Finset.card_eq_two.mp hrc
  have he₀ : e₀ ∈ Finset.univ.filter (fun e : E => N.graph.source e = r) := by
    rw [heq]
    simp
  have he₁ : e₁ ∈ Finset.univ.filter (fun e : E => N.graph.source e = r) := by
    rw [heq]
    simp
  have hs₀ := (Finset.mem_filter.mp he₀).2
  have hs₁ := (Finset.mem_filter.mp he₁).2
  have ht₀ := hrt e₀ hs₀
  have ht₁ := hrt e₁ hs₁
  have hint : ∀ e, (N.graph.blobOf (N.graph.source e) = b ∧
      N.graph.blobOf (N.graph.target e) = b) ↔ e = e₀ ∨ e = e₁ := by
    intro e
    constructor
    · rintro ⟨hs, ht⟩
      have her : N.graph.source e = r := by
        rcases (hv (N.graph.source e)).mp hs with her | heh
        · exact her
        · have heb : N.graph.IsBridge e := hcut e (heh.symm ▸ hhyb)
          exact False.elim (N.graph.bridge_blob_ne heb (hs.trans ht.symm))
      have hem : e ∈ Finset.univ.filter (fun f : E => N.graph.source f = r) := by
        simp [her]
      rw [heq] at hem
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hem
    · rintro (he | he)
      · subst e
        exact ⟨hs₀.symm ▸ hrb, ht₀.symm ▸ hhb⟩
      · subst e
        exact ⟨hs₁.symm ▸ hrb, ht₁.symm ▸ hhb⟩
  exact ⟨r, h, e₀, e₁, hrh, hrd, hhyb, hv, hne, hs₀, ht₀, hs₁, ht₁, hint, hi, ho⟩

#print axioms leaf_incidence_unique
#print axioms leaf_incoming_isBridge
#print axioms sameBlob_leaf_eq
#print axioms twoport_no_leaf
#print axioms finite_degree_balance
#print axioms incoming_card_cut
#print axioms outgoing_card_cut
#print axioms blob_degree_balance
#print axioms twoport_degree_sums
#print axioms ordinary_hybrid_card_one
#print axioms actual_nonroot_two_port_bigon

end UnifiedLean.G6.NonrootTwoPortBigon
