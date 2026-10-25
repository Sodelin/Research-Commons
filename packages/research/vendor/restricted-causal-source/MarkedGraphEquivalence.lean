import CanonicalRootSeparation

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Explicit marked-graph relabeling transport, for common-source indicator proofs.
-/

namespace RestrictedCausal.GraphEquivalence

open SelectedWalk CanonicalSelection
open SourceSelection (AncestorOf)
open LatentRoots (ActiveConnection)

universe u v

structure MarkedEquiv {V : Type u} {W : Type v} (G : MarkedGraph V) (K : MarkedGraph W) where
  toEquiv : V ≃ W
  edge : ∀ a b ma mb, G.edge a b ma mb ↔ K.edge (toEquiv a) (toEquiv b) ma mb

def MarkedEquiv.symm {V : Type u} {W : Type v} {G : MarkedGraph V} {K : MarkedGraph W}
    (e : MarkedEquiv G K) : MarkedEquiv K G where
  toEquiv := e.toEquiv.symm
  edge a b ma mb := by
    simpa only [Equiv.apply_symm_apply] using (e.edge (e.toEquiv.symm a) (e.toEquiv.symm b) ma mb).symm

theorem MarkedEquiv.reach {V : Type u} {W : Type v} {G : MarkedGraph V} {K : MarkedGraph W}
    (e : MarkedEquiv G K) {x y : V} (h : Reach G x y) :
    Reach K (e.toEquiv x) (e.toEquiv y) := by
  obtain ⟨xs, hx⟩ := h
  exact ⟨_, hx.map e.toEquiv (fun a b hab => (e.edge a b .tail .head).mp hab)⟩

theorem MarkedEquiv.reach_iff {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (e : MarkedEquiv G K)
    (x y : V) : Reach G x y ↔ Reach K (e.toEquiv x) (e.toEquiv y) := by
  constructor
  · exact e.reach
  · intro h
    have hp := e.symm.reach h
    simpa only [MarkedEquiv.symm, Equiv.symm_apply_apply] using hp

theorem MarkedEquiv.condition_symm {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (e : MarkedEquiv G K)
    {C : V → Prop} {D : W → Prop} (hC : ∀ x, C x ↔ D (e.toEquiv x)) :
    ∀ y, D y ↔ C (e.toEquiv.symm y) := by
  intro y
  simpa only [Equiv.apply_symm_apply] using (hC (e.toEquiv.symm y)).symm

theorem MarkedEquiv.ancestor {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (e : MarkedEquiv G K)
    {C : V → Prop} {D : W → Prop} (hC : ∀ x, C x ↔ D (e.toEquiv x))
    {x : V} (h : AncestorOf G C x) : AncestorOf K D (e.toEquiv x) := by
  obtain ⟨y, hxy, hy⟩ := h
  exact ⟨e.toEquiv y, e.reach hxy, (hC y).mp hy⟩

theorem MarkedEquiv.ancestor_iff {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (e : MarkedEquiv G K)
    {C : V → Prop} {D : W → Prop} (hC : ∀ x, C x ↔ D (e.toEquiv x))
    (x : V) : AncestorOf G C x ↔ AncestorOf K D (e.toEquiv x) := by
  constructor
  · exact e.ancestor hC
  · intro h
    have hp := e.symm.ancestor (e.condition_symm hC) h
    simpa only [MarkedEquiv.symm, Equiv.symm_apply_apply] using hp

def mapArrival {V : Type u} {W : Type v} (f : V → W) (p : Arrival V) : Arrival W :=
  ⟨f p.vertex, p.incoming⟩

theorem MarkedEquiv.transition {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (e : MarkedEquiv G K)
    {C : V → Prop} {D : W → Prop} (hC : ∀ x, C x ↔ D (e.toEquiv x))
    (p q : Arrival V) (h : Transition G C (AncestorOf G C) p q) :
    Transition K D (AncestorOf K D) (mapArrival e.toEquiv p) (mapArrival e.toEquiv q) := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  refine ⟨outgoing, incoming, (e.edge p.vertex q.vertex outgoing incoming).mp hedge, hmark, ?_⟩
  rcases p with ⟨pv, pm⟩
  cases pm with
  | none => trivial
  | some previous =>
      by_cases hcollider : previous = .head ∧ outgoing = .head
      · simp only [mapArrival, ActiveAt, if_pos hcollider] at hactive ⊢
        exact (e.ancestor_iff hC pv).mp hactive
      · simp only [mapArrival, ActiveAt, if_neg hcollider] at hactive ⊢
        exact fun hd => hactive ((hC pv).mpr hd)

theorem MarkedEquiv.active {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (e : MarkedEquiv G K)
    {C : V → Prop} {D : W → Prop} (hC : ∀ x, C x ↔ D (e.toEquiv x))
    {x y : V} (h : ActiveConnection G C x y) :
    ActiveConnection K D (e.toEquiv x) (e.toEquiv y) := by
  obtain ⟨lastMark, xs, hp, hnd⟩ := h
  have hroute := hp.map (mapArrival e.toEquiv) (e.transition hC)
  refine ⟨lastMark, xs.map (mapArrival e.toEquiv), hroute, ?_⟩
  have hn := List.Nodup.map e.toEquiv.injective hnd
  simpa only [List.map_cons, List.map_map, Function.comp_def, mapArrival] using hn

theorem MarkedEquiv.active_iff {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (e : MarkedEquiv G K)
    {C : V → Prop} {D : W → Prop} (hC : ∀ x, C x ↔ D (e.toEquiv x))
    (x y : V) : ActiveConnection G C x y ↔
      ActiveConnection K D (e.toEquiv x) (e.toEquiv y) := by
  constructor
  · exact e.active hC
  · intro h
    have hp := e.symm.active (e.condition_symm hC) h
    simpa only [MarkedEquiv.symm, Equiv.symm_apply_apply] using hp

end RestrictedCausal.GraphEquivalence
