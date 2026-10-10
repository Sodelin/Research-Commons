import GParity.Chart
import G7FiniteReachability
import Mathlib.Data.List.Range

/-!
# Native CHART reachability refines bounded original graph paths

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
The actual native edge-scan closure uses the original vertex count. Completeness
reuses G7FiniteReachability.reached_complete, rather than assuming a graph
oracle. Original edge list occurrences remain distinct in the typed graph.
This is the path/acyclicity part of the RootedBinary validator bridge, not
child-bridge, cofacial, physical-calendar or active-exposure admission.
-/
namespace UnifiedLean.G6.ChartReachabilityRefinement

open Nanuq.Source
open GProgram.G7.FiniteReachability
open scoped Classical

def Bounded (s : GParity.Chart.Source) : Prop :=
  ∀ e ∈ s.edges, e.source < s.vertices ∧ e.target < s.vertices

def RawStep (s : GParity.Chart.Source) (blocked : Option Nat) (a b : Nat) : Prop :=
  ∃ e ∈ s.edges, e.source = a ∧ e.target = b ∧
    blocked ≠ some a ∧ blocked ≠ some b

def TypedStep (s : GParity.Chart.Source) (blocked : Option Nat)
    (a b : Fin s.vertices) : Prop := RawStep s blocked a.val b.val

def edgeStep (blocked : Option Nat) (visited : List Nat) (e : GParity.Chart.Edge) :
    List Nat :=
  if visited.contains e.source && blocked != some e.target &&
      blocked != some e.source && !visited.contains e.target
  then visited ++ [e.target] else visited

def scanEdges (blocked : Option Nat) (edges : List GParity.Chart.Edge)
    (visited : List Nat) : List Nat := edges.foldl (edgeStep blocked) visited

def rounds (s : GParity.Chart.Source) (blocked : Option Nat) (start n : Nat) :
    List Nat :=
  (List.range n).foldl (fun visited _ => scanEdges blocked s.edges visited) [start]

theorem rounds_succ (s : GParity.Chart.Source) (blocked : Option Nat) (start n : Nat) :
    rounds s blocked start (n + 1) = scanEdges blocked s.edges (rounds s blocked start n) := by
  simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem reachable_eq_rounds (s : GParity.Chart.Source) (blocked : Option Nat) (start : Nat)
    (hstart : blocked ≠ some start) :
    s.reachable start blocked = rounds s blocked start s.vertices := by
  simp [GParity.Chart.Source.reachable, rounds, scanEdges, edgeStep, hstart]

theorem edgeStep_contains (blocked : Option Nat) (visited : List Nat)
    (e : GParity.Chart.Edge) {a : Nat} (ha : a ∈ visited) :
    a ∈ edgeStep blocked visited e := by
  unfold edgeStep
  split
  · exact List.mem_append.mpr (Or.inl ha)
  · exact ha

theorem scanEdges_contains (blocked : Option Nat) (edges : List GParity.Chart.Edge)
    (visited : List Nat) {a : Nat} (ha : a ∈ visited) :
    a ∈ scanEdges blocked edges visited := by
  induction edges generalizing visited with
  | nil => exact ha
  | cons e es ih =>
      simp only [scanEdges, List.foldl_cons]
      exact ih (edgeStep blocked visited e) (edgeStep_contains blocked visited e ha)

theorem edgeStep_target (blocked : Option Nat) (visited : List Nat)
    (e : GParity.Chart.Edge) (hs : e.source ∈ visited)
    (hbs : blocked ≠ some e.source) (hbt : blocked ≠ some e.target) :
    e.target ∈ edgeStep blocked visited e := by
  by_cases ht : e.target ∈ visited
  · exact edgeStep_contains blocked visited e ht
  · simp [edgeStep, hs, hbs, hbt, ht]

theorem scanEdges_target (blocked : Option Nat) (edges : List GParity.Chart.Edge)
    (visited : List Nat) (e : GParity.Chart.Edge) (he : e ∈ edges)
    (hs : e.source ∈ visited)
    (hbs : blocked ≠ some e.source) (hbt : blocked ≠ some e.target) :
    e.target ∈ scanEdges blocked edges visited := by
  induction edges generalizing visited with
  | nil => simp at he
  | cons f es ih =>
      simp only [scanEdges, List.foldl_cons]
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact scanEdges_contains blocked es _ (edgeStep_target blocked visited f hs hbs hbt)
      · exact ih (edgeStep blocked visited f) he (edgeStep_contains blocked visited f hs)

theorem edgeStep_preserves (blocked : Option Nat) (visited : List Nat)
    (e : GParity.Chart.Edge) (P : Nat → Prop)
    (hvisited : ∀ a ∈ visited, P a)
    (hclose : P e.source → blocked ≠ some e.source → blocked ≠ some e.target → P e.target) :
    ∀ a ∈ edgeStep blocked visited e, P a := by
  intro a ha
  unfold edgeStep at ha
  split at ha
  next h =>
    rcases List.mem_append.mp ha with ha | ha
    · exact hvisited a ha
    · have hea : a = e.target := by simpa using ha
      subst a
      have hc : e.source ∈ visited ∧ blocked ≠ some e.target ∧
          blocked ≠ some e.source ∧ e.target ∉ visited := by
        simpa [Bool.and_assoc] using h
      exact hclose (hvisited _ hc.1) hc.2.2.1 hc.2.1
  next => exact hvisited a ha

theorem scanEdges_preserves (blocked : Option Nat) (edges : List GParity.Chart.Edge)
    (visited : List Nat) (P : Nat → Prop)
    (hvisited : ∀ a ∈ visited, P a)
    (hclose : ∀ e ∈ edges, P e.source → blocked ≠ some e.source →
      blocked ≠ some e.target → P e.target) :
    ∀ a ∈ scanEdges blocked edges visited, P a := by
  induction edges generalizing visited with
  | nil => exact hvisited
  | cons e es ih =>
      simp only [scanEdges, List.foldl_cons]
      apply ih (edgeStep blocked visited e)
      · exact edgeStep_preserves blocked visited e P hvisited (hclose e (by simp))
      · intro f hf
        exact hclose f (by simp [hf])

theorem rounds_sound (s : GParity.Chart.Source) (blocked : Option Nat) (start n : Nat) :
    ∀ b ∈ rounds s blocked start n, Relation.ReflTransGen (RawStep s blocked) start b := by
  induction n with
  | zero =>
      intro b hb
      have he : b = start := by simpa [rounds] using hb
      subst b
      exact .refl
  | succ n ih =>
      rw [rounds_succ]
      apply scanEdges_preserves blocked s.edges _
        (fun b => Relation.ReflTransGen (RawStep s blocked) start b) ih
      intro e he hs hbs hbt
      exact hs.tail ⟨e, he, rfl, rfl, hbs, hbt⟩

theorem rawReach_to_typed (s : GParity.Chart.Source) (hbounded : Bounded s)
    (blocked : Option Nat) (start : Fin s.vertices) {b : Nat}
    (h : Relation.ReflTransGen (RawStep s blocked) start.val b) :
    ∀ finish : Fin s.vertices, finish.val = b →
      Relation.ReflTransGen (TypedStep s blocked) start finish := by
  induction h with
  | refl =>
      intro finish hf
      have he : finish = start := Fin.ext hf
      subst finish
      exact .refl
  | @tail b c _ hbc ih =>
      intro finish hf
      have hb : b < s.vertices := by
        obtain ⟨e, he, hs, _, _, _⟩ := hbc
        rw [← hs]
        exact (hbounded e he).1
      let middle : Fin s.vertices := ⟨b, hb⟩
      apply (ih middle rfl).tail
      change RawStep s blocked b finish.val
      rw [hf]
      exact hbc

/-- A complete native scan includes every one-step finite saturation grow.
The inherited G7 bound therefore also bounds this literal native algorithm. -/
theorem rounds_contains_reached (s : GParity.Chart.Source) (blocked : Option Nat)
    (start : Fin s.vertices) (n : Nat) (b : Fin s.vertices)
    (h : b ∈ reached (TypedStep s blocked) start n) :
    b.val ∈ rounds s blocked start.val n := by
  induction n with
  | zero =>
      have he : b = start := by simpa [reached] using h
      subst b
      simp [rounds]
  | succ n ih =>
      rw [rounds_succ]
      rcases Finset.mem_union.mp h with h | h
      · exact scanEdges_contains blocked s.edges _ (ih h)
      · obtain ⟨a, ha, hab⟩ := (Finset.mem_filter.mp h).2
        obtain ⟨e, he, hs, ht, hbs, hbt⟩ := hab
        have hsource : e.source ∈ rounds s blocked start.val n := by
          rw [hs]
          exact ih ha
        have htarget := scanEdges_target blocked s.edges _ e he hsource hbs hbt
        rw [ht] at htarget
        exact htarget

/-- Exact semantics of the actual executable closure, with explicit endpoint
bounds and the native blocked-start refusal stated in the theorem premises. -/
theorem reachable_iff (s : GParity.Chart.Source) (hbounded : Bounded s)
    (blocked : Option Nat) (start finish : Fin s.vertices)
    (hstart : blocked ≠ some start.val) :
    finish.val ∈ s.reachable start.val blocked ↔
      Relation.ReflTransGen (TypedStep s blocked) start finish := by
  rw [reachable_eq_rounds s blocked start.val hstart]
  constructor
  · intro h
    exact rawReach_to_typed s hbounded blocked start
      (rounds_sound s blocked start.val s.vertices finish.val h) finish rfl
  · intro h
    have hr : finish ∈ reached (TypedStep s blocked) start s.vertices := by
      simpa only [Fintype.card_fin] using
        reached_complete (TypedStep s blocked) start finish h
    exact rounds_contains_reached s blocked start s.vertices finish hr

def graphOfBounded (s : GParity.Chart.Source) (hbounded : Bounded s) :
    EdgeGraph (Fin s.vertices) (Fin s.edges.length) where
  source e := ⟨(s.edges.get e).source, (hbounded _ (List.get_mem _ e)).1⟩
  target e := ⟨(s.edges.get e).target, (hbounded _ (List.get_mem _ e)).2⟩

theorem typedStep_graph_iff (s : GParity.Chart.Source) (hbounded : Bounded s)
    (blocked : Option Nat) (a b : Fin s.vertices) :
    TypedStep s blocked a b ↔
      (graphOfBounded s hbounded).DStep a b ∧
        blocked ≠ some a.val ∧ blocked ≠ some b.val := by
  constructor
  · rintro ⟨e, he, hs, ht, hbs, hbt⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    subst e
    exact ⟨⟨i, Fin.ext hs, Fin.ext ht⟩, hbs, hbt⟩
  · rintro ⟨⟨i, hs, ht⟩, hbs, hbt⟩
    exact ⟨s.edges.get i, List.get_mem _ i,
      congrArg Fin.val hs, congrArg Fin.val ht, hbs, hbt⟩

theorem reachable_graph_iff (s : GParity.Chart.Source) (hbounded : Bounded s)
    (start finish : Fin s.vertices) :
    finish.val ∈ s.reachable start.val none ↔
      (graphOfBounded s hbounded).DReach start finish := by
  rw [reachable_iff s hbounded none start finish (by simp)]
  constructor
  · exact Relation.ReflTransGen.mono
      (fun a b h => ((typedStep_graph_iff s hbounded none a b).mp h).1)
  · exact Relation.ReflTransGen.mono
      (fun a b h => (typedStep_graph_iff s hbounded none a b).mpr ⟨h, by simp, by simp⟩)

#print axioms rounds_sound
#print axioms rounds_contains_reached
#print axioms reachable_iff
#print axioms graphOfBounded
#print axioms reachable_graph_iff

end UnifiedLean.G6.ChartReachabilityRefinement
