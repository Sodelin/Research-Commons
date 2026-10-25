import IndexedDiscriminatingSections

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Finite trace reversal and the actual right-to-left discriminating adapter.
Every reversal index is bounded before subtraction is used. Original vertex
labels and the actual discriminating witness are retained literally.
-/

namespace RestrictedCausal.IndexedDiscriminatingSections

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open InducingSeparation DiscriminatingStatus VertexActivePaths
open DiscriminatingIntervalGeometry

universe u v w

def ReverseVertex {X : Type u} (vertex : Nat → X) (size : Nat) (i : Nat) : X :=
  vertex (size - 1 - i)

def vertexAt {X : Type u} (fallback : X) : List X → Nat → X
  | [], _ => fallback
  | x :: _, 0 => x
  | _ :: xs, i + 1 => vertexAt fallback xs i

theorem trace_shift {X : Type u} (vertex : Nat → X) (xs : List X) (offset shift : Nat) :
    Trace (fun i => vertex (i + shift)) offset xs ↔ Trace vertex (offset + shift) xs := by
  induction xs generalizing offset with
  | nil => exact Iff.rfl
  | cons x xs ih =>
      simp only [Trace, ih]
      have same : offset + 1 + shift = offset + shift + 1 := by omega
      rw [same]

/-- A total indexing function is constructed from the actual finite list.
Its fallback is never used by any bounded-position argument. -/
theorem trace_vertexAt {X : Type u} (fallback : X) (xs : List X) :
    Trace (vertexAt fallback xs) 0 xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      refine ⟨rfl, ?_⟩
      have shifted : Trace (fun i => vertexAt fallback (x :: xs) (i + 1)) 0 xs := by
        simpa only [vertexAt] using ih
      simpa only [Nat.zero_add] using (trace_shift (vertexAt fallback (x :: xs)) xs 0 1).mp shifted

theorem trace_reverse {X : Type u} (vertex : Nat → X) (xs : List X) (offset : Nat)
    («trace» : Trace vertex offset xs) :
    Trace (fun i => vertex (offset + xs.length - 1 - i)) 0 xs.reverse := by
  induction xs generalizing offset with
  | nil => trivial
  | cons x xs ih =>
      rw [List.reverse_cons]
      apply (trace_append _ xs.reverse [x] 0).mpr
      constructor
      · have rest := ih (offset + 1) «trace».2
        have same : (fun i => vertex (offset + 1 + xs.length - 1 - i)) =
            (fun i => vertex (offset + (x :: xs).length - 1 - i)) := by
          funext i
          congr 1
          simp only [List.length_cons]
          omega
        rw [same] at rest
        exact rest
      · change vertex (offset + (x :: xs).length - 1 - (0 + xs.reverse.length)) = x ∧ True
        have index : offset + (x :: xs).length - 1 - (0 + xs.reverse.length) = offset := by
          simp only [List.length_cons, List.length_reverse]
          omega
        exact ⟨by simpa only [index] using «trace».1, trivial⟩

theorem trace_mem_at {X : Type u} (vertex : Nat → X) (xs : List X) (offset : Nat)
    («trace» : Trace vertex offset xs) (i : Nat) (lower : offset ≤ i)
    (upper : i < offset + xs.length) : vertex i ∈ xs := by
  induction xs generalizing offset with
  | nil => simp only [List.length_nil] at upper; omega
  | cons x xs ih =>
      by_cases «first» : i = offset
      · exact List.mem_cons.mpr (Or.inl (by simpa only [«first»] using «trace».1))
      · apply List.mem_cons_of_mem
        exact ih (offset + 1) «trace».2 (by omega) (by simp only [List.length_cons] at upper; omega)

/-- A simple physical vertex trace gives injectivity on its real finite
position range. Values of the total indexing function outside that range
are deliberately unconstrained and cannot enter this argument. -/
theorem trace_injective {X : Type u} (vertex : Nat → X) (xs : List X) :
    ∀ offset, Trace vertex offset xs → xs.Nodup →
      ∀ i j, offset ≤ i → i < offset + xs.length →
        offset ≤ j → j < offset + xs.length → vertex i = vertex j → i = j := by
  induction xs with
  | nil =>
      intro offset «trace» simple i j iLower iUpper jLower jUpper same
      simp only [List.length_nil] at iUpper
      omega
  | cons x xs ih =>
      intro offset «trace» simple i j iLower iUpper jLower jUpper same
      have noHead := (List.nodup_cons.mp simple).1
      have tailSimple := (List.nodup_cons.mp simple).2
      by_cases iFirst : i = offset
      · by_cases jFirst : j = offset
        · omega
        · have member := trace_mem_at vertex xs (offset + 1) «trace».2 j
            (by omega) (by simp only [List.length_cons] at jUpper; omega)
          have jValue : vertex j = x := same.symm.trans (by simpa only [iFirst] using «trace».1)
          exact (noHead (jValue ▸ member)).elim
      · by_cases jFirst : j = offset
        · have member := trace_mem_at vertex xs (offset + 1) «trace».2 i
            (by omega) (by simp only [List.length_cons] at iUpper; omega)
          have iValue : vertex i = x := same.trans (by simpa only [jFirst] using «trace».1)
          exact (noHead (iValue ▸ member)).elim
        · exact ih (offset + 1) «trace».2 tailSimple i j (by omega)
            (by simp only [List.length_cons] at iUpper; omega) (by omega)
            (by simp only [List.length_cons] at jUpper; omega) same

/-- Reflect an actual forward section into the original path positions.
Its underlying discriminating path remains the same ordered path; only the
indexing function changes. Interior collider triples reverse their two
neighbors, using actual marked-edge symmetry. -/
theorem reverse_forward_indexed {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) (size center : Nat)
    (w : IndexedWitness D (ReverseVertex vertex size) center)
    (forward : w.start < center ∧ w.before + 1 = center ∧ w.finish = center + 1)
    (bounded : w.finish < size) :
    ∃ reversed : IndexedWitness D vertex (size - 1 - center),
      reversed.start = size - 1 - w.start ∧ reversed.before = size - 1 - w.before ∧
      reversed.finish = size - 1 - w.finish := by
  have oldTrace : Trace (ReverseVertex vertex size) w.start w.witness.vertices := by
    rcases w.position_trace with «left» | «right»
    · exact «left».2
    · omega
  have shifted : Trace (fun i => ReverseVertex vertex size (i + w.start)) 0 w.witness.vertices :=
    (trace_shift (ReverseVertex vertex size) w.witness.vertices 0 w.start).mpr
      (by simpa only [Nat.zero_add] using oldTrace)
  have sameFunction : (fun i => ReverseVertex vertex size (i + w.start)) =
      (fun i => vertex (size - 1 - w.start - i)) := by
    funext i
    unfold ReverseVertex
    congr 1
    omega
  rw [sameFunction] at shifted
  refine ⟨{
    start := size - 1 - w.start
    before := size - 1 - w.before
    finish := size - 1 - w.finish
    orientation := ?_
    witness := w.witness
    start_vertex := w.start_vertex
    position_trace := ?_
    span := ?_
    parents := ?_
    colliders := ?_
  }, rfl, rfl, rfl⟩
  · exact Or.inr ⟨by omega, by omega, by omega⟩
  · exact Or.inr ⟨by omega, shifted⟩
  · have oldSpan := w.span.1 forward.1
    exact ⟨fun «impossible» => by omega, fun _ => by omega⟩
  · intro i interior
    have inside : size - 1 - center < i ∧ i < size - 1 - w.start := by
      rcases interior with h | h <;> omega
    have reflected : Interior w.start center (size - 1 - i) := Or.inl ⟨by omega, by omega⟩
    have involution : size - 1 - (size - 1 - i) = i := by omega
    simpa only [ReverseVertex, involution] using w.parents (size - 1 - i) reflected
  · intro i interior
    have inside : size - 1 - center < i ∧ i < size - 1 - w.start := by
      rcases interior with h | h <;> omega
    have reflected : Interior w.start center (size - 1 - i) := Or.inl ⟨by omega, by omega⟩
    have involution : size - 1 - (size - 1 - i) = i := by omega
    have «left» : size - 1 - (size - 1 - i - 1) = i + 1 := by omega
    have «right» : size - 1 - (size - 1 - i + 1) = i - 1 := by omega
    have old := collider_reverse D (w.colliders (size - 1 - i) reflected)
    simpa only [ReverseVertex, involution, «left», «right»] using old

theorem index_reverse_occurrence {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) {a b c : X}
    (w : DiscriminatingWitness (mag D) a b c) (whole : List X)
    («trace» : Trace vertex 0 whole) (occurs : w.OccursOn whole.reverse) :
    ∃ center, ∃ indexed : IndexedWitness D vertex center,
      indexed.finish < center ∧ center < indexed.start ∧ indexed.start < whole.length ∧
      vertex center = b := by
  have reversedTrace : Trace (ReverseVertex vertex whole.length) 0 whole.reverse := by
    change Trace (fun i => vertex (whole.length - 1 - i)) 0 whole.reverse
    simpa only [Nat.zero_add] using trace_reverse vertex whole 0 «trace»
  obtain ⟨offset, indexed, start, before, finish, bounded, label⟩ :=
    index_forward_occurrence D (ReverseVertex vertex whole.length) w whole.reverse reversedTrace occurs
  have forward : indexed.start < offset + w.parents.length + 1 ∧
      indexed.before + 1 = offset + w.parents.length + 1 ∧
      indexed.finish = offset + w.parents.length + 1 + 1 := by
    rw [start, before, finish]
    omega
  have sizeBound : indexed.finish < whole.length := by simpa only [List.length_reverse] using bounded
  obtain ⟨actual, actualStart, actualBefore, actualFinish⟩ := reverse_forward_indexed D vertex whole.length
    (offset + w.parents.length + 1) indexed forward sizeBound
  refine ⟨whole.length - 1 - (offset + w.parents.length + 1), actual, ?_, ?_, ?_, label⟩
  · rw [actualFinish, finish]
    omega
  · rw [actualStart, start]
    omega
  · rw [actualStart]
    omega

end RestrictedCausal.IndexedDiscriminatingSections
