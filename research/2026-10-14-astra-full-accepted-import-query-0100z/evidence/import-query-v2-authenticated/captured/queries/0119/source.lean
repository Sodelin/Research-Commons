import G2LiteralCutResidual
import G2MarkedTraceBudgetStability

/-!
# Deterministic continuation from the actual retained cut residual

Contributor: dot (OpenAI), 2026-10-06. This phase08 module uses the frozen
literal recursion, inclusive event cutoff and unchanged destination-clock
embedding. ClockRegular permits an initial clock equal to zero. All list
identities remove inactive padding first. No probability-law or Markov
premise is assumed. The full recorded-past joint law is a separate module.
-/

namespace GProgram.G2.SameClockContinuation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.MarkedTraceCuts
open GProgram.G2.MarkedTraceBudgetStability
open GProgram.G2.LiteralCutResidual
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def cutGood (N : RootedBinary V E X) {sample : Copy → X} (bound : Nat) :
    CutResidual N sample → Prop
  | .inl _ => True
  | .inr z => liveCard z.1 ≤ bound ∧ ClockRegular z.2

lemma cutGood_mono (N : RootedBinary V E X) {sample : Copy → X}
    {a b : Nat} (hab : a ≤ b) (z : CutResidual N sample) :
    cutGood N a z → cutGood N b z := by
  cases z with
  | inl u => simp [cutGood]
  | inr z => exact fun h => ⟨le_trans h.1 hab,h.2⟩

lemma shifted_clock_regular {I : Type*} (c : I → ℝ) (a : ℝ)
    (hc : ClockRegular c) (ha : ∀ p, a ≤ c p) :
    ClockRegular (fun p => c p-a) := by
  constructor
  · intro p; exact sub_nonneg.mpr (ha p)
  · intro p q h; exact hc.2 (sub_left_injective h)

/-- Every successful residual is on a smaller live carrier and retains
regular original coordinates. Failure branches assert nothing. -/
theorem literal_cut_good (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hc : ClockRegular c) :
    cutGood N (liveCard s) (literalCutResidual N n t s c) := by
  induction n generalizing s t with
  | zero =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp only [literalCutResidual,if_pos hstop,encodeResidual,cutGood]
        exact ⟨le_refl _,shifted_clock_regular c t hc (fun p => (hstop p).le)⟩
      · simp [literalCutResidual,hstop,cutGood]
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp only [literalCutResidual,if_pos hstop,encodeResidual,cutGood]
        exact ⟨le_refl _,shifted_clock_regular c t hc (fun p => (hstop p).le)⟩
      · simp only [literalCutResidual,if_neg hstop]
        cases hp : selectedWinner c with
        | none => trivial
        | some p =>
            simp only
            by_cases hpt : c p ≤ t
            · rw [if_pos hpt]
              have hcard := merger_destination_card N s p
              apply cutGood_mono N (show liveCard (stepDestination N s (some p)) ≤ liveCard s by omega)
              exact ih (t-c p) (stepDestination N s (some p))
                (fun q => c (destinationClockEmbedding N s p q).val-c p)
                (destination_residual_regular N s c p hc hp)
            · simp [hpt,cutGood]

theorem residual_regular_and_card (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s d : Code N sample) (c : Choice N s → ℝ)
    (k : Choice N d → ℝ) (hc : ClockRegular c)
    (hcut : literalCutResidual N n t s c = encodeResidual N d k) :
    liveCard d ≤ liveCard s ∧ ClockRegular k := by
  have h := literal_cut_good N n t s c hc
  rw [hcut] at h
  exact h

lemma selectedWinner_sub_eq {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℝ) (a : ℝ) (ha : 0 ≤ a) (hb : ∀ p, a ≤ c p) :
    selectedWinner (fun p => c p-a) = selectedWinner c := by
  cases hp : selectedWinner c with
  | some p =>
      apply (selectedWinner_eq_some_iff _ p).mpr
      have hw := (selectedWinner_eq_some_iff c p).mp hp
      exact ⟨sub_nonneg.mpr (hb p),fun q => sub_lt_sub_right (hw.2 q) a⟩
  | none =>
      cases hq : selectedWinner (fun p => c p-a) with
      | none => rfl
      | some q =>
          have hw := (selectedWinner_eq_some_iff _ q).mp hq
          have hq' : selectedWinner c = some q :=
            (selectedWinner_eq_some_iff c q).mpr
              ⟨le_trans ha (hb q),fun p => by have hh := hw.2 p; dsimp at hh; linarith⟩
          rw [hp] at hq'
          cases hq'

lemma map_shiftRecord_add {S : Type*} (l : List (Bool × ℝ × S)) (a b : ℝ) :
    (l.map (shiftRecord b)).map (shiftRecord a) = l.map (shiftRecord (a+b)) := by
  rw [List.map_map]
  congr 1
  funext r
  simp [Function.comp_def,shiftRecord,add_assoc]

/-- Before any clock can have rung, translating all clock coordinates
translates exactly the active record ages. No padded-vector identity is used. -/
theorem activeTrace_shift_clocks (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (a v : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (ha : 0 ≤ a) (hb : ∀ p, a ≤ c p) :
    activeTrace N n (a+v) s c =
      (activeTrace N n v s (fun p => c p-a)).map (shiftRecord a) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [activeTrace_succ,activeTrace_succ,selectedWinner_sub_eq c a ha hb]
      cases hp : selectedWinner c with
      | none => rfl
      | some p =>
          simp only
          by_cases hpt : c p ≤ a+v
          · have hpt' : c p-a ≤ v := by linarith
            simp only [if_pos hpt,if_pos hpt',List.map_cons]
            have htime : v-(c p-a) = a+v-c p := by ring
            have hclock :
                (fun q : Choice N (stepDestination N s (some p)) =>
                  (c (destinationClockEmbedding N s p q).val-a)-(c p-a)) =
                (fun q => c (destinationClockEmbedding N s p q).val-c p) := by
              funext q; ring
            rw [htime,hclock,map_shiftRecord_add]
            have he : a+(c p-a) = c p := by ring
            simp [shiftRecord,he]
          · have hpt' : ¬ c p-a ≤ v := by intro hh; apply hpt; linarith
            simp [hpt,hpt']

def activeContinuation (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t v : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    CutResidual N sample → Prop
  | .inl _ => True
  | .inr z => activeTrace N n (t+v) s c = activeTrace N n t s c ++
      (activeTrace N n v z.1 z.2).map (shiftRecord t)

/-- Induction follows the actual retained-coordinate recursion. At a merger,
cardinality descent and the proved successful-budget stability identify the
remaining-budget future with the requested full-budget future. -/
theorem active_continuation_aux (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t v : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hc : ClockRegular c) (hn : liveCard s ≤ n) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    activeContinuation N n t v s c (literalCutResidual N n t s c) := by
  induction n generalizing s t v with
  | zero =>
      by_cases hstop : ∀ p : Choice N s, t < c p <;>
        simp [literalCutResidual,hstop,activeContinuation,encodeResidual]
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp only [literalCutResidual,if_pos hstop,encodeResidual,activeContinuation]
        rw [activeTrace_of_no_jump N (n+1) t s c hstop,List.nil_append]
        exact activeTrace_shift_clocks N (n+1) t v s c ht (fun p => (hstop p).le)
      · simp only [literalCutResidual,if_neg hstop]
        cases hp : selectedWinner c with
        | none => trivial
        | some p =>
            simp only
            by_cases hpt : c p ≤ t
            · rw [if_pos hpt]
              let d0 := stepDestination N s (some p)
              let c0 : Choice N d0 → ℝ :=
                fun q => c (destinationClockEmbedding N s p q).val-c p
              have hc0 : ClockRegular c0 := destination_residual_regular N s c p hc hp
              have hcard := merger_destination_card N s p
              have hn0 : liveCard d0 ≤ n := by dsimp [d0]; omega
              have ht0 : 0 ≤ t-c p := sub_nonneg.mpr hpt
              have hi := ih (t-c p) v d0 c0 hc0 hn0 ht0 hv
              cases hr : literalCutResidual N n (t-c p) d0 c0 with
              | inl u =>
                  trivial
              | inr z =>
                  rcases z with ⟨d,k⟩
                  have hk := residual_regular_and_card N n (t-c p) d0 d c0 k hc0 hr
                  have hkn : liveCard d ≤ n := le_trans hk.1 hn0
                  have hb := activeTrace_budget_succ_of_success N n v d k
                    (marked_trace_success_on_regular N n d v k hkn hk.2)
                  rw [hr] at hi
                  change activeTrace N n ((t-c p)+v) d0 c0 =
                    activeTrace N n (t-c p) d0 c0 ++
                      (activeTrace N n v d k).map (shiftRecord (t-c p)) at hi
                  change activeTrace N (n+1) (t+v) s c =
                    activeTrace N (n+1) t s c ++
                      (activeTrace N (n+1) v d k).map (shiftRecord t)
                  rw [activeTrace_succ,activeTrace_succ]
                  have hptv : c p ≤ t+v := by linarith
                  simp only [hp,if_pos hpt,if_pos hptv]
                  change (true,c p,d0) ::
                    (activeTrace N n (t+v-c p) d0 c0).map (shiftRecord (c p)) =
                    ((true,c p,d0) ::
                      (activeTrace N n (t-c p) d0 c0).map (shiftRecord (c p))) ++
                      (activeTrace N (n+1) v d k).map (shiftRecord t)
                  have he : t+v-c p = (t-c p)+v := by ring
                  rw [he,hi,List.map_append,map_shiftRecord_add,hb]
                  have he' : c p+(t-c p) = t := by ring
                  rw [he',List.cons_append]
            · simp [hpt,activeContinuation]

theorem same_clock_active_continuation (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (t v : ℝ) (s d : Code N sample)
    (c : Choice N s → ℝ) (k : Choice N d → ℝ) (hc : ClockRegular c)
    (hn : liveCard s ≤ n) (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hcut : literalCutResidual N n t s c = encodeResidual N d k) :
    activeTrace N n (t+v) s c = activeTrace N n t s c ++
      (activeTrace N n v d k).map (shiftRecord t) := by
  have h := active_continuation_aux N n t v s c hc hn ht hv
  rw [hcut] at h
  exact h

def recordEndpoint {S : Type*} (s : S) (l : List (Bool × ℝ × S)) : S :=
  l.foldl (fun _ r => r.2.2) s

@[simp] lemma recordEndpoint_nil {S : Type*} (s : S) :
    recordEndpoint s [] = s := rfl

@[simp] lemma recordEndpoint_cons {S : Type*} (s : S) (r : Bool × ℝ × S)
    (l : List (Bool × ℝ × S)) : recordEndpoint s (r::l) = recordEndpoint r.2.2 l := rfl

@[simp] lemma recordEndpoint_shift {S : Type*} (s : S) (l : List (Bool × ℝ × S))
    (a : ℝ) : recordEndpoint s (l.map (shiftRecord a)) = recordEndpoint s l := by
  simp [recordEndpoint,List.foldl_map,shiftRecord]

lemma recordEndpoint_append {S : Type*} (s : S) (l q : List (Bool × ℝ × S)) :
    recordEndpoint s (l++q) = recordEndpoint (recordEndpoint s l) q := by
  exact List.foldl_append

/-- On actual recursively generated traces, the endpoint is the fold of the
active destinations, even when the success flag is false. This is not an
assertion about arbitrary padded vectors. -/
theorem actual_trace_endpoint_fold (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    traceEndpoint N n s (literalMarkedTrace N n t s c).2 =
      recordEndpoint s (activeTrace N n t s c) := by
  induction n generalizing s t with
  | zero => simp [traceEndpoint]
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp [literalMarkedTrace,hstop,activeTrace,empty_trace_endpoint]
      · cases hp : selectedWinner c with
        | none => simp [literalMarkedTrace,hstop,hp,activeTrace]
        | some p =>
            by_cases hpt : c p ≤ t
            · simp only [literalMarkedTrace,if_neg hstop,hp,if_pos hpt,
                prepend_trace_endpoint,activeTrace_succ,recordEndpoint_cons,
                recordEndpoint_shift]
              exact ih (t-c p) (stepDestination N s (some p))
                (fun q => c (destinationClockEmbedding N s p q).val-c p)
            · simp [literalMarkedTrace,hstop,hp,hpt,activeTrace]

theorem literal_endpoint_of_success (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hs : (literalMarkedTrace N n t s c).1 = true) :
    literalClockEndpoint N n t s c = some (recordEndpoint s (activeTrace N n t s c)) := by
  rw [← marked_trace_endpoint_eq N n s t c]
  simp only [decodedEndpoint,hs,if_true,actual_trace_endpoint_fold]

/-- Endpoint continuation from the exact encoded retained residual. The
clock vector and catalogue are unchanged; sufficient budgets are proved. -/
theorem same_clock_endpoint_continuation (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (t v : ℝ) (s d : Code N sample)
    (c : Choice N s → ℝ) (k : Choice N d → ℝ) (hc : ClockRegular c)
    (hn : liveCard s ≤ n) (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hcut : literalCutResidual N n t s c = encodeResidual N d k) :
    literalClockEndpoint N n (t+v) s c = literalClockEndpoint N n v d k := by
  have hk := residual_regular_and_card N n t s d c k hc hcut
  have hd : literalClockEndpoint N n t s c = some d := by
    rw [← cut_endpoint_eq_literal N n s t c,hcut]
    rfl
  have hf : recordEndpoint s (activeTrace N n t s c) = d := by
    rw [literal_endpoint_of_success N n t s c
      (marked_trace_success_on_regular N n s t c hn hc)] at hd
    exact Option.some.inj hd
  rw [literal_endpoint_of_success N n (t+v) s c
      (marked_trace_success_on_regular N n s (t+v) c hn hc),
    literal_endpoint_of_success N n v d k
      (marked_trace_success_on_regular N n d v k (le_trans hk.1 hn) hk.2),
    same_clock_active_continuation N n t v s d c k hc hn ht hv hcut,
    recordEndpoint_append,recordEndpoint_shift,hf]

#print axioms cutGood_mono
#print axioms shifted_clock_regular
#print axioms literal_cut_good
#print axioms residual_regular_and_card
#print axioms selectedWinner_sub_eq
#print axioms map_shiftRecord_add
#print axioms activeTrace_shift_clocks
#print axioms active_continuation_aux
#print axioms same_clock_active_continuation
#print axioms recordEndpoint_nil
#print axioms recordEndpoint_cons
#print axioms recordEndpoint_shift
#print axioms recordEndpoint_append
#print axioms actual_trace_endpoint_fold
#print axioms literal_endpoint_of_success
#print axioms same_clock_endpoint_continuation

end GProgram.G2.SameClockContinuation
