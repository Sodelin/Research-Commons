/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Observation theorem for an actual countdown when the mathematical fold
state includes DATA observations (for example a physical tape length).
This does not put that potentially infinite type into machine control.
The actual body contract and all observation laws remain explicit.
-/
import PolytomyObservedCountdownFold

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F A Q : Type} [DecidableEq K]

def dataVisitObservation (obs : CountdownStore (NumericStack K) F → Q)
    (s : CountdownStore (NumericStack K) F) : Option (List Bool × Q) :=
  if s.state.2 then some (s.stk (.inl .source), obs s) else none

theorem dataVisitObservation_none (obs : CountdownStore (NumericStack K) F → Q)
    (s : CountdownStore (NumericStack K) F) :
    dataVisitObservation obs s = none ↔ s.state.2 = false := by
  cases h : s.state.2 <;> simp [dataVisitObservation, h]

theorem dataVisitObservation_some (obs : CountdownStore (NumericStack K) F → Q)
    (s : CountdownStore (NumericStack K) F) (bits : List Bool) (q : Q) :
    dataVisitObservation obs s = some (bits, q) ↔
      s.state.2 = true ∧ s.stk (.inl .source) = bits ∧ obs s = q := by
  cases h : s.state.2 <;> simp [dataVisitObservation, h, Prod.mk.injEq]

theorem dataVisitObservation_peek (c : K) (obs : CountdownStore (NumericStack K) F → Q)
    (hp : ∀ s, obs (countdownPeek (.inr c) s) = obs s) (s : CountdownStore (NumericStack K) F) :
    dataVisitObservation obs (countdownPeek (.inr c) s) = dataVisitObservation obs s := by
  unfold dataVisitObservation
  rw [hp]
  rfl

theorem dataObservedCountdownLoop (c : K)
    (body : Routine (fun _ : NumericStack K => Bool) (CountdownState F))
    (f : CountdownStore (NumericStack K) F → CountdownStore (NumericStack K) F)
    (Inv : CountdownStore (NumericStack K) F → Prop) (M : ℕ)
    (hc : CountdownContract (.inr c) body f Inv M)
    (obs : CountdownStore (NumericStack K) F → Q)
    (hpeek : ∀ s, obs (countdownPeek (.inr c) s) = obs s)
    (hpop : ∀ s, obs (countdownPop (.inr c) s) = obs s)
    (reader : List Bool → Option (A × List Bool)) (step : Q → A → Q)
    (hbody : ∀ s, Inv s → dataVisitObservation obs (f s) =
      if s.state.2 then (reader (s.stk (.inl .source))).map (fun q => (q.2, step (obs s) q.1)) else none)
    (n : ℕ) : ∀ s, Inv s → (s.stk (.inr c)).length = n → s.state.2 = true →
      dataVisitObservation obs (countdownLoopEval (.inr c) f n (countdownPeek (.inr c) s)) =
        countdownReadFold reader step n (s.stk (.inl .source)) (obs s) := by
  induction n with
  | zero =>
      intro s hs hlen hok
      rw [countdownLoopEval, dataVisitObservation_peek c obs hpeek]
      simp [countdownReadFold, dataVisitObservation, hok]
  | succ n ih =>
      intro s hs hlen hok
      have hhead : (s.stk (.inr c)).head?.isSome = true := by
        cases hw : s.stk (.inr c) with
        | nil => simp [hw] at hlen
        | cons b xs => rfl
      have hg : countdownGuard (countdownPeek (.inr c) s).state = true := by
        simp [countdownGuard, countdownPeek, countdownPeekOp, Op.apply, hhead, hok]
      let p := countdownPop (.inr c) (countdownPeek (.inr c) s)
      have hpInv : Inv p := hc.pop_closed _ (hc.peek_closed s hs) hg
      have hsrc : p.stk (.inl .source) = s.stk (.inl .source) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply]
      have hacc : obs p = obs s := by rw [hpop, hpeek]
      have hpflag : p.state.2 = true := hok
      have hplen : (p.stk (.inr c)).length = n := by
        change ((countdownPop (.inr c) (countdownPeek (.inr c) s)).stk (.inr c)).length = n
        rw [countdownPop_counter]
        change (s.stk (.inr c)).tail.length = n
        rw [List.length_tail, hlen]
        omega
      have hb := hbody p hpInv
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      change dataVisitObservation obs (countdownLoopEval (.inr c) f n (countdownPeek (.inr c) (f p))) = _
      cases hp : reader (s.stk (.inl .source)) with
      | none =>
          have ho : dataVisitObservation obs (f p) = none := by
            simpa only [hpflag, ↓reduceIte, hsrc, hp, Option.map_none] using hb
          have hf := (dataVisitObservation_none obs _).mp ho
          rw [countdownLoop_failed (.inr c) f n (countdownPeek (.inr c) (f p)) hf,
            dataVisitObservation_peek c obs hpeek, ho]
          simp [countdownReadFold, hp]
      | some q =>
          rcases q with ⟨a, rest⟩
          have ho : dataVisitObservation obs (f p) = some (rest, step (obs s) a) := by
            simpa only [hpflag, ↓reduceIte, hsrc, hp, hacc, Option.map_some] using hb
          obtain ⟨hflag, hsource, hframe⟩ := (dataVisitObservation_some obs _ _ _).mp ho
          have hcounter := hc.counter_preserved p hpInv
          have hi := ih (f p) (hc.body_closed p hpInv) (by rw [hcounter]; exact hplen) hflag
          simpa only [hsource, hframe, countdownReadFold, hp] using hi

theorem dataObservedCountdown (c : K)
    (body : Routine (fun _ : NumericStack K => Bool) (CountdownState F))
    (f : CountdownStore (NumericStack K) F → CountdownStore (NumericStack K) F)
    (Inv : CountdownStore (NumericStack K) F → Prop) (M : ℕ)
    (hc : CountdownContract (.inr c) body f Inv M)
    (obs : CountdownStore (NumericStack K) F → Q)
    (hpeek : ∀ s, obs (countdownPeek (.inr c) s) = obs s)
    (hpop : ∀ s, obs (countdownPop (.inr c) s) = obs s)
    (hreset : ∀ s, obs (countdownReset s) = obs s)
    (reader : List Bool → Option (A × List Bool)) (step : Q → A → Q)
    (hbody : ∀ s, Inv s → dataVisitObservation obs (f s) =
      if s.state.2 then (reader (s.stk (.inl .source))).map (fun q => (q.2, step (obs s) q.1)) else none)
    (s : CountdownStore (NumericStack K) F) (hs : Inv s) :
    dataVisitObservation obs (countdownEval (.inr c) f s) =
      if s.state.2 then (readMany reader (s.stk (.inr c)).length (s.stk (.inl .source))).map
        (fun q => (q.2, q.1.foldl step (obs s))) else none := by
  have hr : ∀ t, dataVisitObservation obs (countdownReset t) = dataVisitObservation obs t := by
    intro t
    unfold dataVisitObservation
    rw [hreset]
    rfl
  rw [countdownEval, hr]
  cases hf : s.state.2 with
  | false =>
      rw [countdownLoop_failed (.inr c) f (s.stk (.inr c)).length (countdownPeek (.inr c) s) hf,
        dataVisitObservation_peek c obs hpeek]
      simp [dataVisitObservation, hf]
  | true =>
      rw [dataObservedCountdownLoop c body f Inv M hc obs hpeek hpop reader step hbody
        (s.stk (.inr c)).length s hs rfl hf, countdownReadFold_eq]
      simp only [hf, ↓reduceIte]

/- No machine takes Q as finite control. The data observation may be
unbounded; its update theorem must be proved from actual finite-control
instructions on physical stacks. Concrete instantiation, time, invariant
preservation and cleanup obligations cannot be inferred from this lemma.
-/

end PolytomyReductionModel
