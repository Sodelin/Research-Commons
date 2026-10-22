/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Invariant-sensitive original-reader observation for an actual physical
countdown. Both an actual body contract and its exact observation law are
explicit premises. The next file discharges them for unary identifiers.
-/
import PolytomyUnaryVisitorSemantics

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F A B : Type} [DecidableEq K]

def countdownReadFold (reader : List Bool → Option (A × List Bool)) (step : F → A → F) :
    ℕ → List Bool → F → Option (List Bool × F)
  | 0, bits, acc => some (bits, acc)
  | n + 1, bits, acc =>
      match reader bits with
      | none => none
      | some (a, rest) => countdownReadFold reader step n rest (step acc a)

theorem countdownReadFold_eq (reader : List Bool → Option (A × List Bool)) (step : F → A → F)
    (n : ℕ) : ∀ bits acc, countdownReadFold reader step n bits acc =
      (readMany reader n bits).map (fun q => (q.2, q.1.foldl step acc)) := by
  induction n with
  | zero => intro bits acc; simp [countdownReadFold, readMany]
  | succ n ih =>
      intro bits acc
      cases hp : reader bits with
      | none => simp [countdownReadFold, readMany, hp]
      | some q =>
          rcases q with ⟨a, rest⟩
          rw [countdownReadFold, hp, ih]
          cases hq : readMany reader n rest with
          | none => simp [readMany, hp, hq]
          | some z => rcases z with ⟨xs, tail⟩; simp [readMany, hp, hq]

theorem unaryVisitObservation_none (s : CountdownStore (NumericStack K) F) :
    unaryVisitObservation s = none ↔ s.state.2 = false := by
  cases h : s.state.2 <;> simp [unaryVisitObservation, h]

theorem unaryVisitObservation_some (s : CountdownStore (NumericStack K) F)
    (bits : List Bool) (acc : F) :
    unaryVisitObservation s = some (bits, acc) ↔
      s.state.2 = true ∧ s.stk (.inl .source) = bits ∧ s.state.1.1 = acc := by
  cases h : s.state.2 <;> simp [unaryVisitObservation, h, Prod.mk.injEq]

theorem observedCountdownLoop (c : K)
    (body : Routine (fun _ : NumericStack K => Bool) (CountdownState F))
    (f : CountdownStore (NumericStack K) F → CountdownStore (NumericStack K) F)
    (Inv : CountdownStore (NumericStack K) F → Prop) (M : ℕ)
    (hc : CountdownContract (.inr c) body f Inv M)
    (reader : List Bool → Option (A × List Bool)) (step : F → A → F)
    (hbody : ∀ s, Inv s → unaryVisitObservation (f s) =
      if s.state.2 then (reader (s.stk (.inl .source))).map (fun q => (q.2, step s.state.1.1 q.1)) else none)
    (n : ℕ) : ∀ s, Inv s → (s.stk (.inr c)).length = n → s.state.2 = true →
      unaryVisitObservation (countdownLoopEval (.inr c) f n (countdownPeek (.inr c) s)) =
        countdownReadFold reader step n (s.stk (.inl .source)) s.state.1.1 := by
  induction n with
  | zero =>
      intro s hs hlen hok
      simp [countdownLoopEval, countdownReadFold, unaryVisitObservation,
        countdownPeek, countdownPeekOp, Op.apply, hok]
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
      have hacc : p.state.1.1 = s.state.1.1 := rfl
      have hpflag : p.state.2 = true := hok
      have hplen : (p.stk (.inr c)).length = n := by
        change ((countdownPop (.inr c) (countdownPeek (.inr c) s)).stk (.inr c)).length = n
        rw [countdownPop_counter]
        change (s.stk (.inr c)).tail.length = n
        cases hw : s.stk (.inr c) with
        | nil => simp [hw] at hlen
        | cons b xs => simp only [hw, List.length_cons] at hlen; simp only [List.tail_cons]; omega
      have hb := hbody p hpInv
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      change unaryVisitObservation (countdownLoopEval (.inr c) f n (countdownPeek (.inr c) (f p))) = _
      cases hp : reader (s.stk (.inl .source)) with
      | none =>
          have ho : unaryVisitObservation (f p) = none := by
            simpa only [hpflag, ↓reduceIte, hsrc, hp, Option.map_none] using hb
          have hf := (unaryVisitObservation_none _).mp ho
          rw [countdownLoop_failed (.inr c) f n (countdownPeek (.inr c) (f p)) hf]
          change unaryVisitObservation (f p) = _
          rw [ho]; simp [countdownReadFold, hp]
      | some q =>
          rcases q with ⟨a, rest⟩
          have ho : unaryVisitObservation (f p) = some (rest, step s.state.1.1 a) := by
            simpa only [hpflag, ↓reduceIte, hsrc, hp, hacc, Option.map_some] using hb
          obtain ⟨hflag, hsource, hframe⟩ := (unaryVisitObservation_some _ _ _).mp ho
          have hcounter := hc.counter_preserved p hpInv
          have hi := ih (f p) (hc.body_closed p hpInv) (by rw [hcounter]; exact hplen) hflag
          simpa only [hsource, hframe, countdownReadFold, hp] using hi

theorem observedCountdown (c : K)
    (body : Routine (fun _ : NumericStack K => Bool) (CountdownState F))
    (f : CountdownStore (NumericStack K) F → CountdownStore (NumericStack K) F)
    (Inv : CountdownStore (NumericStack K) F → Prop) (M : ℕ)
    (hc : CountdownContract (.inr c) body f Inv M)
    (reader : List Bool → Option (A × List Bool)) (step : F → A → F)
    (hbody : ∀ s, Inv s → unaryVisitObservation (f s) =
      if s.state.2 then (reader (s.stk (.inl .source))).map (fun q => (q.2, step s.state.1.1 q.1)) else none)
    (s : CountdownStore (NumericStack K) F) (hs : Inv s) :
    unaryVisitObservation (countdownEval (.inr c) f s) =
      if s.state.2 then (readMany reader (s.stk (.inr c)).length (s.stk (.inl .source))).map
        (fun q => (q.2, q.1.foldl step s.state.1.1)) else none := by
  change unaryVisitObservation
    (countdownLoopEval (.inr c) f (s.stk (.inr c)).length (countdownPeek (.inr c) s)) = _
  cases hf : s.state.2 with
  | false =>
      rw [countdownLoop_failed (.inr c) f (s.stk (.inr c)).length (countdownPeek (.inr c) s) hf]
      simp [unaryVisitObservation, countdownPeek, countdownPeekOp, Op.apply, hf]
  | true =>
      rw [observedCountdownLoop c body f Inv M hc reader step hbody
        (s.stk (.inr c)).length s hs rfl hf, countdownReadFold_eq]
      simp only [hf, ↓reduceIte]

theorem countdownLoop_preserves_on (counter : K)
    (body : Routine (fun _ : K => Bool) (CountdownState F))
    (f : CountdownStore K F → CountdownStore K F) (Inv : CountdownStore K F → Prop)
    (M : ℕ) (hc : CountdownContract counter body f Inv M) (obs : CountdownStore K F → B)
    (hpeek : ∀ s, obs (countdownPeek counter s) = obs s)
    (hpop : ∀ s, obs (countdownPop counter s) = obs s)
    (hf : ∀ s, Inv s → obs (f s) = obs s) (fuel : ℕ) :
    ∀ s, Inv s → obs (countdownLoopEval counter f fuel s) = obs s := by
  induction fuel with
  | zero => intro s hs; rfl
  | succ fuel ih =>
      intro s hs
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          have hp := hc.pop_closed s hs hg
          have hu := hc.peek_closed _ (hc.body_closed _ hp)
          rw [countdownLoopEval, hg]
          simp only [↓reduceIte]
          rw [ih _ hu, hpeek, hf _ hp, hpop]

end PolytomyReductionModel
