/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

One shared front-end inventory: original pair split, exact physical caps,
three original bounded/saturated headers, required dimensions, and paid A.
Malformed pair failure skips the cap-dependent header code. This supplies
the front of the SAME restricted verifier, not the final grammar/guards/
clean-halt composition or the independent encoded-hardness premise.
-/
import PolytomyVerifierPairCaps

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive VerifierFrontPort where
  | target | certificate | universe | rows | budget | types
  | large | counter | temp | residue | subtrahend
  deriving DecidableEq, Fintype

abbrev VerifierFrontPorts (K : Type) := VerifierFrontPort ↪ K

@[simp] theorem verifierFrontPorts_eq (p : VerifierFrontPorts K) (a b : VerifierFrontPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def verifierFrontPair (p : VerifierFrontPorts K) : PairCapPorts K where
  toFun := fun
    | .target => p .target
    | .certificate => p .certificate
    | .temp => p .temp
    | .large => p .large
    | .counter => p .counter
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def verifierFrontHeader (p : VerifierFrontPorts K) : VerifierHeaderPorts K where
  toFun := fun
    | .universe => p .universe
    | .rows => p .rows
    | .budget => p .budget
    | .large => p .large
    | .counter => p .counter
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

theorem verifierFront_types_distinct (p : VerifierFrontPorts K) (j : VerifierHeaderPort) :
    p .types ≠ verifierFrontHeader p j := by cases j <;> simp [verifierFrontHeader]

def verifierFrontRoutine (p : VerifierFrontPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (pairCapsRoutine (verifierFrontPair p))
    (RoutineControl.branch Prod.snd (verifierHeaderAlphabetRoutine (verifierFrontHeader p) (p .types))
      (Atom.routine cleanupNoop))

def verifierFrontResult (p : VerifierFrontPorts K) (bits : List Bool)
    (base : K → List Bool) (frame : F) : CountdownStore (NumericStack K) F :=
  match readVerifierPair bits with
  | none => pairCapsResult (verifierFrontPair p) bits base frame
  | some (input, cert) =>
      verifierHeaderAlphabetEval (verifierFrontHeader p) (p .types)
        (input.length + 1) (verifierBudgetCap input cert)
        (pairCapsSuccessResult (verifierFrontPair p) input cert base frame)

def verifierFrontBound (L : ℕ) : ℕ :=
  pairCapsBound L + verifierHeaderAlphabetBound L (L + 1) ((L + 1) ^ 2) + 2

theorem verifierHeaderAlphabetBound_mono (L C D C' D' : ℕ) (hC : C ≤ C') (hD : D ≤ D') :
    verifierHeaderAlphabetBound L C D ≤ verifierHeaderAlphabetBound L C' D' := by
  unfold verifierHeaderAlphabetBound verifierHeadersBound headerScalarBound numericRecordStepBound
  have hLC := Nat.mul_le_mul_left L hC
  have hLD := Nat.mul_le_mul_left L hD
  have hCC := Nat.mul_le_mul hC hC
  nlinarith

theorem verifierFrontBound_expansion (L : ℕ) :
    verifierFrontBound L = 6 * L ^ 3 + 50 * L ^ 2 + 183 * L + 269 := by
  unfold verifierFrontBound pairCapsBound verifierHeaderAlphabetBound verifierHeadersBound
    headerScalarBound numericRecordStepBound
  ring

theorem verifierFront_pair_ready (p : VerifierFrontPorts K) (input cert : List Bool)
    (base : K → List Bool) (hfresh : ∀ j : VerifierFrontPort, base (p j) = [])
    (frame : F) (L : ℕ) (hinput : input.length ≤ L) :
    VerifierHeadersEntry (verifierFrontHeader p) (input.length + 1)
      (verifierBudgetCap input cert) L
      (pairCapsSuccessResult (verifierFrontPair p) input cert base frame) ∧
    (pairCapsSuccessResult (verifierFrontPair p) input cert base frame).stk (.inr (p .types)) = [] := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [NumericLoopInv, pairCapsSuccessResult, numericStore, numericStacks] using hinput
  · simp [pairCapsSuccessResult, pairCapsBase, numericStore, numericStacks,
      verifierFrontHeader, verifierFrontPair]
  · intro j hj
    cases j <;> simp_all [pairCapsSuccessResult, pairCapsBase, numericStore,
      numericStacks, verifierFrontHeader, verifierFrontPair, hfresh]
  · simp [pairCapsSuccessResult, pairCapsBase, numericStore, numericStacks,
      verifierFrontPair, hfresh]

/-- No supplied physical-cap premise and no constructor-origin promise.
The program handles every original pair word, all malformed header paths,
both zero/undersized dimensions and capped large headers. The output is
still a front-end store, NOT the final one-bit clean-halt answer. -/
theorem verifierFront_executes (p : VerifierFrontPorts K) (bits : List Bool)
    (base : K → List Bool) (hfresh : ∀ j : VerifierFrontPort, base (p j) = [])
    (frame : F) (guard flag : Bool) :
    ∃ n ≤ verifierFrontBound bits.length,
      (verifierFrontRoutine p).Executes
        (numericStore base (frame, guard) flag bits [] [] [] [])
        (verifierFrontResult p bits base frame) n := by
  have hpair (j : PairCapPort) : base (verifierFrontPair p j) = [] := by
    cases j <;> exact hfresh _
  obtain ⟨a, ha, h1⟩ := pairCaps_executes (verifierFrontPair p) bits base hpair frame guard flag
  cases hp : readVerifierPair bits with
  | none =>
      have hflag : (pairCapsResult (verifierFrontPair p) bits base frame).state.2 = false := by
        simp [pairCapsResult, hp, numericStore]
      have h2 := RoutineControl.branch_false Prod.snd
        (verifierHeaderAlphabetRoutine (verifierFrontHeader p) (p .types)) (Atom.routine cleanupNoop)
        hflag (Atom.executes cleanupNoop (pairCapsResult (verifierFrontPair p) bits base frame))
      refine ⟨a + 2, by unfold verifierFrontBound; omega, ?_⟩
      simpa [verifierFrontRoutine, verifierFrontResult, hp, cleanupNoop, Op.apply] using
        RoutineComposition.seq_executes _ _ h1 h2
  | some q =>
      rcases q with ⟨input, cert⟩
      have hlen := readVerifierPair_payload_length bits input cert hp
      have hinput : input.length ≤ bits.length := by omega
      obtain ⟨hentry, htypes0⟩ := verifierFront_pair_ready p input cert base hfresh frame bits.length hinput
      obtain ⟨b, hb, h2⟩ := verifierHeaderAlphabet_executes (verifierFrontHeader p) (p .types)
        (verifierFront_types_distinct p) (input.length + 1) (verifierBudgetCap input cert) bits.length
        (pairCapsSuccessResult (verifierFrontPair p) input cert base frame) hentry htypes0
      have hflag : (pairCapsSuccessResult (verifierFrontPair p) input cert base frame).state.2 = true := rfl
      have h3 := RoutineControl.branch_true Prod.snd
        (verifierHeaderAlphabetRoutine (verifierFrontHeader p) (p .types)) (Atom.routine cleanupNoop)
        hflag h2
      have hmono := verifierHeaderAlphabetBound_mono bits.length (input.length + 1)
        (verifierBudgetCap input cert) (bits.length + 1) ((bits.length + 1) ^ 2)
        (by omega) (verifierBudgetCap_pair_bound bits input cert hp)
      refine ⟨a + (b + 1), by unfold verifierFrontBound; omega, ?_⟩
      simpa only [verifierFrontRoutine, verifierFrontResult, pairCapsResult, hp] using
        RoutineComposition.seq_executes _ _ h1 h3

/- The initial pair/cap/header/A pipeline now has an explicit polynomial
source contract. Still missing is the ONE full fixed-inventory join with
the original forest/certificate grammar, all target/certificate guards,
cell equality, every-clade refinement, root-inclusive score, absorbing
rejection and exact one-bit clean halt. It is not VerifierMachineWitness;
EncodedSourceHardness and actual elaboration remain independent gaps. -/

/-- A semantic view of the ORIGINAL pair/header frontier. The residual
forest still starts with its ONE original unary tree count. -/
abbrev VerifierFrontView := (List Bool × List Bool) × ((ℕ × ℕ × ℕ) × List Bool)

def readVerifierFront (bits : List Bool) : Option VerifierFrontView :=
  (readVerifierPair bits).bind (fun q =>
    (readDimensionedVerifierHeaders q.1.length (verifierBudgetCap q.1 q.2) q.1).map
      (fun h => (q, h)))

def observeVerifierFront (p : VerifierFrontPorts K)
    (s : CountdownStore (NumericStack K) F) : Option VerifierFrontView :=
  (observeVerifierHeaders (verifierFrontHeader p) s).map (fun h =>
    ((s.stk (.inr (p .target)), s.stk (.inr (p .certificate))), h))

theorem verifierFront_saved (p : VerifierFrontPorts K) (bits input cert : List Bool)
    (base : K → List Bool) (frame : F) (hp : readVerifierPair bits = some (input, cert)) :
    (verifierFrontResult p bits base frame).stk (.inr (p .target)) = input ∧
      (verifierFrontResult p bits base frame).stk (.inr (p .certificate)) = cert := by
  let s := pairCapsSuccessResult (verifierFrontPair p) input cert base frame
  have ht := verifierHeaderAlphabet_extra (verifierFrontHeader p) (p .types) (p .target)
    (by intro j; cases j <;> simp [verifierFrontHeader]) (by simp)
    (input.length + 1) (verifierBudgetCap input cert) s
  have hc := verifierHeaderAlphabet_extra (verifierFrontHeader p) (p .types) (p .certificate)
    (by intro j; cases j <;> simp [verifierFrontHeader]) (by simp)
    (input.length + 1) (verifierBudgetCap input cert) s
  constructor
  · simpa [verifierFrontResult, hp, s, pairCapsSuccessResult, pairCapsBase,
      verifierFrontPair, numericStore, numericStacks] using ht
  · simpa [verifierFrontResult, hp, s, pairCapsSuccessResult, pairCapsBase,
      verifierFrontPair, numericStore, numericStacks] using hc

/-- All words, not merely constructor-produced or well-typed targets:
the actual front store has exactly the original bounded semantic view. -/
theorem verifierFront_observation (p : VerifierFrontPorts K) (bits : List Bool)
    (base : K → List Bool) (hfresh : ∀ j : VerifierFrontPort, base (p j) = []) (frame : F) :
    observeVerifierFront p (verifierFrontResult p bits base frame) = readVerifierFront bits := by
  cases hp : readVerifierPair bits with
  | none =>
      simp [observeVerifierFront, observeVerifierHeaders, verifierFrontResult,
        pairCapsResult, hp, numericStore, readVerifierFront]
  | some q =>
      rcases q with ⟨input, cert⟩
      let s := pairCapsSuccessResult (verifierFrontPair p) input cert base frame
      have hf (j : VerifierHeaderPort) (hj : j ≠ .large) :
          s.stk (.inr (verifierFrontHeader p j)) = [] := by
        cases j <;> simp_all [s, pairCapsSuccessResult, pairCapsBase, verifierFrontPair,
          verifierFrontHeader, numericStore, numericStacks, hfresh]
      have ho := verifierHeaderAlphabet_observation (verifierFrontHeader p) (p .types)
        (verifierFront_types_distinct p) input.length (verifierBudgetCap input cert) s
        (hf .universe (by decide)) (hf .rows (by decide)) (hf .budget (by decide))
      have ht := verifierFront_saved p bits input cert base frame hp
      unfold observeVerifierFront
      rw [ht.1, ht.2]
      simpa [verifierFrontResult, hp, readVerifierFront, s, pairCapsSuccessResult,
        numericStore, numericStacks] using congrArg
          (Option.map (fun h => ((input, cert), h))) ho

theorem observeVerifierFront_none (p : VerifierFrontPorts K)
    (s : CountdownStore (NumericStack K) F) :
    observeVerifierFront p s = none ↔ s.state.2 = false := by
  cases hf : s.state.2 <;> simp [observeVerifierFront, observeVerifierHeaders, hf]

/-- A fixed unused bank stays fresh. This will be instantiated by the
single whole-verifier port inventory, not assumed independently at each
later component. -/
theorem verifierFront_outside (p : VerifierFrontPorts K) (bits : List Bool)
    (base : K → List Bool) (frame : F) (k : K)
    (hk : ∀ j : VerifierFrontPort, k ≠ p j) :
    (verifierFrontResult p bits base frame).stk (.inr k) = base k := by
  cases hp : readVerifierPair bits with
  | none => simp [verifierFrontResult, pairCapsResult, hp, numericStore, numericStacks]
  | some q =>
      rcases q with ⟨input, cert⟩
      have he := verifierHeaderAlphabet_extra (verifierFrontHeader p) (p .types) k
        (by intro j; cases j <;> exact hk _) (hk .types)
        (input.length + 1) (verifierBudgetCap input cert)
        (pairCapsSuccessResult (verifierFrontPair p) input cert base frame)
      simpa [verifierFrontResult, hp, pairCapsSuccessResult, pairCapsBase,
        verifierFrontPair, numericStore, numericStacks, hk] using he

/-- Exact physical success boundary for the next ORIGINAL grammar call.
The hypotheses are observations of the actual original bits, not free
hidden parameters. The length bound is established before any A-sized
scan and includes no appeal to the as-yet-unchecked target guards. -/
theorem verifierFront_success_fields (p : VerifierFrontPorts K) (bits input cert rest : List Bool)
    (base : K → List Bool) (hfresh : ∀ j : VerifierFrontPort, base (p j) = [])
    (frame : F) (N m B : ℕ) (hp : readVerifierPair bits = some (input, cert))
    (hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
      some ((N, m, B), rest)) :
    let s := verifierFrontResult p bits base frame
    s.state.2 = true ∧ s.stk (.inl .source) = rest ∧ rest.length ≤ input.length ∧
      s.stk (.inr (p .universe)) = List.replicate N true ∧
      s.stk (.inr (p .rows)) = List.replicate m true ∧
      s.stk (.inr (p .budget)) = List.replicate B true ∧
      s.stk (.inr (p .types)) = List.replicate (N + m * N + 3) true ∧
      0 < N ∧ 2 ≤ m ∧ N ≤ input.length ∧ m ≤ input.length ∧
      B ≤ verifierBudgetCap input cert ∧ N + m * N + 3 ≤ input.length ^ 2 + input.length + 3 := by
  let h := verifierFrontHeader p
  let u := pairCapsSuccessResult (verifierFrontPair p) input cert base frame
  let v := verifierHeaderAlphabetEval h (p .types) (input.length + 1) (verifierBudgetCap input cert) u
  have hv : verifierFrontResult p bits base frame = v := by simp [verifierFrontResult, hp, v, h, u]
  obtain ⟨hentry, htypes0⟩ := verifierFront_pair_ready p input cert base hfresh frame input.length le_rfl
  have hn0 := hentry.2.2 .universe (by decide)
  have hm0 := hentry.2.2 .rows (by decide)
  have hb0 := hentry.2.2 .budget (by decide)
  have ho := verifierHeaderAlphabet_observation h (p .types) (verifierFront_types_distinct p)
    input.length (verifierBudgetCap input cert) u hn0 hm0 hb0
  have hov : observeVerifierHeaders h v = some ((N, m, B), rest) := by
    simpa [v, u, pairCapsSuccessResult, numericStore, numericStacks, hh] using ho
  obtain ⟨hflag, hN, hm, hB, hrest⟩ := (observeVerifierHeaders_some h v N m B rest).mp hov
  have hun (j : VerifierHeaderPort) (hj : j = .universe ∨ j = .rows ∨ j = .budget) :=
    verifierHeaderAlphabet_unary h (p .types) (verifierFront_types_distinct p)
      (input.length + 1) (verifierBudgetCap input cert) u hn0 hm0 hb0 j hj
  have hi := verifierHeaderAlphabet_numericInv h (p .types) (input.length + 1)
    (verifierBudgetCap input cert) input.length u hentry
  have ha := verifierHeaderAlphabet_types h (p .types) (verifierFront_types_distinct p)
    (input.length + 1) (verifierBudgetCap input cert) u hflag
  obtain ⟨hread, hNpos, hmpos⟩ :=
    (readDimensionedVerifierHeaders_some input.length (verifierBudgetCap input cert) input rest N m B).mp hh
  obtain ⟨hNl, hml, hBl, hAl⟩ :=
    readVerifierHeaders_bounds input.length (verifierBudgetCap input cert) input rest N m B hread
  rw [hv]
  refine ⟨hflag, hrest, ?_, ?_, ?_, ?_, ?_, hNpos, hmpos, hNl, hml, hBl, ?_⟩
  · simpa only [hrest] using hi.2.2.2.2
  · simpa only [hN, h, verifierFrontHeader] using hun .universe (by simp)
  · simpa only [hm, h, verifierFrontHeader] using hun .rows (by simp)
  · simpa only [hB, h, verifierFrontHeader] using hun .budget (by simp)
  · simpa only [hN, hm] using ha
  · simpa only [pow_two] using hAl

theorem readVerifierFront_some (bits input cert rest : List Bool) (N m B : ℕ) :
    readVerifierFront bits = some ((input, cert), ((N, m, B), rest)) ↔
      readVerifierPair bits = some (input, cert) ∧
      readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
        some ((N, m, B), rest) := by
  unfold readVerifierFront
  cases hp : readVerifierPair bits with
  | none => simp
  | some q =>
      simp only [Option.bind_some]
      constructor
      · intro he
        cases hh : readDimensionedVerifierHeaders q.1.length (verifierBudgetCap q.1 q.2) q.1 with
        | none => simp [hh] at he
        | some h =>
            have hev : (q, h) = ((input, cert), ((N, m, B), rest)) := by simpa [hh] using he
            have hq := congrArg Prod.fst hev
            have hd := congrArg Prod.snd hev
            subst q
            subst h
            exact ⟨rfl, hh⟩
      · rintro ⟨he, hh⟩
        have hq := Option.some.inj he
        subst q
        simp [hh]

end PolytomyReductionModel.WholeVerifierController
