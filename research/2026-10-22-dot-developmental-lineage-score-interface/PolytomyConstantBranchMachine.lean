/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime certificate.

A concrete pinned-TM2 primitive for the ACTUAL fixed yes/no output branches:
erase the whole input, write a fixed Boolean list, and halt cleanly. This is
not the full constructor, parser, selector or independent verifier. The
complete machine obligations remain open and are not assumed here.
-/
import PolytomyBinaryWidthBounds

namespace PolytomyReductionModel

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- The argument is a fixed program literal, not a run-time output oracle.
    Executing these pushes reverses their listed order onto the stack. -/
def literalPushStmt : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | b :: rest => .push () (fun _ => b) (literalPushStmt rest)

theorem unitStackUpdate (stack replacement : List Bool) :
    Function.update (fun _ : Unit => stack) () replacement =
      (fun _ : Unit => replacement) := by
  funext k
  cases k
  simp

theorem literalPushStmt_effect (revOut : List Bool) (v : Bool) (stack : List Bool) :
    TM2.stepAux (literalPushStmt revOut) v (fun _ => stack) =
      (⟨none, v, fun _ => revOut.reverse ++ stack⟩ :
        TM2.Cfg (fun _ : Unit => Bool) Unit Bool) := by
  induction revOut generalizing stack with
  | nil => rfl
  | cons b rest ih =>
      simp only [literalPushStmt, TM2.stepAux, unitStackUpdate]
      rw [ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def clearThenLiteralStmt (out : List Bool) :
    TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  .pop () (fun _ head => head.isSome)
    (.branch (fun present => present) (.goto (fun _ => ()))
      (literalPushStmt out.reverse))

/-- One input/output stack, one loop label, two internal Boolean states.
    Every stack alphabet is Bool. There are no auxiliary work stacks. -/
def constantBranchMachine (out : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := clearThenLiteralStmt out

def literalLoopCfg (v : Bool) (bits : List Bool) :
    TM2.Cfg (fun _ : Unit => Bool) Unit Bool :=
  ⟨some (), v, fun _ => bits⟩

def literalHaltCfg (out : List Bool) :
    TM2.Cfg (fun _ : Unit => Bool) Unit Bool :=
  ⟨none, false, fun _ => out⟩

theorem constantBranch_step_cons (out : List Bool) (v b : Bool) (rest : List Bool) :
    (constantBranchMachine out).step (literalLoopCfg v (b :: rest)) =
      some (literalLoopCfg true rest) := by
  simp [FinTM2.step, TM2.step, constantBranchMachine, clearThenLiteralStmt,
    literalLoopCfg, TM2.stepAux, unitStackUpdate]

theorem constantBranch_step_nil (out : List Bool) (v : Bool) :
    (constantBranchMachine out).step (literalLoopCfg v []) =
      some (literalHaltCfg out) := by
  simp [FinTM2.step, TM2.step, constantBranchMachine, clearThenLiteralStmt,
    literalLoopCfg, literalHaltCfg, TM2.stepAux, unitStackUpdate,
    literalPushStmt_effect]

/-- A single actual step, using the pinned operational evidence type. -/
def evalsOneStep {S : Type} (f : S → Option S) (a b : S)
    (h : f a = some b) : EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by simpa using h
  steps_le_m := le_rfl

/-- Each input symbol costs one step, followed by one empty-stack/literal
    step. The fixed literal has finitely many primitive pushes inside that
    last pinned-TM2 statement. No input-dependent work is hidden there. -/
def constantBranchRun (out bits : List Bool) (v : Bool) :
    EvalsToInTime (constantBranchMachine out).step (literalLoopCfg v bits)
      (some (literalHaltCfg out)) (bits.length + 1) := by
  induction bits generalizing v with
  | nil =>
      exact evalsOneStep _ _ _ (constantBranch_step_nil out v)
  | cons b rest ih =>
      have h1 := evalsOneStep _ _ _ (constantBranch_step_cons out v b rest)
      have h2 := ih true
      have h := EvalsToInTime.trans (constantBranchMachine out).step
        1 (rest.length + 1) (literalLoopCfg v (b :: rest))
        (literalLoopCfg true rest) (some (literalHaltCfg out)) h1 h2
      simpa only [List.length_cons] using h

theorem constantBranch_init (out bits : List Bool) :
    initList (constantBranchMachine out) bits = literalLoopCfg false bits := by
  change (⟨some (), false, _⟩ : TM2.Cfg (fun _ : Unit => Bool) Unit Bool) =
    ⟨some (), false, fun _ => bits⟩
  congr 1
  funext k
  cases k
  simp [constantBranchMachine]

theorem constantBranch_halt (out : List Bool) :
    haltList (constantBranchMachine out) out = literalHaltCfg out := by
  change (⟨none, false, _⟩ : TM2.Cfg (fun _ : Unit => Bool) Unit Bool) =
    ⟨none, false, fun _ => out⟩
  congr 1
  funext k
  cases k
  simp [constantBranchMachine]

/-- A supplied source term for this fixed-literal primitive ONLY.
    UNELABORATED: not a compiler-verified machine certificate. -/
def constantBranchPoly (out : List Bool) :
    TM2ComputableInPolyTime (fun bits : List Bool => bits)
      (fun bits : List Bool => bits) (fun _ : List Bool => out) where
  tm := constantBranchMachine out
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun bits := by
    simpa [TM2OutputsInTime, constantBranch_init, constantBranch_halt] using
      constantBranchRun out bits false

/-- These literals are the existing genuine marked-star target encodings,
    not new special yes/no language symbols. The guard selecting a branch
    is NOT implemented by either constant machine. -/
def fixedYesBranchPoly :
    TM2ComputableInPolyTime (fun bits : List Bool => bits)
      (fun bits : List Bool => bits)
      (fun _ : List Bool => scanEncodeTarget scanFixedYesTarget) :=
  constantBranchPoly (scanEncodeTarget scanFixedYesTarget)

def fixedNoBranchPoly :
    TM2ComputableInPolyTime (fun bits : List Bool => bits)
      (fun bits : List Bool => bits)
      (fun _ : List Bool => scanEncodeTarget scanFixedNoTarget) :=
  constantBranchPoly (scanEncodeTarget scanFixedNoTarget)

/- This module does NOT inhabit ConstructorMachineWitness or
VerifierMachineWitness. The dynamic parser, guards, branching control,
canonical constructor, independent checker, general composition and all
time/copy/cleanup proofs for them remain open, along with formal source
hardness and authorized kernel checking of the entire dependency chain.
The full byte/actual-objective semantic theorem remains unchanged. -/

end PolytomyReductionModel
