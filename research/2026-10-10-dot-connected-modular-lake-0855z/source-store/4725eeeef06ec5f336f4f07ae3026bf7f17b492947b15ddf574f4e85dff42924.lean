import UnifiedLean.G6.UpperRateSourceCommon
import UnifiedLean.G6.InheritanceBankCommon

/-!
UNCHECKED additive draft, CLOUD-WHOLE-BANK-PROGRAM-SOL-2231Z.
One fixed original graph, one actual rate/inheritance assignment, and one
comparison bank across a finite word. Reference intervals use actual prefixes;
reference boundaries and the once-drawn ALL-original register use actual p.
The numerical interval is the upper-mean residual PMF at the ONE rhat bank.
COMMON reads the retained register. INDEP uses current original owner roots.
No desired row-law inequality is a scientific input. Physical sorted-calendar,
finite-bin readout and executable rational-table identifications remain open.
No compiler or current build target is invoked by this packet.
-/

namespace UnifiedLean.G6.WholeBankProgramCommon
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.SourcePrefix
open UnifiedLean.G6.ProgramPrefix UnifiedLean.G6.ResidualProgram
open UnifiedLean.G6.UpperMeanCommon UnifiedLean.G6.UpperRateSourceCommon
open UnifiedLean.G6.InheritanceBankCommon
open GProgram.G2.SourceFiniteHistory
open scoped Classical BigOperators NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Approximation metadata is carried only by intervals. Every boundary names
an ORIGINAL operation, and every hybrid occurrence names the same original h. -/
inductive BankInstruction (N : RootedBinary V E X)
  | interval (duration upper : ℝ≥0) (cutoff : ℕ)
  | exit (edge : E)
  | ordinary (edge : E) (degree : N.graph.inDegree (N.graph.target edge) = 1)
  | root
  | hybrid (site : Hybrid N)

/-- This is exact rational scalar data at ONE positive original bank. It does
not assert a rational PMF evaluator or executable correspondence. -/
structure OneRationalBank (N : RootedBinary V E X) where
  rates : PositivePairRates E
  inheritance : HybridProbabilities N
  rateValue : Option E → ℚ
  inheritanceValue : Hybrid N → ℚ
  rate_eq : ∀ i, pairRate rates i = (rateValue i : ℝ)
  inheritance_eq : ∀ h, inheritance.gamma h = (inheritanceValue h : ℝ)

/-- Only scalar bank bounds, never desired kernel domination. -/
structure BankBounds (N : RootedBinary V E X) (r rhat : PositivePairRates E)
    (p phat : HybridProbabilities N) (ell u : ℝ) (beta : Hybrid N → ℝ) : Prop where
  ell_nonnegative : 0 ≤ ell
  ell_le_one : ell ≤ 1
  one_le_u : 1 ≤ u
  rate_lower : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i
  rate_upper : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i
  beta_nonnegative : ∀ h, 0 ≤ beta h
  beta_le_one : ∀ h, beta h ≤ 1
  atom_true : ∀ h, beta h * p.gamma h ≤ phat.gamma h
  atom_false : ∀ h, beta h * (1 - p.gamma h) ≤ 1 - phat.gamma h

noncomputable def InstructionBudget (N : RootedBinary V E X)
    (r : PositivePairRates E) : BankInstruction N → Prop
  | .interval t b K =>
      globalClockRate (Copy := Copy) r * t ≤ b ∧ 2 * (b : ℝ) ≤ (K : ℝ) + 2
  | _ => True

/-- Upper means can be chosen as exact rational scalar values. This condition
is not needed for the analytic comparison, and supplies no executable table. -/
def RationalUpper (N : RootedBinary V E X) : BankInstruction N → Prop
  | .interval _ b _ => ∃ q : ℚ, (b : ℝ) = (q : ℝ)
  | _ => True

noncomputable def instructionSourceStep (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Bool) :
    BankInstruction N → ProgramStep N
  | .interval t _ _ => .interval t
  | .exit e => .boundary (.exit e)
  | .ordinary e hd => .boundary (.ordinary e hd)
  | .root => .boundary .root
  | .hybrid h => .boundary (if common then .common (H.parents h)
      else .independent (H.parents h) (originalGamma p h))

noncomputable def originalWord (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Bool)
    (ops : List (BankInstruction N)) : List (ProgramStep N) :=
  ops.map (instructionSourceStep N H p common)

noncomputable def actualStep (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Bool)
    (r : PositivePairRates E) (op : BankInstruction N) (s : Code N sample) :
    PMF (Code N sample) :=
  sourceProgramStep N r (instructionSourceStep N H p common op) s

noncomputable def referenceStep (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Bool)
    (r : PositivePairRates E) (op : BankInstruction N) (s : Code N sample) :
    PMF (Code N sample) :=
  match op with
  | .interval t _ K => finiteSourcePrefix N r t K s
  | _ => actualStep N H p common r op s

noncomputable def numericalStep (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (phat : HybridProbabilities N) (common : Bool)
    (rhat : PositivePairRates E) (op : BankInstruction N) (s : Code N sample) :
    PMF (Code N sample) :=
  match op with
  | .interval _ b K => upperRateResidualSource N rhat b K s
  | _ => actualStep N H phat common rhat op s

noncomputable def instructionMass (N : RootedBinary V E X)
    (r : PositivePairRates E) (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ) :
    BankInstruction N → ℝ≥0∞
  | .interval t b K =>
      ENNReal.ofReal (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) *
        (ENNReal.ofReal (ell / u)) ^ K
  | .hybrid h => if common then 1 else (ENNReal.ofReal (beta h)) ^ Fintype.card Copy
  | _ => 1

noncomputable def registerMass (N : RootedBinary V E X) (beta : Hybrid N → ℝ) : ℝ≥0∞ :=
  ∏ h : Hybrid N, ENNReal.ofReal (beta h)

/- Generic finite-word algebra. The scientific rows are constructed below. -/
noncomputable def wordMass {Op : Type*} (mu : Op → ℝ≥0∞) : List Op → ℝ≥0∞
  | [] => 1
  | op :: ops => mu op * wordMass mu ops

noncomputable def kernelProgram {S Op : Type*} (K : Op → S → PMF S) :
    List Op → S → PMF S
  | [], s => PMF.pure s
  | op :: ops, s => (K op s).bind (kernelProgram K ops)

theorem kernelProgram_domination {S Op : Type*}
    (P Q : Op → S → PMF S) (mu : Op → ℝ≥0∞) (ops : List Op) (s d : S)
    (hrow : ∀ op ∈ ops, ∀ s d, mu op * Q op s d ≤ P op s d) :
    wordMass mu ops * kernelProgram Q ops s d ≤ kernelProgram P ops s d := by
  induction ops generalizing s d with
  | nil => simp only [wordMass, kernelProgram, one_mul, le_refl]
  | cons op ops ih =>
      have hhead := hrow op (by simp)
      have htail : ∀ q ∈ ops, ∀ s d, mu q * Q q s d ≤ P q s d :=
        fun q hq => hrow q (List.mem_cons_of_mem op hq)
      change (mu op * wordMass mu ops) *
        ((Q op s).bind (kernelProgram Q ops)) d ≤
        ((P op s).bind (kernelProgram P ops)) d
      exact bind_scaled_domination _ _ _ _ _ _ (hhead s) (fun s d => ih s d htail) d

theorem historyLaw_domination {S Op : Type*}
    (P Q : Op → S → PMF S) (mu : Op → ℝ≥0∞) (ops : List Op) (s : S)
    (z : Fin ops.length → S)
    (hrow : ∀ op ∈ ops, ∀ s d, mu op * Q op s d ≤ P op s d) :
    wordMass mu ops * historyLaw Q ops s z ≤ historyLaw P ops s z := by
  induction ops generalizing s with
  | nil => simp only [wordMass, historyLaw, one_mul, le_refl]
  | cons op ops ih =>
      have hhead := hrow op (by simp)
      have htail : ∀ q ∈ ops, ∀ s d, mu q * Q q s d ≤ P q s d :=
        fun q hq => hrow q (List.mem_cons_of_mem op hq)
      change (mu op * wordMass mu ops) *
        ((Q op s).bind (fun d => (historyLaw Q ops d).map (Fin.cons d))) z ≤
        ((P op s).bind (fun d => (historyLaw P ops d).map (Fin.cons d))) z
      apply bind_scaled_domination _ _ _ _ _ _ (hhead s)
      intro d y
      exact map_scaled_domination _ _ _ (fun tail => ih d tail htail)
        (fun tail : Fin ops.length → S => (Fin.cons d tail : Fin (ops.length + 1) → S)) y

/-- Includes the entering Code, hence its once-drawn register, jointly with
ALL endpoints. Empty words still retain their initial record. -/
noncomputable def initializedHistory {S Op : Type*} (initial : PMF S)
    (K : Op → S → PMF S) (ops : List Op) : PMF (S × (Fin ops.length → S)) :=
  initial.bind (fun s => (historyLaw K ops s).map (Prod.mk s))

lemma initializedHistory_domination {S Op : Type*} (initial reference : PMF S)
    (P Q : Op → S → PMF S) (mu : Op → ℝ≥0∞) (eta : ℝ≥0∞) (ops : List Op)
    (hinit : ∀ s, eta * reference s ≤ initial s)
    (hrow : ∀ op ∈ ops, ∀ s d, mu op * Q op s d ≤ P op s d)
    (z : S × (Fin ops.length → S)) :
    (eta * wordMass mu ops) * initializedHistory reference Q ops z ≤
      initializedHistory initial P ops z := by
  unfold initializedHistory
  exact bind_scaled_domination _ _ _ _ _ _ hinit
    (fun s => map_scaled_domination _ _ _
      (fun tail => historyLaw_domination P Q mu ops s tail hrow) (Prod.mk s)) z

lemma instructionMass_le_one (N : RootedBinary V E X)
    (r rhat : PositivePairRates E) (p phat : HybridProbabilities N)
    (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ)
    (B : BankBounds N r rhat p phat ell u beta) (op : BankInstruction N)
    (hbudget : InstructionBudget (Copy := Copy) N r op) :
    instructionMass (Copy := Copy) N r common ell u beta op ≤ 1 := by
  cases op with
  | interval t b K =>
      have hc : ENNReal.ofReal
          (upperCommonMass (globalClockRate (Copy := Copy) r * t) b K) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
          (upperCommonMass_bounds _ b hbudget.1 K).2
      have ha := Left.pow_le_one_of_le (rateRatioENN_le_one ell u B.ell_le_one B.one_le_u) K
      exact (mul_le_mul' hc ha).trans (by simp)
  | exit e => exact le_rfl
  | ordinary e hd => exact le_rfl
  | root => exact le_rfl
  | hybrid h =>
      have hb : ENNReal.ofReal (beta h) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (B.beta_le_one h)
      cases common with
      | false => exact Left.pow_le_one_of_le hb _
      | true => exact le_rfl

lemma registerMass_le_one (N : RootedBinary V E X) (beta : Hybrid N → ℝ)
    (hbeta : ∀ h, beta h ≤ 1) : registerMass N beta ≤ 1 := by
  have h := Finset.prod_le_prod' (fun (h : Hybrid N) (_ : h ∈ Finset.univ) =>
    ENNReal.ofReal_le_ofReal (hbeta h))
  simpa [registerMass] using h

lemma actual_step_domination (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (r rhat : PositivePairRates E)
    (p phat : HybridProbabilities N) (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ)
    (B : BankBounds N r rhat p phat ell u beta) (op : BankInstruction N)
    (s d : Code N sample) (hbudget : InstructionBudget (Copy := Copy) N r op) :
    instructionMass (Copy := Copy) N r common ell u beta op *
      referenceStep N H p common r op s d ≤ actualStep N H p common r op s d := by
  cases op with
  | interval t b K =>
      exact actual_interval_common_domination N r t b hbudget.1 K s d hbudget.2
        ell u B.ell_le_one B.one_le_u
  | exit e => simp only [instructionMass, referenceStep, one_mul, le_refl]
  | ordinary e hd => simp only [instructionMass, referenceStep, one_mul, le_refl]
  | root => simp only [instructionMass, referenceStep, one_mul, le_refl]
  | hybrid h =>
      change instructionMass (Copy := Copy) N r common ell u beta (.hybrid h) *
        actualStep N H p common r (.hybrid h) s d ≤ actualStep N H p common r (.hybrid h) s d
      simpa only [one_mul] using mul_le_mul'
        (instructionMass_le_one N r rhat p phat common ell u beta B (.hybrid h) hbudget)
        (le_rfl : actualStep N H p common r (.hybrid h) s d ≤ _)

/-- The exact independent comparison exponent is the CURRENT AtNode count,
before the state-independent word comparison weakens it to card Copy. -/
theorem numerical_independent_current_owner_domination
    (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (r rhat : PositivePairRates E)
    (p phat : HybridProbabilities N) (ell u : ℝ) (beta : Hybrid N → ℝ)
    (B : BankBounds N r rhat p phat ell u beta) (h : Hybrid N) (s d : Code N sample) :
    (ENNReal.ofReal (beta h)) ^ Fintype.card (AtNode (state s) (H.parents h).hybrid) *
      referenceStep N H p false r (.hybrid h) s d ≤
      numericalStep N H phat false rhat (.hybrid h) s d := by
  exact actual_independent_pulse_bank_lower N (H.parents h) s d
    (originalGamma p h) (originalGamma phat h) (beta h)
    (B.beta_nonnegative h) (B.atom_true h) (B.atom_false h)

lemma numerical_step_domination (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (r rhat : PositivePairRates E)
    (p phat : HybridProbabilities N) (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ)
    (B : BankBounds N r rhat p phat ell u beta) (op : BankInstruction N)
    (s d : Code N sample) (hbudget : InstructionBudget (Copy := Copy) N r op) :
    instructionMass (Copy := Copy) N r common ell u beta op *
      referenceStep N H p common r op s d ≤ numericalStep N H phat common rhat op s d := by
  cases op with
  | interval t b K =>
      exact numerical_interval_common_domination N r rhat t b hbudget.1 K s d
        ell u B.ell_nonnegative B.ell_le_one B.one_le_u B.rate_lower B.rate_upper
  | exit e =>
      change 1 * boundaryKernel N (.exit e) s d ≤ boundaryKernel N (.exit e) s d
      simp only [one_mul, le_refl]
  | ordinary e hd =>
      change 1 * boundaryKernel N (.ordinary e hd) s d ≤ boundaryKernel N (.ordinary e hd) s d
      simp only [one_mul, le_refl]
  | root =>
      change 1 * boundaryKernel N .root s d ≤ boundaryKernel N .root s d
      simp only [one_mul, le_refl]
  | hybrid h =>
      cases common with
      | false =>
          change (ENNReal.ofReal (beta h)) ^ Fintype.card Copy *
            independentPulseKernel (H.parents h) (originalGamma p h) s d ≤
            independentPulseKernel (H.parents h) (originalGamma phat h) s d
          exact actual_independent_pulse_bank_lower_uniform N (H.parents h) s d
            (originalGamma p h) (originalGamma phat h) (beta h)
            (B.beta_nonnegative h) (B.beta_le_one h) (B.atom_true h) (B.atom_false h)
      | true =>
          change 1 * boundaryKernel N (.common (H.parents h)) s d ≤
            boundaryKernel N (.common (H.parents h)) s d
          simp only [one_mul, le_refl]

/-- Literal original source-program identity, not a desired law premise. -/
theorem actual_program_eq_sourceProgram (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Bool)
    (r : PositivePairRates E) (ops : List (BankInstruction N)) (s : Code N sample) :
    kernelProgram (actualStep N H p common r) ops s =
      sourceProgram N r (originalWord N H p common ops) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      change (sourceProgramStep N r (instructionSourceStep N H p common op) s).bind
        (kernelProgram (actualStep N H p common r) ops) =
        (sourceProgramStep N r (instructionSourceStep N H p common op) s).bind
          (sourceProgram N r (originalWord N H p common ops))
      congr 1
      funext d
      exact ih d

noncomputable def naturalInitial (N : RootedBinary V E X) (sample : Copy → X)
    (p : HybridProbabilities N) : PMF (Code N sample) :=
  (originalRegisterPMF N p).map (initialCode N sample)

noncomputable def naturalMass (N : RootedBinary V E X) (r : PositivePairRates E)
    (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ) (ops : List (BankInstruction N)) :
    ℝ≥0∞ :=
  registerMass N beta * wordMass (instructionMass (Copy := Copy) N r common ell u beta) ops

/-- Identifies the actual unconditional endpoint with a once-drawn original
register followed by the literal sourceProgram, with no assumed law equality. -/
theorem natural_actual_endpoint_eq_original (N : RootedBinary V E X)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Bool) (r : PositivePairRates E) (ops : List (BankInstruction N)) :
    (naturalInitial N sample p).bind (kernelProgram (actualStep N H p common r) ops) =
      (originalRegisterPMF N p).bind (fun register =>
        sourceProgram N r (originalWord N H p common ops) (initialCode N sample register)) := by
  unfold naturalInitial
  rw [PMF.bind_map]
  congr 1
  funext register
  exact actual_program_eq_sourceProgram N H p common r ops (initialCode N sample register)

section Consumer
variable (N : RootedBinary V E X) (sample : Copy → X) (H : OriginalParentRegistry N)
variable (r rhat : PositivePairRates E) (p phat : HybridProbabilities N)
variable (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ)
variable (B : BankBounds N r rhat p phat ell u beta)
variable (ops : List (BankInstruction N))
variable (hbudget : ∀ op ∈ ops, InstructionBudget (Copy := Copy) N r op)
include B hbudget

/-- BOTH laws dominate the SAME actual-prefix reference and SAME product mass.
The initial product charges ALL original slots ONCE, including unused slots. -/
theorem natural_endpoint_common_domination (d : Code N sample) :
    (naturalMass (Copy := Copy) N r common ell u beta ops *
      ((naturalInitial N sample p).bind
        (kernelProgram (referenceStep N H p common r) ops)) d ≤
      ((naturalInitial N sample p).bind (kernelProgram (actualStep N H p common r) ops)) d) ∧
    (naturalMass (Copy := Copy) N r common ell u beta ops *
      ((naturalInitial N sample p).bind
        (kernelProgram (referenceStep N H p common r) ops)) d ≤
      ((naturalInitial N sample phat).bind
        (kernelProgram (numericalStep N H phat common rhat) ops)) d) := by
  constructor
  · exact bind_scaled_domination _ _ _ _ _ _
      (fun s => by
        simpa only [one_mul] using mul_le_mul'
          (registerMass_le_one N beta B.beta_le_one)
          (le_rfl : naturalInitial N sample p s ≤ _))
      (fun s d => kernelProgram_domination _ _ _ ops s d
        (fun op hop s d => actual_step_domination N H r rhat p phat common ell u beta B
          op s d (hbudget op hop))) d
  · exact bind_scaled_domination _ _ _ _ _ _
      (fun s => actual_natural_initial_code_bank_lower N sample p phat beta
        B.beta_nonnegative B.atom_true B.atom_false s)
      (fun s d => kernelProgram_domination _ _ _ ops s d
        (fun op hop s d => numerical_step_domination N H r rhat p phat common ell u beta B
          op s d (hbudget op hop))) d

theorem natural_endpoint_tv :
    pmfTV ((naturalInitial N sample p).bind (kernelProgram (actualStep N H p common r) ops))
      ((naturalInitial N sample phat).bind (kernelProgram (numericalStep N H phat common rhat) ops)) ≤
      1 - (naturalMass (Copy := Copy) N r common ell u beta ops).toReal := by
  apply common_pmf_tv _ _ ((naturalInitial N sample p).bind
    (kernelProgram (referenceStep N H p common r) ops))
  · exact fun d => (natural_endpoint_common_domination N sample H r rhat p phat common
      ell u beta B ops hbudget d).1
  · exact fun d => (natural_endpoint_common_domination N sample H r rhat p phat common
      ell u beta B ops hbudget d).2

theorem natural_endpoint_joint_readout_tv {O : Type*} [Fintype O]
    (readout : Code N sample → O) :
    pmfTV (((naturalInitial N sample p).bind
        (kernelProgram (actualStep N H p common r) ops)).map readout)
      (((naturalInitial N sample phat).bind
        (kernelProgram (numericalStep N H phat common rhat) ops)).map readout) ≤
      1 - (naturalMass (Copy := Copy) N r common ell u beta ops).toReal := by
  apply common_pmf_tv _ _ (((naturalInitial N sample p).bind
    (kernelProgram (referenceStep N H p common r) ops)).map readout)
  · exact map_scaled_domination _ _ _
      (fun d => (natural_endpoint_common_domination N sample H r rhat p phat common
        ell u beta B ops hbudget d).1) readout
  · exact map_scaled_domination _ _ _
      (fun d => (natural_endpoint_common_domination N sample H r rhat p phat common
        ell u beta B ops hbudget d).2) readout

/-- One JOINT full finite vector, retaining the initial Code/register. -/
theorem natural_history_common_domination (z : Code N sample × (Fin ops.length → Code N sample)) :
    (naturalMass (Copy := Copy) N r common ell u beta ops *
      initializedHistory (naturalInitial N sample p) (referenceStep N H p common r) ops z ≤
      initializedHistory (naturalInitial N sample p) (actualStep N H p common r) ops z) ∧
    (naturalMass (Copy := Copy) N r common ell u beta ops *
      initializedHistory (naturalInitial N sample p) (referenceStep N H p common r) ops z ≤
      initializedHistory (naturalInitial N sample phat) (numericalStep N H phat common rhat) ops z) := by
  constructor
  · exact initializedHistory_domination _ _ _ _ _ _ ops
      (fun s => by
        simpa only [one_mul] using mul_le_mul'
          (registerMass_le_one N beta B.beta_le_one)
          (le_rfl : naturalInitial N sample p s ≤ _))
      (fun op hop s d => actual_step_domination N H r rhat p phat common ell u beta B
        op s d (hbudget op hop)) z
  · exact initializedHistory_domination _ _ _ _ _ _ ops
      (fun s => actual_natural_initial_code_bank_lower N sample p phat beta
        B.beta_nonnegative B.atom_true B.atom_false s)
      (fun op hop s d => numerical_step_domination N H r rhat p phat common ell u beta B
        op s d (hbudget op hop)) z

theorem natural_history_tv :
    pmfTV (initializedHistory (naturalInitial N sample p) (actualStep N H p common r) ops)
      (initializedHistory (naturalInitial N sample phat) (numericalStep N H phat common rhat) ops) ≤
      1 - (naturalMass (Copy := Copy) N r common ell u beta ops).toReal := by
  apply common_pmf_tv _ _
    (initializedHistory (naturalInitial N sample p) (referenceStep N H p common r) ops)
  · exact fun z => (natural_history_common_domination N sample H r rhat p phat common
      ell u beta B ops hbudget z).1
  · exact fun z => (natural_history_common_domination N sample H r rhat p phat common
      ell u beta B ops hbudget z).2

theorem natural_history_joint_readout_tv {O : Type*} [Fintype O]
    (readout : (Code N sample × (Fin ops.length → Code N sample)) → O) :
    pmfTV ((initializedHistory (naturalInitial N sample p) (actualStep N H p common r) ops).map readout)
      ((initializedHistory (naturalInitial N sample phat) (numericalStep N H phat common rhat) ops).map readout) ≤
      1 - (naturalMass (Copy := Copy) N r common ell u beta ops).toReal := by
  apply common_pmf_tv _ _
    ((initializedHistory (naturalInitial N sample p) (referenceStep N H p common r) ops).map readout)
  · exact map_scaled_domination _ _ _
      (fun z => (natural_history_common_domination N sample H r rhat p phat common
        ell u beta B ops hbudget z).1) readout
  · exact map_scaled_domination _ _ _
      (fun z => (natural_history_common_domination N sample H r rhat p phat common
        ell u beta B ops hbudget z).2) readout
end Consumer

/-- A bounded useful endpoint consumer stated directly against the actual
once-register source-program law, at ONE exact rational comparison bank. -/
theorem one_rational_bank_joint_endpoint_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) (sample : Copy → X) (H : OriginalParentRegistry N)
    (r : PositivePairRates E) (p : HybridProbabilities N) (bank : OneRationalBank N)
    (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ)
    (B : BankBounds N r bank.rates p bank.inheritance ell u beta)
    (ops : List (BankInstruction N))
    (hbudget : ∀ op ∈ ops, InstructionBudget (Copy := Copy) N r op)
    (readout : Code N sample → O) :
    pmfTV (((originalRegisterPMF N p).bind (fun register =>
        sourceProgram N r (originalWord N H p common ops) (initialCode N sample register))).map readout)
      (((naturalInitial N sample bank.inheritance).bind
        (kernelProgram (numericalStep N H bank.inheritance common bank.rates) ops)).map readout) ≤
      1 - (naturalMass (Copy := Copy) N r common ell u beta ops).toReal := by
  rw [← natural_actual_endpoint_eq_original N sample H p common r ops]
  exact natural_endpoint_joint_readout_tv N sample H r bank.rates p bank.inheritance common
    ell u beta B ops hbudget readout

/-- Specializes the constructed full-history consumer to ONE exact rational
bank; every occurrence of h uses bank.inheritance.gamma h. -/
theorem one_rational_bank_joint_history_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) (sample : Copy → X) (H : OriginalParentRegistry N)
    (r : PositivePairRates E) (p : HybridProbabilities N) (bank : OneRationalBank N)
    (common : Bool) (ell u : ℝ) (beta : Hybrid N → ℝ)
    (B : BankBounds N r bank.rates p bank.inheritance ell u beta)
    (ops : List (BankInstruction N))
    (hbudget : ∀ op ∈ ops, InstructionBudget (Copy := Copy) N r op)
    (readout : (Code N sample × (Fin ops.length → Code N sample)) → O) :
    pmfTV ((initializedHistory (naturalInitial N sample p) (actualStep N H p common r) ops).map readout)
      ((initializedHistory (naturalInitial N sample bank.inheritance)
        (numericalStep N H bank.inheritance common bank.rates) ops).map readout) ≤
      1 - (naturalMass (Copy := Copy) N r common ell u beta ops).toReal :=
  natural_history_joint_readout_tv N sample H r bank.rates p bank.inheritance common
    ell u beta B ops hbudget readout

#print axioms actual_step_domination
#print axioms numerical_step_domination
#print axioms numerical_independent_current_owner_domination
#print axioms actual_program_eq_sourceProgram
#print axioms natural_actual_endpoint_eq_original
#print axioms natural_endpoint_common_domination
#print axioms natural_endpoint_tv
#print axioms natural_endpoint_joint_readout_tv
#print axioms natural_history_common_domination
#print axioms natural_history_tv
#print axioms natural_history_joint_readout_tv
#print axioms one_rational_bank_joint_endpoint_tv
#print axioms one_rational_bank_joint_history_tv

end UnifiedLean.G6.WholeBankProgramCommon
