import G6PositiveGeneratorCompression
import G6RationalCompressionCertificate
import G1ContextualForestReplacement

/-!
# Original full forest/register fibres inherit one positive atom certificate

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Source consumer of accepted G6PositiveGeneratorCompression (1ca6ba90),
G6RationalCompressionCertificate (353521bc), and the original G1 full rooted
labelled forest reader (feab5f5e). The unchanged full-Code row theorem is
summed over its actual finite reader fibres. There is no count-only model,
new generator, coefficient extractor, or positive source construction here.

Every carried subtree and complete original register is retained. The output
reader type need not be finite: the original Code carrier supplies finite
fibres and a finite image. One supplied atom certificate precedes every
source/entering row and forest/register output. All-copy co-location and the
CURRENT live-root cap remain explicit. Proper outside panels, private seed
marginalization, physical exit/context composition and legal positive graph
factors require their separate existing interfaces.

Status: separately frozen source proposal. No kernel acceptance is asserted
until the sole scheduler supplies an exact complete owned-audit receipt.
-/

namespace GProgram.G6.OriginalForestRegisterCompression

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G6.OriginalPopulationGeneratorBounds
open GProgram.G6.PositiveGeneratorCompression
open GProgram.G6.RationalCompressionCertificate
open G1ContextualForestReplacement
open scoped BigOperators Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The complete original Code row is grouped by one fixed actual reader.
Only Code is summed; no finiteness of the ambient reader type is assumed. -/
noncomputable def observedQuotient {Obs : Type*} [DecidableEq Obs]
    (N : RootedBinary V E X) {sample : Copy → X} (M : ℕ) (s : Code N sample)
    (readout : Code N sample → Obs) (output : Obs) (z : ℝ) : ℝ :=
  ∑ d : Code N sample,
    if readout d = output then populationQuotient N M s d z else 0

/-- Original complete labelled unranked forest and the ENTIRE original
vertex register, without current-owner or ordered-child identities. -/
noncomputable def forestRegister (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) : (V → Bool) × Finset (UnrankedTree Copy) :=
  ((state d).register,rootForest N d)

noncomputable def forestRegisterQuotient
    (N : RootedBinary V E X) {sample : Copy → X} (M : ℕ) (s : Code N sample)
    (register : V → Bool) (forest : Finset (UnrankedTree Copy)) (z : ℝ) : ℝ :=
  observedQuotient N M s (forestRegister N) (register,forest) z

/-- Finite fibre pushforward of the accepted full original-Code equality.
The same supplied mass/tail certificate is used in every fibre. -/
theorem observed_compression {Obs : Type*} [DecidableEq Obs] {n r : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (z alpha : Fin n → ℝ)
    (atom : Fin r → Fin n) (beta : Fin r → ℝ)
    (hz : ∀ a, z a < 1)
    (hmass : (∑ b, beta b) = ∑ a, alpha a)
    (htail : ∀ q : Fin (M - 2),
      (∑ a, alpha a * tailVector M (z a) q) =
        ∑ b, beta b * tailVector M (z (atom b)) q)
    (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample)
    (i : Option E) (hs : CoLocated N s i) (hcap : liveCard s ≤ M)
    (readout : Code N sample → Obs) (output : Obs) :
    (∑ a, alpha a * observedQuotient N M s readout output (z a)) =
      ∑ b, beta b * observedQuotient N M s readout output (z (atom b)) := by
  classical
  calc
    _ = ∑ d : Code N sample, ∑ a : Fin n,
        if readout d = output then alpha a * populationQuotient N M s d (z a) else 0 := by
      simp only [observedQuotient,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : readout d = output <;> simp [h]
    _ = ∑ d : Code N sample, ∑ b : Fin r,
        if readout d = output then beta b * populationQuotient N M s d (z (atom b)) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : readout d = output
      · simp only [if_pos h]
        exact original_population_compression M hM z alpha atom beta hz hmass htail
          N s d i hs hcap
      · simp only [if_neg h,Finset.sum_const_zero]
    _ = _ := by
      simp only [observedQuotient,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : readout d = output <;> simp [h]

/-- Concrete full rooted labelled-forest/complete-register source interface,
including arbitrary already formed descendant-labelled trees. -/
theorem original_forest_register_compression {n r : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (z alpha : Fin n → ℝ)
    (atom : Fin r → Fin n) (beta : Fin r → ℝ)
    (hz : ∀ a, z a < 1)
    (hmass : (∑ b, beta b) = ∑ a, alpha a)
    (htail : ∀ q : Fin (M - 2),
      (∑ a, alpha a * tailVector M (z a) q) =
        ∑ b, beta b * tailVector M (z (atom b)) q)
    (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample)
    (i : Option E) (hs : CoLocated N s i) (hcap : liveCard s ≤ M)
    (register : V → Bool) (forest : Finset (UnrankedTree Copy)) :
    (∑ a, alpha a * forestRegisterQuotient N M s register forest (z a)) =
      ∑ b, beta b * forestRegisterQuotient N M s register forest (z (atom b)) := by
  classical
  exact observed_compression M hM z alpha atom beta hz hmass htail N s i hs hcap
    (forestRegister N) (register,forest)

/-- The positive supplied-atom list is chosen ONCE before all actual source
rows and full forest/register outputs. No forest alphabet factor is introduced. -/
theorem exists_uniform_original_forest_register_compression {n : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (z alpha : Fin n → ℝ)
    (hz : ∀ a, 0 < z a ∧ z a < 1) (halpha : ∀ a, 0 ≤ alpha a) :
    ∃ r : ℕ, r ≤ M - 1 ∧ ∃ atom : Fin r → Fin n, ∃ beta : Fin r → ℝ,
      (∀ b, 0 < beta b) ∧ (∑ b, beta b) = ∑ a, alpha a ∧
      (∀ q : Fin (M - 2),
        (∑ a, alpha a * tailVector M (z a) q) =
          ∑ b, beta b * tailVector M (z (atom b)) q) ∧
      ∀ (N : RootedBinary V E X) (sample : Copy → X) (s : Code N sample)
        (i : Option E), CoLocated N s i → liveCard s ≤ M →
        ∀ (register : V → Bool) (forest : Finset (UnrankedTree Copy)),
          (∑ a, alpha a * forestRegisterQuotient N M s register forest (z a)) =
            ∑ b, beta b * forestRegisterQuotient N M s register forest (z (atom b)) := by
  obtain ⟨r,hr,atom,beta,hb,hm,ht⟩ := positive_tail_compression M hM z alpha halpha
  refine ⟨r,hr,atom,beta,hb,hm,ht,?_⟩
  intro N sample s i hs hcap register forest
  exact original_forest_register_compression M hM z alpha atom beta (fun a => (hz a).2)
    hm ht N s i hs hcap register forest

/-- The existing executable rational certificate feeds the same concrete
forest/register interface; no noncomputable atom selection is needed. -/
theorem checked_original_forest_register_compression {n r : ℕ}
    (M : ℕ) (z alpha : Fin n → ℚ) (atom : Fin r → Fin n) (beta : Fin r → ℚ)
    (h : checkCompression M z alpha atom beta = true)
    (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample)
    (i : Option E) (hs : CoLocated N s i) (hcap : liveCard s ≤ M)
    (register : V → Bool) (forest : Finset (UnrankedTree Copy)) :
    (∑ a, (alpha a : ℝ) * forestRegisterQuotient N M s register forest (z a : ℝ)) =
      ∑ b, (beta b : ℝ) * forestRegisterQuotient N M s register forest (z (atom b) : ℝ) := by
  obtain ⟨hM,hz,_,_,_,hm,ht⟩ := checked_real_moments M z alpha atom beta h
  exact original_forest_register_compression M hM
    (fun a => (z a : ℝ)) (fun a => (alpha a : ℝ)) atom (fun b => (beta b : ℝ))
    (fun a => (hz a).2) hm ht N s i hs hcap register forest

#print axioms observed_compression
#print axioms original_forest_register_compression
#print axioms exists_uniform_original_forest_register_compression
#print axioms checked_original_forest_register_compression

end GProgram.G6.OriginalForestRegisterCompression
