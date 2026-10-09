import UnifiedLean.G3.ConditionalZeroScoreBound

/-!
Typed provider boundary. The structures require mathematical proofs of the
displayed obligations; JSON booleans cannot construct them. `Source`, `Fits`,
`InPiece`, actual physical slots and the source pair identities must be supplied
by a source-faithful provider. This file supplies no such provider for G3.
-/

namespace UnifiedLean.G3.ConditionalZeroScore

open scoped BigOperators

inductive SupportedMode where
  | independent
  | both
  deriving DecidableEq

/-- One *physical* source on one covered shared-static piece. Repeated observed
appearances refer to these slots, rather than to independently fitted copies.
Every field is a proof obligation on that source, not a user assertion.
-/
structure PieceCertificate (slots : ℕ) where
  mode : SupportedMode
  numeric : Fin slots → NumericData
  length : Fin slots → ℕ
  p : (j : Fin slots) → Fin (length j) → ℝ
  duration : (j : Fin slots) → Fin (length j) → ℝ
  score : (j : Fin slots) → Fin (length j) → ℝ
  normalized : (j : Fin slots) → Fin (length j) → ℝ
  normalizedAtZero : (j : Fin slots) → Fin (length j) → ℝ
  weight : Fin slots → ℝ
  endpointScore : Fin slots → ℝ
  p_pos : ∀ j i, 0 < p j i
  duration_pos : ∀ j i, 0 < duration j i
  weight_pos : ∀ j, 0 < weight j
  score_nonneg : ∀ j i, 0 ≤ score j i
  additive_same_source : ∀ j, endpointScore j = ∑ i, score j i
  exact_endpoint_zero : ∑ j, weight j * endpointScore j = 0
  normalization : ∀ j i, score j i = p j i * duration j i * normalized j i
  zero_slope_floor : ∀ j i, ((numeric j).sigma : ℝ) ≤ normalizedAtZero j i
  uniform_weak_modulus : ∀ j i, duration j i ≤ ((numeric j).epsilon : ℝ) →
    |normalized j i - normalizedAtZero j i| ≤ ((numeric j).M : ℝ) * duration j i
  pairFactor : (j : Fin slots) → Fin (length j) → ℝ
  q : (j : Fin slots) → Fin (length j) → ℝ
  coin_upper : ∀ j i, p j i ≤ 1 / 4
  q_upper : ∀ j i, q j i ≤ 1
  pairFactor_nonneg : ∀ j i, 0 ≤ pairFactor j i
  actual_equal_arm_pair : ∀ j i,
    pairFactor j i = q j i + 2 * p j i * (1 - q j i)
  /-- Analytic source obligation, following from q=exp(-duration) and exp(t)≥1+t.
  The consumer does not establish that arbitrary sources have this law. -/
  exp_duration_estimate : ∀ j i, ((numeric j).delta : ℝ) < duration j i →
    (1 + ((numeric j).delta : ℝ)) * q j i ≤ 1
  survival : Fin slots → ℝ
  ordinaryFactor : Fin slots → ℝ
  ordinaryFactor_le_one : ∀ j, ordinaryFactor j ≤ 1
  actual_chronological_survival : ∀ j,
    survival j = ordinaryFactor j * ∏ i, pairFactor j i
  observed_same_source_survival_floor : ∀ j, ((numeric j).b : ℝ) ≤ survival j

theorem PieceCertificate.cell_score_zero {slots : ℕ} (c : PieceCertificate slots) :
    ∀ j i, c.score j i = 0 := by
  apply cells_zero_of_weighted_endpoint_zero c.length c.weight c.score
    c.weight_pos c.score_nonneg
  simpa only [c.additive_same_source] using c.exact_endpoint_zero

theorem PieceCertificate.duration_gap {slots : ℕ} (c : PieceCertificate slots) :
    ∀ j i, ((c.numeric j).delta : ℝ) < c.duration j i := by
  intro j i
  exact zero_score_duration_gap (c.numeric j) (c.p_pos j i) (c.duration_pos j i)
    (c.zero_slope_floor j i) (c.uniform_weak_modulus j i)
    (c.normalization j i) (c.cell_score_zero j i)

theorem PieceCertificate.slot_count_bound {slots : ℕ} (c : PieceCertificate slots) :
    ∀ j, c.length j ≤ (c.numeric j).independentBound := by
  intro j
  apply independent_product_count (c.numeric j) (c.length j) (c.pairFactor j)
    (c.survival j) (c.ordinaryFactor j) (c.pairFactor_nonneg j)
  · intro i
    exact equal_arm_pair_loss (c.numeric j) (c.coin_upper j i) (c.q_upper j i)
      (c.exp_duration_estimate j i (c.duration_gap j i)) (c.actual_equal_arm_pair j i)
  · exact c.ordinaryFactor_le_one j
  · exact c.actual_chronological_survival j
  · exact c.observed_same_source_survival_floor j

/-- Whole-fibre quantifiers are explicit. No finite cover is produced here.
`Fits` must be the original joint equations with IDs, rows, positivity,
chronology and shared registers preserved by the external source provider. -/
structure WholeFibreProvider (Source Core Piece : Type*) [Fintype Core] [Fintype Piece]
    (Fits : Source → Prop) (InCore : Source → Core → Prop)
    (InPiece : Source → Core → Piece → Prop) (slots : Core → Piece → ℕ)
    (actualLength : (source : Source) → (core : Core) → (piece : Piece) →
      Fin (slots core piece) → ℕ)
    (uniformNumeric : (core : Core) → (piece : Piece) →
      Fin (slots core piece) → NumericData)
    (SourceFaithful : (source : Source) → (core : Core) → (piece : Piece) →
      PieceCertificate (slots core piece) → Prop) where
  excluded : Core → Prop
  all_core_coverage : ∀ source, Fits source → ∃ core, InCore source core
  excluded_core_sound : ∀ source core, Fits source → InCore source core → ¬ excluded core
  all_fitting_piece_coverage : ∀ source core, Fits source → InCore source core →
    ¬ excluded core → ∃ piece, InPiece source core piece
  /-- Same original physical source, all tuples on every covered piece.
  Constructing this field is the unformalized analytic/source obligation. -/
  certificate : ∀ source core piece, Fits source → InCore source core →
    InPiece source core piece → PieceCertificate (slots core piece)
  /-- External original-source semantic obligation: certificate fields are the
  actual equal-arm slots, scores, durations, factors and observed floor of THIS
  admitted source, preserving rows, IDs, strict positivity, registers, protected
  sites and chronology. No interpretation or constructor is supplied here. -/
  source_faithfulness : ∀ source core piece hf hc hp,
    SourceFaithful source core piece (certificate source core piece hf hc hp)
  source_length_identity : ∀ source core piece hf hc hp j,
    (certificate source core piece hf hc hp).length j = actualLength source core piece j
  piece_numeric_identity : ∀ source core piece hf hc hp j,
    (certificate source core piece hf hc hp).numeric j = uniformNumeric core piece j

theorem WholeFibreProvider.every_fitting_source_bounded
    {Source Core Piece : Type*} [Fintype Core] [Fintype Piece]
    {Fits : Source → Prop} {InCore : Source → Core → Prop}
    {InPiece : Source → Core → Piece → Prop} {slots : Core → Piece → ℕ}
    {actualLength : (source : Source) → (core : Core) → (piece : Piece) →
      Fin (slots core piece) → ℕ}
    {uniformNumeric : (core : Core) → (piece : Piece) →
      Fin (slots core piece) → NumericData}
    {SourceFaithful : (source : Source) → (core : Core) → (piece : Piece) →
      PieceCertificate (slots core piece) → Prop}
    (provider : WholeFibreProvider Source Core Piece Fits InCore InPiece slots
      actualLength uniformNumeric SourceFaithful)
    (source : Source) (hf : Fits source) :
    ∃ core, ∃ hc : InCore source core, ∃ piece, ∃ hp : InPiece source core piece,
      ∀ j, actualLength source core piece j ≤
        (uniformNumeric core piece j).independentBound := by
  obtain ⟨core, hc⟩ := provider.all_core_coverage source hf
  have hn := provider.excluded_core_sound source core hf hc
  obtain ⟨piece, hp⟩ := provider.all_fitting_piece_coverage source core hf hc hn
  refine ⟨core, hc, piece, hp, ?_⟩
  intro j
  have h := (provider.certificate source core piece hf hc hp).slot_count_bound j
  rw [provider.source_length_identity, provider.piece_numeric_identity] at h
  exact h

end UnifiedLean.G3.ConditionalZeroScore
