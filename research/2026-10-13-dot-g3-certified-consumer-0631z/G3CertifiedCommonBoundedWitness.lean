import G4ProtectedCommonRepresentative

/-!
# Supplied-certificate COMMON bounded witnesses

Contributor: dot (OpenAI), 13 October 2026.
UNCOMPILED SOURCE CANDIDATE. No Lean or Lake command has been run for this file.

This is the concrete consumer of the independently reviewed supplied-certificate
composition, not a certificate-acquisition algorithm or general G3 recognizer.
The sole direct research provider is the accepted 1614 source
G4ProtectedCommonRepresentative, SHA256
0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04.

No source target is a field of the input certificate. The conclusion is existence
of a bounded equivalent representative for each compatible actual realizer;
it does not bound the size of every original realizer. All future laws use the
same physical trace, parameter tuple, and retained-ID map.
-/

namespace DotG3.CertifiedCommonBoundedWitness

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.OriginalFixedIDControls
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1ExactSemidirectedPartnerAdmission
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open DotG4.ActualPositiveGridUniqueness DotG4.WeightedOrdinaryTreeLaw
open DotG4.WholeProfileDetermination DotG4.ProtectedCommonRepresentative
open scoped Classical BigOperators ENNReal

universe u v w z q a b

/-- Supplied normalized legal mixed-comb moments and their exact certificates.
This is proof-carrying input, not a parser or an executable certificate search. -/
structure SuppliedCombCertificates (Y : Type w) where
  level : Y × Y → Nat
  value : Y × Y → Nat → ℝ
  coeff : Y × Y → Nat → ℝ
  level_pos : ∀ ij, 0 < level ij
  nonzero : ∀ ij, sparsePolynomial (momentLevels (level ij)) (coeff ij) ≠ 0
  nonnegative : ∀ ij x, x ∈ Set.Icc (0 : ℝ) 1 →
    0 ≤ (sparsePolynomial (momentLevels (level ij)) (coeff ij)).eval x
  annihilates : ∀ ij,
    (∑ k ∈ momentLevels (level ij), coeff ij k * value ij k) = 0

variable {Y : Type w} [Fintype Y] [DecidableEq Y]

noncomputable def certificateGrid (cert : SuppliedCombCertificates Y)
    (ij : Y × Y) : Finset ℝ :=
  positiveCertificateGrid (cert.level ij) (cert.coeff ij)

noncomputable def supportCap (cert : SuppliedCombCertificates Y) : Nat :=
  (Finset.univ : Finset (Y × Y)).sup (fun ij => cert.level ij - 1)

noncomputable def hybridBudget (cert : SuppliedCombCertificates Y) (h : Nat) : Nat :=
  (2 * Fintype.card Y - 2 + 2*h) +
    (8 * Fintype.card Y - 8 + 6*h) * (supportCap cert - 1)

lemma certificateGrid_card_le (cert : SuppliedCombCertificates Y) (ij : Y × Y) :
    (certificateGrid cert ij).card ≤ supportCap cert := by
  have hlt := positiveCertificateGrid_card_lt (cert.level ij) (cert.coeff ij)
    (cert.nonzero ij)
  have hle : (certificateGrid cert ij).card ≤ cert.level ij - 1 := by
    dsimp only [certificateGrid]
    omega
  exact hle.trans (Finset.le_sup (f := fun ij => cert.level ij - 1) (Finset.mem_univ ij))

/-- The actual mixed row confines every supported configuration and every
original natural bank. Zero-mass configurations are not separately observed.
Neither a protected mask nor an outer-admission premise is used in this lemma. -/
theorem actual_mixed_certificate_support
    (cert : SuppliedCombCertificates Y) (P : PhysicalMarkedSource.{u,v,w} Y)
    {Config : Type q} [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask P.marked.source.network)
    (hmatch : ∀ i j k, k ∈ momentLevels (cert.level (i,j)) →
      randomizedLegalCombMoment P.marked.source.network P.marked.source.calendar P.registry
        P.probabilities P.rates ν masks i j k = cert.value (i,j) k) :
    ∀ cfg, ν cfg ≠ 0 → ∀ coin i j,
      realSurvival P.marked.source.network P.marked.source.calendar P.registry
        P.probabilities P.rates i j
        (overrideBank P.marked.source.network (masks cfg) coin) ∈ certificateGrid cert (i,j) := by
  classical
  intro cfg hcfg coin i j
  let ρ := configurationBankPMF ν
    (originalRegisterMeasure P.marked.source.network P.probabilities).toPMF
  let x : Config × CommonSeed P.marked.source.network → ℝ := fun s =>
    directedSurvival
      (maskedNormalizedTree P.marked.source.network P.marked.source.calendar
        P.registry P.rates (masks s.1) s.2) i j
  have hm (k : Nat) (hk : k ∈ momentLevels (cert.level (i,j))) :
      finiteBankMoment (positiveSupportPMF ρ) (fun s => x s.val) k = cert.value (i,j) k := by
    change (∑ s : {s : Config × CommonSeed P.marked.source.network // ρ s ≠ 0},
      (positiveSupportPMF ρ s).toReal * x s.val ^ k.choose 2) = _
    rw [positiveSupportPMF_sum ρ (fun s => x s ^ k.choose 2)]
    have hr : randomizedLegalCombMoment P.marked.source.network P.marked.source.calendar
        P.registry P.probabilities P.rates ν masks i j k = finiteBankMoment ρ x k :=
      (actual_randomized_legal_moment P.marked.source.network P.marked.source.calendar
        P.registry P.probabilities P.rates ν masks i j k
        (momentLevels_positive _ k hk)).trans (finiteBankMoment_enumeration _ _ _ _ _)
    exact hr.symm.trans (hmatch i j k hk)
  have hz : (∑ k ∈ momentLevels (cert.level (i,j)),
      cert.coeff (i,j) k * finiteBankMoment (positiveSupportPMF ρ) (fun s => x s.val) k) = 0 := by
    calc
      _ = ∑ k ∈ momentLevels (cert.level (i,j)),
          cert.coeff (i,j) k * cert.value (i,j) k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hm k hk]
      _ = 0 := cert.annihilates (i,j)
  have hrestrict := finiteBank_certificate_restricts (positiveSupportPMF ρ)
    (positiveSupportPMF_positive ρ) (fun s => x s.val)
    (fun s => directedSurvival_bounds _ _ _) (cert.level (i,j)) (cert.coeff (i,j))
    (cert.nonzero (i,j)) (cert.nonnegative (i,j)) hz
  have hb : (originalRegisterMeasure P.marked.source.network P.probabilities).toPMF coin ≠ 0 := by
    intro he
    have hp := original_bank_real_weight_positive P.marked.source.network P.probabilities coin
    simp only [he,ENNReal.toReal_zero] at hp
    exact lt_irrefl _ hp
  have hpair : ρ (cfg,coin) ≠ 0 := by
    dsimp only [ρ]
    rw [configurationBankPMF_apply]
    exact mul_ne_zero hcfg hb
  have hg := hrestrict ⟨(cfg,coin),hpair⟩
  simpa only [x,certificateGrid,
    maskedNormalizedTree_survival P.marked.source.network P.marked.source.calendar
      P.registry P.probabilities P.rates (masks cfg) coin i j] using hg

/-- Input-only certificate budget, followed by an arbitrary actual realizer.
All source-size, registry and future-law conclusions concern one representative
R constructed from one trace. The complete candidate registry is not supplied.

The unused-looking n >= 4 premise retains the reviewed original endpoint's
domain. No certificate acquisition, exact feasibility algorithm, timed law,
INDEPENDENT/BOTH law, or arbitrary unprotected parameter tie is asserted. -/
theorem actual_certificate_bounded_original_coverage
    (cert : SuppliedCombCertificates Y)
    (PE : Type a) (PH : Type b) [Fintype PE] [Fintype PH]
    (h : Nat) (hlabels : Fintype.card PE + Fintype.card PH ≤ h)
    (_hn : 4 ≤ Fintype.card Y)
    (P : PhysicalMarkedSource.{u,v,w} Y)
    (Config : Type q) [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask P.marked.source.network)
    (edgeLabels : PE ≃ P.marked.marks.edges) (hybridLabels : PH ≃ P.marked.marks.hybrids)
    (houter : HasOuterSemidirectedPartner P.marked.source)
    (hprotected : ∀ cfg, ProtectedMask P.marked (masks cfg))
    (hmatch : ∀ i j k, k ∈ momentLevels (cert.level (i,j)) →
      randomizedLegalCombMoment P.marked.source.network P.marked.source.calendar P.registry
        P.probabilities P.rates ν masks i j k = cert.value (i,j) k) :
    ∃ R : PhysicalMarkedSource.{u,v,w} Y,
      ∃ J : Hybrid R.marked.source.network ↪ Hybrid P.marked.source.network,
      ∃ D : Decoration P.marked.source R.marked.source,
      PhysicalPrimitiveProvenance P R J D ∧ PhysicalSteps P R ∧ EqualArmReduced R ∧
      (∀ k, J k ∈ P.marked.marks.hybrids ↔ k ∈ R.marked.marks.hybrids) ∧
      HasOuterSemidirectedPartner R.marked.source ∧
      Fintype.card (Hybrid R.marked.source.network) ≤ hybridBudget cert h ∧
      (∃ rr : Fin (hybridBudget cert h + 1), ∃ ids : Fin rr.val ≃ Hybrid R.marked.source.network,
        ∃ em : PE → Fin (edgeCount (Fintype.card Y) rr.val), ∃ hm : PH → Fin rr.val,
          (⟨rr,encode R.marked.source.network ids R.registry,em,hm⟩ :
            ProtectedCode Y PE PH (hybridBudget cert h)) ∈ protectedCodes PE PH (hybridBudget cert h) ∧
          encode R.marked.source.network ids R.registry ∈
            (registeredBinaryCutChildCodes : Finset (Code Y (Fin rr.val))) ∧
          Function.Injective em ∧ Function.Injective hm ∧
          (∀ a, D.recipe ((finiteEdgeNumbering R.marked.source.network ids).symm (em a)) =
            Recipe.raw (edgeLabels a).val) ∧
          (∀ a, J (ids (hm a)) = (hybridLabels a).val)) ∧
      (∀ (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
        (controls : Cfg → OriginalMask P.marked.source.network),
        randomizedTreeLaw R.marked.source.network R.marked.source.calendar R.registry
          R.probabilities R.rates μ (fun cfg k => controls cfg (J k)) =
        randomizedTreeLaw P.marked.source.network P.marked.source.calendar P.registry
          P.probabilities P.rates μ controls) ∧
      ∀ (Copy : Type z) [Fintype Copy] [DecidableEq Copy]
        (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
        (controls : Cfg → OriginalMask P.marked.source.network) (sample : Copy → Y),
        randomizedFullForestLaw R.marked.source.network R.marked.source.calendar R.registry
          R.probabilities R.rates μ (fun cfg k => controls cfg (J k)) sample =
        randomizedFullForestLaw P.marked.source.network P.marked.source.calendar P.registry
          P.probabilities P.rates μ controls sample := by
  cases Subsingleton.elim (inferInstance : DecidableEq Y) (Classical.decEq Y)
  obtain ⟨R,hPR,hred⟩ := actual_finite_equal_arm_reduction P
  let tr := Classical.choice (physicalSteps_trace hPR)
  let J := traceHybrid tr
  let D := traceDecoration tr
  have hprov := tracePrimitive tr
  have hmarks := traceHybrid_marks tr
  have hmom (i j : Y) (k : Nat) :
      randomizedLegalCombMoment R.marked.source.network R.marked.source.calendar R.registry
        R.probabilities R.rates ν (fun cfg k => masks cfg (J k)) i j k =
      randomizedLegalCombMoment P.marked.source.network P.marked.source.calendar P.registry
        P.probabilities P.rates ν masks i j k := by
    unfold randomizedLegalCombMoment
    rw [trace_joint_row_law tr _ Config ν masks _]
  have hgrid := actual_mixed_certificate_support cert R ν (fun cfg k => masks cfg (J k))
    (fun i j k hk => (hmom i j k).trans (hmatch i j k hk))
  obtain ⟨cfg,hcfg⟩ := ν.support_nonempty
  have hcfg' : ν cfg ≠ 0 := hcfg
  have hbound := equalArmReduced_physical_hybrid_bound R hred
    (fun k => masks cfg (J k))
    (projected_protected_mask P.marked R.marked J hmarks _ (hprotected cfg))
    (certificateGrid cert) (supportCap cert) (certificateGrid_card_le cert) (hgrid cfg hcfg')
  have hcount := markedSteps_count (physicalSteps_marked hPR)
  rw [hcount] at hbound
  have hprimitive : protectedCount P.marked.source.network P.marked.marks ≤ h := by
    have he := Fintype.card_congr edgeLabels
    have hh := Fintype.card_congr hybridLabels
    simp only [Fintype.card_coe] at he hh
    unfold protectedCount
    omega
  have hb : Fintype.card (Hybrid R.marked.source.network) ≤ hybridBudget cert h := by
    apply hbound.trans
    apply Nat.add_le_add
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hprimitive) _
    · exact Nat.mul_le_mul_right (supportCap cert - 1)
        (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hprimitive) _)
  exact ⟨R,J,D,hprov,hPR,hred,hmarks,
    markedSteps_outer (physicalSteps_marked hPR) houter,hb,
    protected_original_code_coverage P R J D hprov (hybridBudget cert h) hb PE PH
      edgeLabels hybridLabels,
    trace_tree_bucket_law tr,trace_joint_row_law tr⟩

end DotG3.CertifiedCommonBoundedWitness
