import G3CertifiedCommonBoundedWitness

/-! Thin source-only packaging of the accepted 0223 supplied-certificate
consequence. The literal 400153aa consumer and 0616 physical provider are
unchanged. External labels/tables/readouts are fixed before a source; no
source, representative, desired bound or law is an input-certificate field.
This file has not been elaborated or selected into an existing target. -/
namespace Astra.CertifiedCommonExternal

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualGraphNormalization G1DecoratedOriginalProvenance
open G1ExactSemidirectedPartnerAdmission
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open DotG4.ActualSparseCertificateExistence DotG4.WeightedOrdinaryTreeLaw
open DotG4.WholeProfileDetermination DotG4.ProtectedCommonRepresentative
open DotG3.CertifiedCommonBoundedWitness
open scoped Classical

universe u v w a b q s z t
variable {Y : Type w} [Fintype Y] [DecidableEq Y]
variable {PE : Type a} {PH : Type b} [Fintype PE] [Fintype PH]

/-- Actual physical source plus bijections onto precisely its marked carriers. -/
structure LabelledSource (Y : Type w) [Fintype Y] (PE : Type a) (PH : Type b) where
  physical : PhysicalMarkedSource.{u,v,w} Y
  edges : PE ≃ physical.marked.marks.edges
  hybrids : PH ≃ physical.marked.marks.hybrids

/-- Marked preimages are chosen coherently. Individual cardinal equalities
are derived from both injections and the preserved TOTAL, not assumed. -/
theorem marked_label_equivalences
    (P R : PhysicalMarkedSource.{u,v,w} Y)
    (J : Hybrid R.marked.source.network ↪ Hybrid P.marked.source.network)
    (D : Decoration P.marked.source R.marked.source)
    (hp : PhysicalPrimitiveProvenance P R J D) (hs : PhysicalSteps P R)
    (eP : PE ≃ P.marked.marks.edges) (hP : PH ≃ P.marked.marks.hybrids) :
    ∃ eR : PE ≃ R.marked.marks.edges, ∃ hR : PH ≃ R.marked.marks.hybrids,
      (∀ a, D.recipe (eR a).val = Recipe.raw (eP a).val) ∧
      (∀ a, J (hR a).val = (hP a).val) := by
  classical
  have he a := hp.protected_primitives.1 (eP a).val (eP a).property
  choose ef hef hraw using he
  have hh a := hp.protected_primitives.2 (hP a).val (hP a).property
  choose hf hhf hvertex using hh
  let f : PE → R.marked.marks.edges := fun a => ⟨ef a, hef a⟩
  let g : PH → R.marked.marks.hybrids := fun a => ⟨hf a, hhf a⟩
  have hJ (a : PH) : J (hf a) = (hP a).val := by
    apply Subtype.ext
    exact (hp.hybrid_vertex (hf a)).symm.trans (hvertex a)
  have fi : Function.Injective f := by
    intro a c hac
    apply eP.injective
    apply Subtype.ext
    have hr := congrArg (fun e : R.marked.marks.edges => D.recipe e.val) hac
    exact Recipe.raw.inj ((hraw a).symm.trans (hr.trans (hraw c)))
  have gi : Function.Injective g := by
    intro a c hac
    apply hP.injective
    apply Subtype.ext
    have hr := congrArg (fun h : R.marked.marks.hybrids => J h.val) hac
    exact (hJ a).symm.trans (hr.trans (hJ c))
  have ele : Fintype.card PE ≤ R.marked.marks.edges.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f fi
  have hle : Fintype.card PH ≤ R.marked.marks.hybrids.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g gi
  have ep : Fintype.card PE = P.marked.marks.edges.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr eP
  have hp' : Fintype.card PH = P.marked.marks.hybrids.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr hP
  have total := markedSteps_count (physicalSteps_marked hs)
  unfold protectedCount at total
  rw [← ep, ← hp'] at total
  have ec : Fintype.card PE = Fintype.card R.marked.marks.edges := by
    rw [Fintype.card_coe]
    omega
  have hc : Fintype.card PH = Fintype.card R.marked.marks.hybrids := by
    rw [Fintype.card_coe]
    omega
  let eR := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨fi,ec⟩)
  let hR := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨gi,hc⟩)
  exact ⟨eR,hR,hraw,hJ⟩

/-- External controls mean none outside the label image. This pure extension
identity is credited to the earlier optional 0435 interface proposal. -/
noncomputable def labelMask {Label Site : Type*}
    (mark : Label → Site) (table : Label → Option Bool) : Site → Option Bool :=
  Function.extend mark table (fun _ => none)

lemma labelMask_on {Label Site : Type*} (mark : Label → Site)
    (hi : Function.Injective mark) (table : Label → Option Bool) (a : Label) :
    labelMask mark table (mark a) = table a :=
  hi.extend_apply table (fun _ => none) a

lemma labelMask_off {Label Site : Type*} (mark : Label → Site)
    (table : Label → Option Bool) (x : Site) (hx : ¬ ∃ a, mark a = x) :
    labelMask mark table x = none := Function.extend_apply' table (fun _ => none) x hx

theorem labelMask_pullback {Label Old New : Type*} (J : New ↪ Old)
    (old : Label → Old) (new : Label → New) (hi : Function.Injective old)
    (hf : ∀ a, J (new a) = old a) (table : Label → Option Bool) :
    (fun k => labelMask old table (J k)) = labelMask new table := by
  have hn : Function.Injective new := by
    intro a c h
    apply hi
    rw [← hf a, ← hf c, h]
  funext k
  by_cases hk : ∃ a, new a = k
  · obtain ⟨a,rfl⟩ := hk
    rw [hf a, labelMask_on old hi, labelMask_on new hn]
  · have ho : ¬ ∃ a, old a = J k := by
      rintro ⟨a,ha⟩
      exact hk ⟨a,J.injective ((hf a).trans ha)⟩
    rw [labelMask_off old table (J k) ho, labelMask_off new table k hk]

noncomputable def mask (S : LabelledSource.{u,v,w,a,b} Y PE PH)
    (table : PH → Option Bool) : OriginalMask S.physical.marked.source.network :=
  labelMask (fun a => (S.hybrids a).val) table

lemma mask_protected (S : LabelledSource.{u,v,w,a,b} Y PE PH)
    (table : PH → Option Bool) : ProtectedMask S.physical.marked (mask S table) := by
  intro k hk
  apply labelMask_off
  rintro ⟨a,ha⟩
  exact hk (ha ▸ (S.hybrids a).property)

noncomputable def externalTreeLaw (S : LabelledSource.{u,v,w,a,b} Y PE PH)
    {Cfg : Type q} [Fintype Cfg] (μ : PMF Cfg) (tables : Cfg → PH → Option Bool) :=
  randomizedTreeLaw S.physical.marked.source.network S.physical.marked.source.calendar
    S.physical.registry S.physical.probabilities S.physical.rates μ (fun c => mask S (tables c))

noncomputable def externalForestLaw (S : LabelledSource.{u,v,w,a,b} Y PE PH)
    {Cfg : Type q} [Fintype Cfg] {Copy : Type z} [Fintype Copy] [DecidableEq Copy]
    (μ : PMF Cfg) (tables : Cfg → PH → Option Bool) (sample : Copy → Y) :=
  randomizedFullForestLaw S.physical.marked.source.network S.physical.marked.source.calendar
    S.physical.registry S.physical.probabilities S.physical.rates μ
    (fun c => mask S (tables c)) sample

/-- A proved conclusion, never an input realizer/certificate field. -/
structure Transfer (P R : LabelledSource.{u,v,w,a,b} Y PE PH)
    (J : Hybrid R.physical.marked.source.network ↪ Hybrid P.physical.marked.source.network)
    (D : Decoration P.physical.marked.source R.physical.marked.source) : Prop where
  provenance : PhysicalPrimitiveProvenance P.physical R.physical J D
  steps : PhysicalSteps P.physical R.physical
  reduced : EqualArmReduced R.physical
  marked_iff : ∀ k, J k ∈ P.physical.marked.marks.hybrids ↔
    k ∈ R.physical.marked.marks.hybrids
  raw : ∀ a, D.recipe (R.edges a).val = Recipe.raw (P.edges a).val
  hybrid : ∀ a, J (R.hybrids a).val = (P.hybrids a).val
  tree : ∀ (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
    (tables : Cfg → PH → Option Bool), externalTreeLaw R μ tables = externalTreeLaw P μ tables

theorem Transfer.forest {P R : LabelledSource.{u,v,w,a,b} Y PE PH} {J D}
    (tr : Transfer.{u,v,w,a,b,q} P R J D)
    {Cfg : Type q} [Fintype Cfg] {Copy : Type z} [Fintype Copy] [DecidableEq Copy]
    (μ : PMF Cfg) (tables : Cfg → PH → Option Bool) (sample : Copy → Y) :
    externalForestLaw R μ tables sample = externalForestLaw P μ tables sample := by
  unfold externalForestLaw
  rw [randomizedFullForestLaw_eq_tree_bind, randomizedFullForestLaw_eq_tree_bind]
  change (externalTreeLaw R μ tables).bind _ = (externalTreeLaw P μ tables).bind _
  rw [tr.tree Cfg μ tables]

theorem Transfer.channel {P R : LabelledSource.{u,v,w,a,b} Y PE PH} {J D}
    (tr : Transfer.{u,v,w,a,b,q} P R J D)
    {Cfg : Type q} [Fintype Cfg] {Copy : Type z} [Fintype Copy] [DecidableEq Copy]
    {Out : Type t} (μ : PMF Cfg) (tables : Cfg → PH → Option Bool) (sample : Copy → Y)
    (channel : Finset (UnrankedTree Copy) → PMF Out) :
    (externalForestLaw R μ tables sample).bind channel =
      (externalForestLaw P μ tables sample).bind channel := by
  rw [tr.forest μ tables sample]

theorem Transfer.readout {P R : LabelledSource.{u,v,w,a,b} Y PE PH} {J D}
    (tr : Transfer.{u,v,w,a,b,q} P R J D)
    {Cfg : Type q} [Fintype Cfg] {Copy : Type z} [Fintype Copy] [DecidableEq Copy]
    {Out : Type t} (μ : PMF Cfg) (tables : Cfg → PH → Option Bool) (sample : Copy → Y)
    (readout : Finset (UnrankedTree Copy) → Out) :
    (externalForestLaw R μ tables sample).map readout =
      (externalForestLaw P μ tables sample).map readout := by
  rw [tr.forest μ tables sample]

def parameterCondition (S : LabelledSource.{u,v,w,a,b} Y PE PH)
    (Q : (PE → ℝ) → (PE → ℝ) → (PE → ℝ) → (PH → ℝ) → Prop) : Prop :=
  Q (fun a => S.physical.rates.edge (S.edges a).val)
    (fun a => S.physical.marked.source.calendar.age
      (S.physical.marked.source.network.graph.source (S.edges a).val))
    (fun a => S.physical.marked.source.calendar.age
      (S.physical.marked.source.network.graph.target (S.edges a).val))
    (fun a => S.physical.probabilities.gamma (S.hybrids a).val)

theorem Transfer.parameters {P R : LabelledSource.{u,v,w,a,b} Y PE PH} {J D}
    (tr : Transfer.{u,v,w,a,b,q} P R J D)
    (Q : (PE → ℝ) → (PE → ℝ) → (PE → ℝ) → (PH → ℝ) → Prop) :
    parameterCondition R Q ↔ parameterCondition P Q :=
  protected_parameter_constraints_preserved P.physical R.physical J D tr.provenance
    (fun a => (P.edges a).val) (fun a => (R.edges a).val)
    (fun a => (P.hybrids a).val) (fun a => (R.hybrids a).val) tr.raw tr.hybrid Q

/-- Numeric code maps are rebuilt from the SAME marked bijections. -/
def CoherentCodeCoverage (S : LabelledSource.{u,v,w,a,b} Y PE PH) (B : Nat) : Prop :=
  ∃ rr : Fin (B+1), ∃ ids : Fin rr.val ≃ Hybrid S.physical.marked.source.network,
    let em := fun a => finiteEdgeNumbering S.physical.marked.source.network ids (S.edges a).val
    let hm := fun a => ids.symm (S.hybrids a).val
    (⟨rr,encode S.physical.marked.source.network ids S.physical.registry,em,hm⟩ :
      ProtectedCode Y PE PH B) ∈ protectedCodes PE PH B ∧
    encode S.physical.marked.source.network ids S.physical.registry ∈
      (registeredBinaryCutChildCodes : Finset (Code Y (Fin rr.val))) ∧
    Function.Injective em ∧ Function.Injective hm

theorem coherent_code_coverage (S : LabelledSource.{u,v,w,a,b} Y PE PH) (B : Nat)
    (hb : Fintype.card (Hybrid S.physical.marked.source.network) ≤ B) :
    CoherentCodeCoverage S B := by
  classical
  let rr : Fin (B+1) := ⟨Fintype.card (Hybrid S.physical.marked.source.network),by omega⟩
  let ids : Fin rr.val ≃ Hybrid S.physical.marked.source.network := (Fintype.equivFin _).symm
  refine ⟨rr,ids,Finset.mem_univ _,?_,?_,?_⟩
  · exact every_registered_source_survives_filter S.physical.marked.source.network ids
      S.physical.registry S.physical.marked.source.cutChild
  · intro a c hac
    apply S.edges.injective
    apply Subtype.ext
    exact (finiteEdgeNumbering S.physical.marked.source.network ids).injective hac
  · intro a c hac
    apply S.hybrids.injective
    apply Subtype.ext
    exact ids.symm.injective hac

theorem bounded_external_representative
    (cert : SuppliedCombCertificates Y) (h : Nat)
    (hlabels : Fintype.card PE + Fintype.card PH ≤ h) (hn : 4 ≤ Fintype.card Y)
    (P : LabelledSource.{u,v,w,a,b} Y PE PH)
    (Config : Type q) [Fintype Config] (ν : PMF Config)
    (tables : Config → PH → Option Bool)
    (houter : HasOuterSemidirectedPartner P.physical.marked.source)
    (hmatch : ∀ i j k, k ∈ momentLevels (cert.level (i,j)) →
      randomizedLegalCombMoment P.physical.marked.source.network
        P.physical.marked.source.calendar P.physical.registry P.physical.probabilities
        P.physical.rates ν (fun c => mask P (tables c)) i j k = cert.value (i,j) k) :
    ∃ R : LabelledSource.{u,v,w,a,b} Y PE PH,
      ∃ J : Hybrid R.physical.marked.source.network ↪ Hybrid P.physical.marked.source.network,
      ∃ D : Decoration P.physical.marked.source R.physical.marked.source,
      Transfer.{u,v,w,a,b,q} P R J D ∧
      HasOuterSemidirectedPartner R.physical.marked.source ∧
      Fintype.card (Hybrid R.physical.marked.source.network) ≤ hybridBudget cert h ∧
      CoherentCodeCoverage R (hybridBudget cert h) := by
  obtain ⟨R,J,D,hprov,hsteps,hred,hmarks,hout,hbound,_hcodes,htree,_hforest⟩ :=
    actual_certificate_bounded_original_coverage cert PE PH h hlabels hn P.physical
      Config ν (fun c => mask P (tables c)) P.edges P.hybrids houter
      (fun c => mask_protected P (tables c)) hmatch
  obtain ⟨eR,hR,her,hhr⟩ := marked_label_equivalences P.physical R J D hprov hsteps
    P.edges P.hybrids
  let T : LabelledSource.{u,v,w,a,b} Y PE PH := ⟨R,eR,hR⟩
  have hi : Function.Injective (fun a => (P.hybrids a).val) := by
    intro a c hac
    exact P.hybrids.injective (Subtype.ext hac)
  have ht : Transfer.{u,v,w,a,b,q} P T J D := by
    refine ⟨hprov,hsteps,hred,hmarks,her,hhr,?_⟩
    intro Cfg _ μ controls
    have hm : (fun c k => mask P (controls c) (J k)) =
        (fun c => mask T (controls c)) := by
      funext c
      exact labelMask_pullback J (fun a => (P.hybrids a).val)
        (fun a => (T.hybrids a).val) hi hhr (controls c)
    have he := htree Cfg μ (fun c => mask P (controls c))
    rw [hm] at he
    exact he
  exact ⟨T,J,D,ht,hout,hbound,coherent_code_coverage T _ hbound⟩

/-- Finite row carriers, their joint distributions and observations are
external data. Q is restricted by its type to the protected numeric frame.
No physical source, outer witness or bounded target is stored here. -/
structure FixedInput (Y : Type w) (PE : Type a) (PH : Type b)
    (Config : Type q) (Row : Type s) (Copy : Row → Type z)
    (Cfg : Row → Type q) (Out : Row → Type t) where
  cert : SuppliedCombCertificates Y
  ν : PMF Config
  exposing : Config → PH → Option Bool
  μ : ∀ row, PMF (Cfg row)
  controls : ∀ row, Cfg row → PH → Option Bool
  sample : ∀ row, Copy row → Y
  channel : ∀ row, Finset (UnrankedTree (Copy row)) → PMF (Out row)
  observed : ∀ row, PMF (Out row)
  Q : (PE → ℝ) → (PE → ℝ) → (PE → ℝ) → (PH → ℝ) → Prop

section FixedInputRealization
variable {Config : Type q} [Fintype Config] {Row : Type s} [Fintype Row]
variable {Copy : Row → Type z} {Cfg : Row → Type q} {Out : Row → Type t}
variable [∀ row, Fintype (Copy row)] [∀ row, DecidableEq (Copy row)]
variable [∀ row, Fintype (Cfg row)]

def Realizes (I : FixedInput Y PE PH Config Row Copy Cfg Out)
    (P : LabelledSource.{u,v,w,a,b} Y PE PH) : Prop :=
  HasOuterSemidirectedPartner P.physical.marked.source ∧
  (∀ i j k, k ∈ momentLevels (I.cert.level (i,j)) →
    randomizedLegalCombMoment P.physical.marked.source.network
      P.physical.marked.source.calendar P.physical.registry P.physical.probabilities
      P.physical.rates I.ν (fun c => mask P (I.exposing c)) i j k = I.cert.value (i,j) k) ∧
  parameterCondition P I.Q ∧
  ∀ row, (externalForestLaw P (I.μ row) (I.controls row) (I.sample row)).bind
    (I.channel row) = I.observed row

/-- Uniform full-law transport also preserves the fixed padded legal moments;
the common tree-law evaluator makes copy-universe changes explicit. -/
theorem Transfer.exposing_moments {P R : LabelledSource.{u,v,w,a,b} Y PE PH} {J D}
    (tr : Transfer.{u,v,w,a,b,q} P R J D) (ν : PMF Config)
    (tables : Config → PH → Option Bool) (i j : Y) (k : Nat) :
    randomizedLegalCombMoment R.physical.marked.source.network
      R.physical.marked.source.calendar R.physical.registry R.physical.probabilities
      R.physical.rates ν (fun c => mask R (tables c)) i j k =
    randomizedLegalCombMoment P.physical.marked.source.network
      P.physical.marked.source.calendar P.physical.registry P.physical.probabilities
      P.physical.rates ν (fun c => mask P (tables c)) i j k := by
  unfold randomizedLegalCombMoment
  rw [tr.forest ν tables]

/-- One representative, with the same fixed input and no desired output law
assumed, before every future external table/readout/channel via Transfer. -/
theorem realizes_bounded_representative
    (I : FixedInput Y PE PH Config Row Copy Cfg Out) (h : Nat)
    (hlabels : Fintype.card PE + Fintype.card PH ≤ h) (hn : 4 ≤ Fintype.card Y)
    (P : LabelledSource.{u,v,w,a,b} Y PE PH) (hP : Realizes I P) :
    ∃ R : LabelledSource.{u,v,w,a,b} Y PE PH,
      ∃ J : Hybrid R.physical.marked.source.network ↪ Hybrid P.physical.marked.source.network,
      ∃ D : Decoration P.physical.marked.source R.physical.marked.source,
      Transfer.{u,v,w,a,b,q} P R J D ∧ Realizes I R ∧
      Fintype.card (Hybrid R.physical.marked.source.network) ≤ hybridBudget I.cert h ∧
      CoherentCodeCoverage R (hybridBudget I.cert h) := by
  obtain ⟨R,J,D,tr,houter,hbound,hcode⟩ := bounded_external_representative I.cert h hlabels hn
    P Config I.ν I.exposing hP.1 hP.2.1
  refine ⟨R,J,D,tr,?_,hbound,hcode⟩
  refine ⟨houter,?_,(tr.parameters I.Q).mpr hP.2.2.1,?_⟩
  · intro i j k hk
    exact (tr.exposing_moments I.ν I.exposing i j k).trans (hP.2.1 i j k hk)
  · intro row
    exact (tr.channel (I.μ row) (I.controls row) (I.sample row) (I.channel row)).trans
      (hP.2.2.2 row)

/-- Conditional bounded existence for the explicit fixed-input class. This is
semantic completeness of a structural superset, not a feasibility algorithm. -/
theorem fixed_input_bounded_realizer_iff
    (I : FixedInput Y PE PH Config Row Copy Cfg Out) (h : Nat)
    (hlabels : Fintype.card PE + Fintype.card PH ≤ h) (hn : 4 ≤ Fintype.card Y) :
    (∃ P : LabelledSource.{u,v,w,a,b} Y PE PH, Realizes I P) ↔
    ∃ R : LabelledSource.{u,v,w,a,b} Y PE PH, Realizes I R ∧
      Fintype.card (Hybrid R.physical.marked.source.network) ≤ hybridBudget I.cert h ∧
      CoherentCodeCoverage R (hybridBudget I.cert h) := by
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨R,J,D,_tr,hR,hbound,hcode⟩ := realizes_bounded_representative I h hlabels hn P hP
    exact ⟨R,hR,hbound,hcode⟩
  · rintro ⟨R,hR,_hbound,_hcode⟩
    exact ⟨R,hR⟩

end FixedInputRealization

#check marked_label_equivalences
#check bounded_external_representative
#check realizes_bounded_representative
#check fixed_input_bounded_realizer_iff
#print axioms marked_label_equivalences
#print axioms labelMask_pullback
#print axioms Transfer.forest
#print axioms Transfer.channel
#print axioms Transfer.readout
#print axioms Transfer.parameters
#print axioms coherent_code_coverage
#print axioms bounded_external_representative
#print axioms Transfer.exposing_moments
#print axioms realizes_bounded_representative
#print axioms fixed_input_bounded_realizer_iff

end Astra.CertifiedCommonExternal
