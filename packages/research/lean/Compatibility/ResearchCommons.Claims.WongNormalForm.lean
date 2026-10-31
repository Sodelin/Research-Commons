import WongSimplificationNormalForm

/-! Frozen CB-WONG-003 full-card owner/type correspondence, NOT adopted.
Original finite GARG and sample IDs, total local MRCA truncation, protected
coordinate-dependent contraction and maximal interval storage are retained.
Full graph preparation remains noncomputable; only original touching-list
merger is executable. No pipeline idempotence, timestamps, stochastic law,
production exporter/runtime, empirical ancestry or novelty claim. -/
set_option autoImplicit false
noncomputable section
namespace ResearchCommons.Claims.WongNormalForm
open WongGARG AncestryViews AncestryContraction WongIntervalNormalization
open WongLocalSimplification WongMRCATruncation WongIntervalCanonicalization
open WongSimplificationNormalForm
universe u v
variable {Node : Type u} {Coord : Type v} [Fintype Node] [LinearOrder Coord]
local instance (α : Type*) : DecidableEq α := Classical.decEq α
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem actual_canonical_resolved_normal_form (G : GARG Node Coord) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ x a b, H.AtLocus x a b ↔
        Contract ((truncate G).ExtractedAt x)
          (KeepSamplesAndBranching (truncate G) x) a b) ∧
      (∀ x, G.UniqueParentAt x → H.UniqueParentAt x ∧ NoNonsampleUnary H x) ∧
      H.SampleSupported ∧ H.breakpoints ⊆ G.breakpoints ∧
      (∀ x a s, a ∈ G.samples → s ∈ G.samples →
        (Reach (H.AtLocus x) a s ↔ Reach (G.AtLocus x) a s)) ∧
      (∀ x m s, G.samples.Nonempty → IsMRCA G x m → s ∈ G.samples →
        (Reach (H.AtLocus x) m s ↔ Reach (G.AtLocus x) m s)) ∧
      (∀ e ∈ H.records, ∀ I ∈ e.regions, ∀ J ∈ e.regions,
        I ≠ J → I.hi < J.lo ∨ J.hi < I.lo) ∧
      WongIntervalCanonicalization.canonicalize H = H :=
  WongSimplificationNormalForm.canonical_resolved_normal_form G

theorem total_mrca_truncation (G : GARG Node Coord) :
    ∃ H : GARG Node Coord,
      H.samples = G.samples ∧ H.NonemptyAnnotations ∧ H.CanonicalRecords ∧
      (∀ y p c, H.AtLocus y p c ↔ TruncatedAt G y p c) ∧
      H.SampleSupported ∧
      (∀ y, G.UniqueParentAt y → H.UniqueParentAt y) ∧
      H.breakpoints ⊆ G.breakpoints ∧
      (∀ y a s, a ∈ G.samples → s ∈ G.samples →
        (Reach (H.AtLocus y) a s ↔ Reach (G.AtLocus y) a s)) ∧
      (∀ y m s, IsMRCA G y m → s ∈ G.samples →
        (Reach (H.AtLocus y) m s ↔ Reach (G.AtLocus y) m s)) :=
  WongMRCATruncation.finite_mrca_truncation G

theorem mrca_unique_under_source_premises (G : GARG Node Coord) (x : Coord) (samples : G.samples.Nonempty) (unique : G.UniqueParentAt x)
    (common : ∃ a, Common G x a) : ∃! m, IsMRCA G x m :=
  WongMRCATruncation.exists_unique_mrca G x samples unique common

theorem empty_samples_no_truncated_edges (G : GARG Node Coord) (x : Coord) (samples : G.samples = ∅) (p c : Node) :
    ¬ TruncatedAt G x p c :=
  WongMRCATruncation.empty_samples_no_edges G x samples p c

theorem singleton_samples_no_truncated_edges (G : GARG Node Coord) (x : Coord) {s : Node} (samples : G.samples = {s}) (p c : Node) :
    ¬ TruncatedAt G x p c :=
  WongMRCATruncation.singleton_has_no_edges G x samples p c

theorem without_common_is_sample_support (G : GARG Node Coord) (x : Coord) (h : ¬ ∃ a, Common G x a) (p c : Node) :
    TruncatedAt G x p c ↔ G.ExtractedAt x p c :=
  WongMRCATruncation.no_common_no_extra_truncation G x h p c

theorem supported_material_can_be_removed (G : GARG Node Coord) (x : Coord) (samples : G.samples.Nonempty) {p c : Node}
    (hc : Common G x c) (edge : G.AtLocus x p c) :
    G.ExtractedAt x p c ∧ ¬ TruncatedAt G x p c :=
  WongMRCATruncation.supported_but_removed G x samples hc edge

theorem canonical_storage_full_local_relation (G : GARG Node Coord) (x : Coord) (a b : Node) :
    (canonicalize G).AtLocus x a b ↔ G.AtLocus x a b :=
  WongIntervalCanonicalization.canonicalize_at G x a b

theorem canonical_storage_semantic_unique (G H : GARG Node Coord)
    (hs : G.samples = H.samples)
    (heq : ∀ x a b, G.AtLocus x a b ↔ H.AtLocus x a b) :
    canonicalize G = canonicalize H :=
  WongIntervalCanonicalization.canonicalize_semantic_unique G H hs heq

theorem canonical_storage_idempotent (G : GARG Node Coord) :
    canonicalize (canonicalize G) = canonicalize G :=
  WongIntervalCanonicalization.canonicalize_idempotent G

theorem canonical_storage_active_topology (G : GARG Node Coord) (a b : Node) :
    (canonicalize G).Topology a b ↔ ∃ x, G.AtLocus x a b :=
  WongIntervalCanonicalization.canonicalize_topology G a b

theorem list_merge_union_for_every_list (L : List (Interval Coord)) (x : Coord) :
    Covers (mergeAdjacent L) x ↔ Covers L x :=
  WongIntervalCanonicalization.mergeAdjacent_covers L x

theorem ordered_merge_strictly_separated (L : List (Interval Coord)) (hL : Ordered L) :
    Separated (mergeAdjacent L) :=
  WongIntervalCanonicalization.mergeAdjacent_separated L hL

theorem ordered_merge_semantic_unique (L M : List (Interval Coord))
    (hL : Ordered L) (hM : Ordered M) (heq : ∀ x, Covers L x ↔ Covers M x) :
    mergeAdjacent L = mergeAdjacent M :=
  WongIntervalCanonicalization.mergeAdjacent_semantic_unique L M hL hM heq

theorem ordered_merge_idempotent (L : List (Interval Coord)) (hL : Ordered L) :
    mergeAdjacent (mergeAdjacent L) = mergeAdjacent L :=
  WongIntervalCanonicalization.mergeAdjacent_idempotent L hL

theorem canonical_storage_same_samples (G : GARG Node Coord) :
    (canonicalize G).samples = G.samples := rfl

theorem list_merge_reuses_input_endpoints (L : List (Interval Coord)) {J : Interval Coord}
    (hJ : J ∈ mergeAdjacent L) :
    (∃ I ∈ L, J.lo = I.lo) ∧ (∃ I ∈ L, J.hi = I.hi) :=
  ⟨mergeAdjacent_lo L hJ,mergeAdjacent_hi L hJ⟩

/-- Derived on the ORIGINAL source breakpoint cells, not supplied as an
extra retention certificate and not silently moved to a replacement graph. -/
theorem truncated_retention_on_original_source_cells (G : GARG Node Coord)
    (I : Interval Coord) (hI : I ∈ WongBreakpointCells.cells G.breakpoints)
    (x : Coord) (hx : I.Contains x) (a : Node) :
    KeepSamplesAndBranching (truncate G) x a ↔
      KeepSamplesAndBranching (truncate G) I.lo a := by
  have support := ((truncate G).extracted_eq_local_iff_sampleSupported).mpr
    (truncate_sample_supported G)
  have rel : ∀ p c, (truncate G).ExtractedAt x p c ↔
      (truncate G).ExtractedAt I.lo p c := by
    intro p c
    exact (support x p c).trans ((truncate_at_iff G x p c).trans
      (((truncatedPresentation G).constant I hI x hx p c).trans
        ((truncate_at_iff G I.lo p c).symm.trans (support I.lo p c).symm)))
  constructor
  · rintro (sample | ⟨p,c,hpc,hp,hc⟩)
    · exact Or.inl sample
    · exact Or.inr ⟨p,c,hpc,(rel a p).mp hp,(rel a c).mp hc⟩
  · rintro (sample | ⟨p,c,hpc,hp,hc⟩)
    · exact Or.inl sample
    · exact Or.inr ⟨p,c,hpc,(rel a p).mpr hp,(rel a c).mpr hc⟩
end ResearchCommons.Claims.WongNormalForm
