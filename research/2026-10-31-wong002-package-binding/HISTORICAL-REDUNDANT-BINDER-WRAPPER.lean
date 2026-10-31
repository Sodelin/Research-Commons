import WongMemoizedTracing

/-! Exact existing CB-WONG-002 owner/type interface. Existing Wong et al.
Appendix E and Samuel formalization retain credit. No new algorithm, machine
runtime, byte-format inverse or external conformance theorem is claimed.
Binding adoption is pending independent full-card correspondence review. -/
namespace ResearchCommons.Claims.WongRecordExtraction
open WongGARG WongRecordTracing WongSampleTracing WongMemoizedTracing
universe u v
variable {Node : Type u} {Coord : Type v} [DecidableEq Node] [Fintype Node] [LinearOrder Coord]

theorem actual_record_scan (G : GARG Node Coord) (x : Coord) (unique : G.UniqueParentAt x)
    (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records) (p c : Node) :
    lookup records x c = some p ↔ G.AtLocus x p c :=
  WongRecordTracing.lookup_represents G x unique records recordIds p c

theorem reference_record_extraction (G : GARG Node Coord) (x : Coord)
    (unique : G.UniqueParentAt x) (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples)
    (p c : Node) :
    extract (lookup records x) (Fintype.card Node) samples c = some p ↔
      G.ExtractedAt x p c :=
  WongRecordTracing.records_to_sample_array G x unique records recordIds samples sampleIds p c

theorem memoized_record_extraction (G : GARG Node Coord) (x : Coord)
    (unique : G.UniqueParentAt x) (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples)
    (p c : Node) :
    memoExtract (lookup records x) (Fintype.card Node) samples c = some p ↔
      G.ExtractedAt x p c :=
  WongMemoizedTracing.records_to_memoized_sample_array G x unique records recordIds samples sampleIds p c

theorem sample_support_round_trip (G : GARG Node Coord)
    (unique : ∀ x, G.UniqueParentAt x) (records : List (EdgeRecord Node Coord))
    (recordIds : ∀ e, e ∈ records ↔ e ∈ G.records)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples) :
    (∀ x p c, memoExtract (lookup records x) (Fintype.card Node) samples c = some p ↔
      G.AtLocus x p c) ↔ G.SampleSupported :=
  WongMemoizedTracing.memoized_records_round_trip_iff G unique records recordIds samples sampleIds

theorem abstract_counter_bounds [Fintype Node] (parent : Node → Option Node)
    (fuel : Nat) (samples : List Node) :
    let r := run parent fuel samples (fun _ => none)
    r.writes ≤ Fintype.card Node ∧
    r.checks ≤ r.writes + samples.length ∧
    r.lookups ≤ r.writes + samples.length :=
  WongMemoizedTracing.memoized_cost_bounds parent fuel samples

theorem derived_node_count_fuel (G : GARG Node Coord) (x : Coord)
    (parent : Node → Option Node)
    (represents : ∀ a b, parent b = some a ↔ G.AtLocus x a b)
    (samples : List Node) (sampleIds : ∀ s, s ∈ samples ↔ s ∈ G.samples)
    (p c : Node) :
    memoExtract parent (Fintype.card Node) samples c = some p ↔ G.ExtractedAt x p c :=
  WongMemoizedTracing.actual_memoized_extraction G x parent represents samples sampleIds p c

end ResearchCommons.Claims.WongRecordExtraction
