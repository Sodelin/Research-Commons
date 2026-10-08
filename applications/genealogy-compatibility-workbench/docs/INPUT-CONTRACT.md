# Input contract

## Sources

Each supplied source has a stable `source_id`, the family `positive-independent-one-bigon-two-pad`, two distinct original `arm_ids` and the five parameters `leading`, `left`, `right`, `weight`, `trailing`. Parameters must be exact integer/rational strings strictly inside (0,1); JSON floats are refused. The arm probability is applied to each CURRENT entering root independently. Arms undergo ordinary Kingman coalescence and pool without instantaneous merger. Existing subtrees are grafted intact. All histories and coins are private, with no shared registers or feedback.

Survival z means exp(-coalescent duration), not an inferred calendar date. Rates, molecular substitutions and physical sampling are not calibrated by this package.

## Experiments and targets

Experiments have stable `experiment_id`, `entering_roots` containing distinct `copy_id` and preserved `original_taxon_id`, and `readout` equal to `full_forest` or `root_count`. Several copies may have the same original taxon ID. All declared roots enter the same private two-port source interface. `original_taxon_id` records provenance; this package does not compile different population locations, ages, or source entry ports from those IDs. The root cap 1..5 is an implementation resource bound; it is not a scientific determining cutoff or a claim that five sampled specimens can supply five interface roots.

A full-forest outcome is a list of rooted binary trees: a leaf is its original copy ID; an internal tree is a two-element list. Every copy occurs once, across the entire forest. Child and root-list order are canonicalized without changing IDs. Root-count outcomes are integers between one and the declared root count.

Targets:

- `canonical_source`: the passive source-parameter orbit under arm exchange
- `original_arm_assignment`: the actual named arm parameters, which passive equality may not identify
- `trailing_survival`: just the trailing pad survival, allowing agreement even when other source parameters differ
- `catalogue_label`: caller-declared labels attached to source points; these labels are not independently verified biological facts

## Exact-law job

Use schema `genealogy-workbench/job-v1`; declare a named `catalogue` with coverage exactly `only_listed_sources`, its finite `sources`, `experiments`, `target`, and `exact_observations`. Each observed row contains `experiment_id` and `probabilities`: a list of `outcome`/`probability` objects. Absent coordinates mean zero. The row must normalize exactly. At least one observation row is required. All candidate rows use the same source object/parameters.

Empirical `records` or `sampling` must not appear in an exact-law job. The reverse mixture is also rejected. Unknown fields and duplicate JSON object keys are refused instead of silently ignored. See the executable input jobs under [examples](../examples/end-to-end/).

## Fresh-locus job

Use the same catalogue, experiments and target, with `records` and a `sampling` contract. The latter requires `unit: one_joint_outcome_per_locus`, the three explicit true assumptions `independent_fresh_loci`, `fixed_row_laws`, `row_selected_before_outcome`, `channel: declared_interface_readout`, rational `alpha` in (0,1), and rational `eta` in [0,1]. Each record contains stable `locus_id`, `experiment_id` and `outcome`.

Repeated identical records for one locus are ignored. Different outcomes or different rows with the same locus ID are rejected because this version has no multi-readout joint-channel compiler. Distinct IDs do not establish physical independence; the caller must justify the experimental-unit declaration. Within-row outcomes are assumed iid with a fixed distribution; a row may be chosen adaptively before its fresh outcome is observed. The catalogue, finite row menu and target are declared in advance, not chosen after inspecting the same data.

The discrepancy `eta` bounds the maximum coordinate difference between the fixed actual observed row law and the candidate clean row law, uniformly for the true source and all declared rows. It is a supplied premise, not inferred from bootstrap support.

## Exploratory FASTA

Sequence input is a list of `locus_id`/`fasta` records. Exactly four aligned taxon IDs must be consistent across loci. Unsupported ambiguous/gapped bases and changing taxon sets are rejected. A locus is counted once, and differing same-locus alignments are rejected. Original input digests and taxon-ID mappings remain in the report. Identical content under different locus IDs is flagged, not automatically treated as evidence of physical duplication or independence.

This separate channel supplies estimated unrooted quartets, not interface-root forests, exact calendar laws or a biological G6 target certificate.
