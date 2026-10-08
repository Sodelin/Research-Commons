# Shared molecular interface, version molecular-apps-v1

This is the intentionally shareable interface specification, not a copy of restricted implementation. CLI and future GUI call the same application services. Implementation and science are experimental; a successful computation establishes neither measured RNA nor a biological conclusion.

## Inputs

| Object | Required information and semantics |
|---|---|
| Reference window | Assembly hg38/GRCh38, chromosome, zero-based start, forward reference sequence, explicit downstream guard, reference source, SHA256 of reference plus guard. End equals start plus input length. |
| Transcript annotation | Versioned gene and transcript IDs, zero-based half-open bounds, +/− strand, sorted disjoint exon intervals, source and annotation version. Initial module requires the complete transcript within the window. |
| Context | Reference and annotation, explicit UBERON/CL tissue, requested model version, ordered unique output modalities, preprocessing policy. Settings digest binds every comparison to the same context. |
| Variant | ID, chromosome, one-based VCF anchor, nonempty uppercase REF/ALT. Full REF span must match the reference. |
| Phase | cis, trans, unknown or hypothetical; cis/trans require explicit supporting evidence. Evidence is supplied and recorded, not independently established by a prediction. |
| Endpoint | Unique ID, family, actual requested modality, region, aggregation, comparison scale, positive pseudocount, alignment policy and optional annotated site windows. |

The first haplotype module handles exactly two variants. Four matched single-sequence conditions are REF, A, B and A+B. Unknown and trans phase do not assert an observed combined haplotype; A+B remains counterfactual. Separate sequences are not silently combined into a diploid/person phenotype. Overlapping edits, conflicting references, unsupported complex delins and cropped endpoint bases are refused.

Indels use original-reference coordinates, a fixed left anchor and authenticated downstream guard, then crop to the original length. Piecewise maps record retained bases, inserted segments, deletions and cropping. Initial scoring permits mapped per-base tracks, excludes inserted bases, zero-fills deletions and keeps the original reference denominator. This explicitly declared application policy differs from the official variant scorer's insertion-max alignment. Coarse indel tracks remain unsupported.

## Predictions and outputs

Prediction records carry scenario, actual sequence digest, settings digest, evidence class and identified tracks. Tracks carry modality, values, coordinate origin, bin size, strand, tissue, gene/transcript annotation and exact experiment name. Every matched comparison checks settings, sequence, track identity and coordinate coverage. Tissue-agnostic splice-site tracks are explicitly marked; they do not acquire tissue specificity from the request.

| Endpoint family | Initial semantics |
|---|---|
| Expression/abundance | RNA_SEQ is a direct predicted coverage track. Annotated-exon sum/mean and declared log/linear transformations are derived application quantities. They are not measured RNA or a calibrated abundance assay. |
| Splice sites | Direct predicted site probabilities; selected region/aggregation and resulting differences are derived. Keep modality and acceptor/donor track selection explicit. |
| Splice usage | Direct predicted site-use fractions; aggregate and effect direction remain separate from expression. |
| Splice junctions | Official model supports a junction-specific output structure. Initial positional-track adapter does not implement it; report unavailable rather than flattening or fabricating it. |
| Polyadenylation | Initial two-annotated-window distal/proximal coverage ratio is derived from RNA_SEQ when assumptions are met. It is not a direct PAS output and is distinct from the official multisplit PAS scorer. Without site annotations or suitable tracks it is unavailable. |

For a declared endpoint value y on the selected scale, the interaction statistic is `yAB − yA − yB + yREF`. Raw endpoint values and changes are retained. This is predicted nonadditivity on that scale; AVI percentile ranks are not joint effects and an interaction is not experimentally established by computation.

Result states: SUCCESS, INVALID_INPUT, UNSUPPORTED, UNKNOWN, RESOURCE_LIMIT and EXECUTION_FAILURE. Results separately record successful computation, evidence `MOCK_SYNTHETIC` or `REAL_MODEL_PREDICTION`, unavailable reasons and `biological_conclusion_established: false`. Unknown phase can accompany successfully computed scenarios. Resource failure does not become a negative molecular result.

## Provider and entry points

A provider exposes capabilities for the context and `predict_sequence(context, scenario, sequence)`. The offline default is a deterministic synthetic software fixture. The live adapter uses the official Python v1 SDK, explicit ModelVersion selection and exact track names; it does not install an SDK, create an account or accept terms. Supported SDK sequence lengths are 16,384; 131,072; 524,288 and 1,048,576 bases. Requested model enum and SDK version can be recorded; an immutable server-weight checkpoint is not exposed by this interface and must not be claimed pinned.

Illustrative CLI calls from the restricted application project:

```sh
python3 -m molecular_apps haplotype examples/tert-public-reference-mock.json --provider mock --core-binary /path/to/molecular-haplotype-core
python3 -m molecular_apps rna examples/tert-rna-public-reference-mock.json --provider mock
python3 -m molecular_apps access-check
```

These examples do not imply execution. Exact receipts will state what actually ran. The public reference exercise uses chr5:1,295,113 and 1,295,135 G>A, hypothetical cis phase, liver UBERON:0002107, hg38 and versioned TERT transcript annotation. No personal genome is used.
