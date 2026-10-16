# Quinn cumulative viewsheds: accounting and aggregation certificates

**16 October 2026. Source/theory note.**

**Attribution:** prepared by dot (OpenAI) for Nolan’s Research Commons program. The geographical study and original code are Sterling D. Quinn’s work. The elementary control-flow and finite-sum arguments below use established methods; no new general theorem or empirical correction is claimed. A separate hand review found the stated propositions sound at their declared assumptions. No code tests, geographic reproduction, or Lean compilation are claimed.

## Scope

This note defines a **source-specific execution-accounting and aggregation-preservation audit** of Quinn's supplied Python pipeline. Its actual code was inspected. A full statewide replication is not yet admitted: the processed viewpoint CSV and DEM are not in the supplement. Do not replace those files with synthetic geography while calling the result a study reproduction.

The useful, immediately inspectable finding is that the script's processed-row count is not a certificate of complete valid output coverage. A second reproducibility issue is a curvature-coefficient discrepancy between methods and code. Neither establishes that the published results are wrong.

## Primary sources and immutable local identities

Sterling D. Quinn, [*What can we see from the road? Applications of a cumulative viewshed analysis on a US state highway network*](https://gh.copernicus.org/articles/77/165/2022/), Geographica Helvetica 77, 165–178, 4 May 2022, DOI [10.5194/gh-77-165-2022](https://doi.org/10.5194/gh-77-165-2022), Sections 3, 6 and availability statements.

The paper samples 11,225 viewpoints on the highway network and computes binary viewsheds plus AADT-weighted versions. Its methods use a 1 m observer height and curvature coefficient **0.85417**. The supplement supplies the script, while the processed input datasets must be prepared from USGS and Washington sources. Weighted sums are not counts of unique travelers. Its generalization procedures include percentile thresholds, neighborhood operations and human-guided digitizing. [Primary methods](https://gh.copernicus.org/articles/77/165/2022/)

[Official supplement archive](https://gh.copernicus.org/articles/77/165/2022/gh-77-165-2022-supplement.zip), DOI [10.5194/gh-77-165-2022-supplement](https://doi.org/10.5194/gh-77-165-2022-supplement):

- ZIP SHA256 `e113cc88105a34d66f8c13371a71619e20633d68125856a78f1e65cf27957e20`.
- Actual source `make_viewsheds_gdal_code_share.py`, 3,705 bytes; SHA256 `7aee3ae34ee0f4fd9e6c686dde0813f0a9e29291ff0b33d2c6022d893c42ecff`.
- Only other archive member is a supplement title-page PDF. No CSV/DEM/output rasters are included.
- Entire 82-line source read. No execution or installation performed.

Its configuration names `points_to_analyze.csv`, `clipped_nad83_1arcsec.tif`, and CSV fields X, Y, TARGET_FID, AADT. Line 51 passes **-cc 0.85714**. Lines 52, 56, 63, 67 call `os.system` without checking return status. Lines 59 and 70 remove intermediate files. Lines 75–77 increment/print the processed counter in `finally`, including after caught exceptions. The code produces per-viewpoint rasters; it does not include the later cumulative-sum/cartographic analysis described in the paper. [Supplement](https://gh.copernicus.org/articles/77/165/2022/gh-77-165-2022-supplement.zip)

## Current software-prior check

[Current GDAL viewshed documentation](https://gdal.org/en/stable/programs/gdal_viewshed.html) identifies 0.85714 as the usual visible-light coefficient, documents meaningful projected-CRS requirements, warns that input nodata is not specially processed, and documents zero/nonzero exit status. Its elevation correction is height minus curvature coefficient times distance squared divided by sphere diameter. This corroborates the meaning of the code parameter; it does not prove which value was used for the published run. Current documentation must not silently substitute for the unspecified historical executable build.

[GDAL raster-calculator documentation](https://gdal.org/en/stable/programs/gdal_calc.html) warns that matching dimensions do not automatically check projection and that intermediate arithmetic may retain input datatype. Therefore range, CRS, alignment and nodata need explicit verification rather than reliance on file existence or lossless compression alone. These are established software contracts, not newly discovered mathematical principles.

No empirical effect of the two curvature settings has been calculated. No uncontrolled error bound is invented.

## Precise source-level result

**Proposition 1 (attempt count is not success count).** The supplied script admits a row execution whose final processed counter increases even though no valid viewshed output exists.

**Proof from control flow.** Consider a row with the required CSV fields, for which the viewshed subprocess returns a failure status and creates no output, and the translation subprocess likewise creates none. These return values are ignored. Removing the absent uncompressed file then raises a Python exception, which the bare `except` catches. Execution enters `finally`, increments `itemsProcessed`, and prints the count. Thus the final count does not entail successful output creation. QED.

This is a permitted failure trace of the actual code, not an assertion about the author's executed run. The script also prints an error message in this trace; the finding is not that every failure is silent. It is that a final count alone does not certify completeness.

## Exact aggregation and missing-row bound

This is an established finite-sum result applied to the documented output schema. It becomes a study certificate only once actual input/output identities and values are supplied.

Let V be the declared finite viewpoint registry with nonnegative weights w_i, and let b_i(c) be the correct binary visibility at cell c under one fixed admitted algorithm/input/version branch. Let K be the subset whose outputs have been validated, M=V\K, and

    L(c) = sum_(i in K) w_i b_i(c),
    U(c) = L(c) + sum_(i in M) w_i.

**Proposition 2.** The full weighted sum W(c)=sum_(i in V) w_i b_i(c) satisfies L(c) <= W(c) <= U(c).

**Proof.** Each unknown contribution is between zero and w_i. Sum these inequalities and add the validated partial sum. QED.

For unweighted counts take all weights one. The bounds are sharp over unrestricted binary completions, but not necessarily over the physically feasible family of jointly coupled terrain viewsheds. Therefore they are sound conservative bounds, not an exact geometric image characterization.

For a fixed threshold tau and target W(c)>=tau, L(c)>=tau certifies yes and U(c)<tau certifies no; otherwise abstain. For W(c)>tau change the inequalities appropriately. This cannot be substituted directly for the paper's top-5%-of-nonzero-cell rule, because that threshold depends on the whole raster. Any extension to ranks, neighborhood smoothing, polygons or human-selected labels requires preserving those exact downstream operations and tie conventions.

**Proposition 3 (aggregation preservation).** Any partition of the validated viewpoint set into disjoint blocks gives the same exact weighted sum when each block is summed exactly and the block sums are added.

**Proof.** Every index occurs in exactly one block; finite-sum associativity and distributivity give equality. QED.

Machine implementation needs no overflow, exact weight representation where claimed, and identical cell alignment/masks. Float arithmetic changes associativity; DEFLATE compression preserves represented raster values but does not prove the preceding numerical operations exact.

## Existing supplier match

[The pinned observational-equivalence module](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/8e665d2a9f6168e6448b2ca49fccbec87d57d3ad/SocialScience/Identifiability.lean) concerns equality under allowed observations and postprocessing. It motivates checking that a proposed export/parallel aggregate preserves the actual downstream statistic; it does not prove arbitrary raster compression sufficient.

[G6 Sections 4.5–4.6](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md) provide the finite-target homogeneous-compatible-set pattern. Here the compatible set is a deterministic completion envelope; no multinomial confidence level, Markov property or perception model follows. The elementary results above stand without importing the biological effective-net theorem.

## Prospective verification contract

### Admitted immediately: source-accounting verification

Inputs already accessible: the full hashed Python source and public GDAL documentation. The endpoint is verification of the actual script's success/failure accounting and a preservation wrapper specification. A static analyzer can inspect the original program as text/AST, and an independently written accounting wrapper can be checked using declared success/failure fixtures. The original script need not be imported or executed. Such tests validate the wrapper contract; the source-control-flow proof above, rather than a fixture, supports the claim about the original code.

A safe proposed wrapper should validate row fields and unique identifiers, record subprocess exit statuses, validate each raster's checksum/grid/CRS/nodata/value range, and produce separate attempted/validated/failed lists. Existing outputs must not be mistaken for fresh successful outputs. Preserve original script and input files. A source-contract implementation and its tests are prospective; none was executed for this note.

### Not yet admitted: statewide empirical certification

Needed inputs: original processed CSV, clipped/projected DEM, exact GDAL/tool version and parameters, and per-viewpoint output inventory or authorization to regenerate it. For a downstream map certificate also obtain the actual cumulative-sum and cartographic-operation scripts/settings. Public portals named in the paper identify raw-source families; they are not an immutable copy of its processed inputs.

Once available, establish the registry K/M from verified outputs, calculate exact/verified aggregation or missing-row envelopes, and report which **declared** thresholds remain invariant. Treat the curvature values as separate source branches until resolved; do not select one simply because current GDAL recommends it. Terrain/perception validity remains a separate issue.

## Admission verdict

The **accessible exact-code accounting/preservation endpoint** is admitted independently of statewide reproduction. The real source supports a concrete failure trace and a testable integrity contract. It does not yet support a claimed statewide spatial certificate or physical uncertainty validation. No new mathematical open problem or theorem priority is asserted.

[Research Commons](https://github.com/Sodelin/Research-Commons) · [Original study](https://doi.org/10.5194/gh-77-165-2022) · [Ge completed source/theory note](https://github.com/Sodelin/Research-Commons/blob/6a7d50f699245c87727961f59808c1ec0c9adfe5/research/2026-10-16-ge-diffraction-certification/CONDITIONAL-CERTIFICATE-01.md)
