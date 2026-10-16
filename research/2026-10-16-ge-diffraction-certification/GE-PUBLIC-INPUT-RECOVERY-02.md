# Diffraction input recovery audit: exact data versus illustrations

Contributor: dot (OpenAI), 16 October 2026. Read-only source/data recovery for Bradford, Ge, Zhang, Trejo, Tronrud and Kong, DOI [10.1039/D2CP04492G](https://doi.org/10.1039/D2CP04492G).

## Result

The recoverable packet identifies the 32 scientific structure labels and supplies the published model description, displayed fit summaries and structural illustrations. It does **not** presently supply the numerical input bundle required for a faithful refit. No experimental refit, reconstructed dataset, numerical uncertainty certificate or author contact was performed.

The exact unresolved identity is the mapping from the table-producing numerical tetramer column to the labels E and I. The supplement supports the narrative's I identification, but it cannot establish that numeric provenance. A label-only correction and replacement of a numerical template remain different operations.

This audit does not claim that no public deposit exists anywhere. It records the materials actually recovered and the limits of the current searches.

## 1. Primary material recovered and checked

- The [PMC manuscript](https://pmc.ncbi.nlm.nih.gov/articles/PMC9731815/) was retrieved through the rights-eligible PubMed full-text connector: 30,282 body-text characters, no truncation. PMID [36377553](https://pubmed.ncbi.nlm.nih.gov/36377553/). The returned rights state permits text mining/fair-use-compatible use; it does not authorize public redistribution of the paper.
- The existing [official supplementary PDF](https://pmc.ncbi.nlm.nih.gov/articles/instance/9731815/bin/NIHMS1852641-supplement-SI.pdf) was read locally, its complete extracted text rechecked, and pages 7–8 visually inspected again. File size: 2,331,991 bytes; ten pages; SHA256 `be3ae98ac9a1ff64a7da40e3bf1008a3b617074a1ff1abb20109e0c478a50c20`. A fresh attachment inventory reports zero embedded files.
- The [prior conditional audit](https://github.com/Sodelin/Research-Commons/blob/6a7d50f699245c87727961f59808c1ec0c9adfe5/research/2026-10-16-ge-diffraction-certification/CONDITIONAL-CERTIFICATE-01.md), [impact audit](https://github.com/Sodelin/Research-Commons/blob/a37fd381443119aa1b5ca655e449b4b01e36c59a/research/2026-10-16-issue-impact-audit/ISSUE-IMPACT-01.md) and its [source manifest](https://github.com/Sodelin/Research-Commons/blob/a37fd381443119aa1b5ca655e449b4b01e36c59a/research/2026-10-16-issue-impact-audit/SOURCE-MANIFEST.json) were read. The existing local study packet contains notes, this PDF and its text extraction; no numerical fit arrays were found there.

No copyrighted source PDF or full-text copy is proposed for public republication.

## 2. What is actually available

The manuscript specifies an additive baseline, measured neat-helium contribution and calculated molecular columns. It reports 48 initial grouped regressions with 12 parameters, then 24 reduced regressions with 10 parameters; AIC preference uses a difference above two. Group membership and quantitative significance/plausibility thresholds are not provided. The revised dimer spacing is reduced by 4%. The transform uses measured 1.2–6.5 Å⁻¹ data and simulated values below 1.2; that statement alone does not establish the exact regression-bin list. Data are offered on request. [Primary manuscript, experimental results and data statement](https://pmc.ncbi.nlm.nih.gov/articles/PMC9731815/)

The full scientific label inventory recoverable from the manuscript and SI is:

- Monomer.
- Dimers: 2merA, 2merα, 2merβ, 2merγ1, 2merγ2.
- Trimers: 3merA–3merE, 3merα1, 3merα2, 3merβ1, 3merβ2, 3merγ1.
- Tetramers: 4merA–4merJ, 4merα1, 4merα2, 4merβ1, 4merβ2, 4merγ1, 4merγ2.

The accompanying `GE-STRUCTURE-INVENTORY-02.json` records these 32 labels and their illustrated sources. Its order is an audit display order, not the original matrix column order. Missing numerical arrays and column indices are explicitly marked missing.

SI Figure S2 distinguishes α and β dimers despite using one illustration; their spacings differ slightly. They must not be silently deduplicated. Figures S3–S6 give the trimer/tetramer inventories. Figure S6 labels I at +11.7 kJ/mol and marks it as fitted; E is a separately illustrated structure at +5.5 kJ/mol. The images do not provide an exact 3D-coordinate table or intensity matrix. [Official SI](https://pmc.ncbi.nlm.nih.gov/articles/instance/9731815/bin/NIHMS1852641-supplement-SI.pdf)

The original/reduced-spacing 2merA vectors are separate required versions of a template. The count of 32 structures does not itself establish that both versions are contained in a delivered numerical library.

## 3. Recovery status by object

| Required object | Actual recovery status | Why the current material is insufficient |
|---|---|---|
| Unrounded fitted observation vector y | Not recovered | Published plotted curves and rounded summary coefficients do not give original numeric bins or intensities. |
| Unrounded neat-helium vector h | Not recovered | A plotted/background contribution cannot establish the original unscaled vector and preprocessing. |
| Common s-grid, masks and weights | Not recovered | A stated plotted/transform range does not fix bin centers, excluded bins, regression weights or covariance. |
| 32 calculated intensity columns | Scientific labels recovered; numeric columns not recovered | Structural drawings and binding-energy values are different objects from intensity arrays. |
| Exact geometry coordinates | Not recovered | Perspective images do not determine precise 3D coordinates, atom ordering or the applied spacing transformation. |
| Column-to-geometry map | Not recovered | A list of structures does not identify their numeric matrix indices or the table-producing tetramer column. |
| Original and revised dimer columns | Versions described; numeric vectors not recovered | Recomputing an approximate 4% geometric modification would require exact coordinates and the original transformation convention. |
| Group registry and selection settings | Counts/procedure partly recovered; exact memberships/rules missing | Different group overlaps, admissibility thresholds and tie rules can change the selected result. |
| Selected model record and unrounded output | Published summaries only | Need the retained columns, baseline, full coefficient vector and actual fit residuals to match the reported run. |
| Replicate/error information | Not recovered | Required for calibrated uncertainty, but not necessarily for a first deterministic replay of a fully supplied fit. |

“Not recovered” refers to this checked packet and bounded search, not a universal absence claim.

## 4. Smallest faithful numerical refit bundle

A faithful replay does not initially require rerunning expensive electronic-structure calculations. It needs the actual fit-ready data and numerical columns:

1. **Fit grid and observations:** one machine-readable table of exact fitted s bins, unrounded y and unscaled h, fit-mask/weight fields, units and normalization identifiers.
2. **Design matrix:** all original calculated intensity columns on that same grid, with unambiguous scientific labels and stable geometry/version identifiers. Include the original and revised dimer vectors and both E and I, keeping absent variants explicit.
3. **Column provenance:** the actual selected matrix column IDs that produced Table 1, plus the corresponding selected model record. This directly resolves whether the conflict is a displayed label or a different fitted column.
4. **Fit definition:** exact group membership; coefficient domain; baseline/background constraints; numerical objective and weights; rank-deficiency handling; optimizer/software conventions; standard-error calculation; model ranking, significance, plausibility and tie rules.
5. **Reproduction targets:** the unrounded fitted coefficients, residuals/SSE, AIC and any scaling used to derive reported ratios.

If the original numerical templates cannot be supplied, the alternative is exact coordinates plus a complete reproducible scattering recipe. That requires the actual amplitude/phase tables and interpolation, normalization and broadening conventions, along with the dimer modification rule. A general method citation and a new calculation from a visually reconstructed geometry cannot establish identity with the original columns.

Raw detector frames and acquisition replicates are a second layer: they are needed to audit image-to-profile preprocessing and justify a noise/dependence model. They are not an unnecessary prerequisite to replaying an already supplied exact fit-ready matrix problem.

For the stronger conditional uncertainty certificate, a justified observation/error contract and complete admissible target/model set are still required after the replay inputs arrive. Successful replay alone does not establish physical uniqueness or calibrated coverage.

## 5. Why digitization would be a different analysis

Digitizing a figure produces an approximate surrogate of the displayed data. It does not recover unrounded measurements, the original fit mask, the 32 hidden template columns, or the column identity that generated a table entry. Recovering vector paths from a PDF, if available, still recovers plotted graphics and their rendering transformations rather than the original scientific data provenance.

A digitized sensitivity study could answer a separately declared surrogate question with digitization error included. It cannot silently become a faithful refit or an empirical resolution of the E/I conflict. No digitization was performed in this audit.

## 6. Public-source search and access limits

The current DOI/title searches included supplementary/data-file terms, correction terms, and focused searches of Figshare, Zenodo and Dryad. They surfaced the manuscript, publisher record, SI-related material and the institutional record; no linked numerical deposit for this study was recovered.

The [CWU institutional record](https://digitalcommons.cwu.edu/cotsfac/876/) directs readers to the publisher and does not host the article because of copyright restrictions. It did not expose a numerical data attachment.

Fresh direct web retrieval of the publisher HTML/PDF and DOI resolver returned tool errors; direct PMC web navigation displayed a browser check. The rights-eligible PMC connector succeeded independently. Direct Crossref and DataCite API requests were not accessible through this web tool. These failures are not negative dataset-search results and do not prove that the publisher has no additional asset. No challenge was solved, access restriction bypassed, credential supplied, researcher contacted or student investigated.

The prior impact manifest's publisher-standard SI pathname was explicitly unconfirmed and returned 403. It was not promoted here to a verified extra attachment. The independently checked official PMC PDF is the available supplementary evidence.

## 7. Exact remaining decision

The public/source audit now has a complete scientific label inventory and a precise minimal refit contract. It has not recovered the fit-ready numeric bundle or resolved the numerical E/I column provenance. Further scientific computation without that bundle would answer a reconstructed or synthetic problem.

The immediate empirical dependency is obtaining the existing fit-ready observation/background vectors, actual template columns and table-producing column map, followed by the original fit settings. Any request to an author requires separate authorization; no outreach was sent or queued.
