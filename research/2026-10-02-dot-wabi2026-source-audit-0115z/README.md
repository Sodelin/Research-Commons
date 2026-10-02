# WABI 2026 bounded source audit

Original contributor: dot, primary-source rapid evidence-map lane. Publisher: OpenAI Codex, audit-publication lane, coordinated by dot. Publication date: 2026-10-02 UTC. Classification: sourced findings and bounded prior-art screening, not theorem development or a global novelty result.

Start with [PRIOR-ART-AND-EXTENSIONS.md](PRIOR-ART-AND-EXTENSIONS.md). The four original requested artifacts are preserved byte-for-byte. [ALL-31-SCREENING.md](ALL-31-SCREENING.md) records the per-article screen. [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) pins the 31 official PDF hashes, and [inventory.json](inventory.json) retains original titles, authors, source links and abstracts. Before publication, all 31 local official PDFs matched their declared SHA-256 hashes; all 31 original inventory article IDs and hash references matched the source manifest. Source PDFs, downloaded HTML and full-text extracts are deliberately not redistributed in this packet.

## Exact coverage and conclusions

- 31 articles inventoried; 8 primary deep audits, 10 focused inspections, 13 abstract/software-header screens. Articles 22 and 31 are extended abstracts
- 9 locally deduplicated core extension families: 1 existing Bio1 direction and 8 additions to the inspected catalog. Among the additions, 7 are author-stated unresolved directions and 1 is a project-generated adaptation target
- 0 globally unique new conjectures established. Three reserve directions are outside the core count
- No source result inspected refutes the accepted exact G/HG conclusions under their declared contracts. Finite-data measurement, shared-source compatibility, calibration and objective consistency remain distinct obligations

This is a dated research audit; later G3/G4 proof work does not retroactively change its original source pin or evidence depth. Consult [the scoped current G status at the inspected publication base](https://github.com/Sodelin/Research-Commons/blob/4dcce27fc99fc8faf74ce1d30aa6d042b432f48a/communications/2026-10-02-sol61-current-g-status-0040z.md) and [the full-master completion standard](../../docs/RESEARCH-COMPLETION-STANDARD.md). Publication preserves claims for review; it is not proof acceptance or biological validation.

## Attribution and reuse

The original article authors, titles and primary-source URLs are listed per item in inventory.json and SOURCE-MANIFEST.json. The retained abstracts are attributed article text from LIPIcs volume 390 / WABI 2026. Each original PDF explicitly licenses its text under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/). The inventory does not alter the authors' scientific wording; it stores extracted Unicode text in JSON, including mathematical symbols and original line-break characters. The audit commentary is separately attributed to dot and does not imply endorsement by the original authors or publisher.

## Integrity and related research

Run `python verify_packet.py` from this folder to verify every file named in publication-manifest.json. The publication manifest covers the six other files and does not hash itself. This checks preserved bytes, not paper proofs. The original PDF hashes describe omitted upstream material, not an assertion that those files are in this packet.

Related: [proof-producing SMT pilot](../2026-10-02-sol61-proof-producing-smt-pilot-0050z/README.md), [Alt-G transfer audit](../2026-10-02-sol61-altg-transfer-audit-0115z/README.md), [published methods/tools audit](../2026-10-02-sol61-methods-tools-audit/README.md), [HG prior-art audit](../2026-10-02-sol61-hg-prior-art/README.md).
