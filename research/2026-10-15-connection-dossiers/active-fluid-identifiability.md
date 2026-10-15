# CWU connection: active-fluid model identifiability and measurement design

## Executive summary

The authors already identify the need for new physical measurements and independent validation. A mathematical contribution could determine which parameters those measurements identify and where extra measurements are necessary. It would support, not replace, experimental validation.

## Primary source and author-stated need

E. M. Craig, F. Oprea, S. Alam, A. Grodsky and K. E. Miller, **A simple active fluid model unites cytokinesis, cell crawling, and axonal outgrowth**, *Frontiers in Cell and Developmental Biology* 12, 1491429, 17 October 2024. DOI [10.3389/fcell.2024.1491429](https://www.frontiersin.org/journals/cell-and-developmental-biology/articles/10.3389/fcell.2024.1491429/full). Version: published article, superseding the May 2024 preprint; not two independent studies. Discussion sections 4.5–4.6 inspected and refreshed 15 October 2026.

The established contribution is a steady active-fluid description comparing subcellular flow profiles across motility modes. Section 4.5 calls for measurements of physical parameters across modes and new validation to address overfitting and generalizability. A short exact statement is: “new experimental validation is needed to directly test our hypothesis”. The paper already discusses extending the treatment to time-dependent elasticity; that extension is not our invention.

## Later-work boundary

The 2025 axon-origin hypothesis [DOI 10.1091/mbc.E24-12-0585](https://pmc.ncbi.nlm.nih.gov/articles/PMC12415613/) reuses this mechanistic comparison but is not independent validation of all physical parameters. No comprehensive citation-chain audit through October 2026 was completed for the proposed parameter-identifiability question. Therefore current unresolved status is **not certified**; admission is justified by direct study support and the explicit 2024 validation need.

## Proposed interface and decisive proposition

Declare a parameter domain Θ for the actual PDE, boundary conditions and nuisance terms. Define Φ(θ) as the measured flow and traction profiles at their actual spatial resolution. First account for nondimensionalization and any parameter symmetries.

**Decisive proposed proposition:** characterize the fibres of Φ on Θ and establish whether the scientific target L is constant on each fibre. If two physically admitted parameter choices predict identical selected measurements but different targets, identify an additional measurement separating that pair; do not infer it separates all rivals. A robust G6 result would require quantitative label-image separation and computable PDE-error enclosures. G7 needs a nonlinear noisy-design generalization; exact affine-response rank deletion does not directly apply. This interface has not been proved for this PDE.

Missing: calibrated uncertainty, simultaneous rather than separately fitted measurements, effective bounded domains, existence/uniqueness of model solutions, discretization control and a precise target (parameter versus mechanism versus predictive response). Fit quality alone cannot certify uniqueness or the evolutionary interpretation.

## Gap classification and benefit

**Authors' gap:** experimental measurement and validation. **Our proposed mathematical gap:** identifiability and robust discriminating design for an admitted model. **Computation:** PDE solves and certified enclosure calculations, with no established capacity bottleneck. Status: proposed application, novelty unresolved; no solved open mathematical problem claimed. Biological benefit is the separation of structural ambiguity from finite-data error and shared-parameter discipline.

## Mathematical contract and verification boundary

The proposed connection is our operationalization, not a theorem claimed by the cited authors. G6 requires a declared source class, finite target labels, effective bounds on closures of forward observation images, and robust label separation for finite honest stopping. See the [G6 proof account](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md). That account is not a claim of a complete compiled Lean endpoint. G7's accepted exact affine-response finite-registry setting does not automatically cover noisy nonlinear experiments. G2 requires an actual transition-preservation criterion, not merely similar observables. The biological G3/G4 master recognition questions remain open.

No experimental replication, code execution, new proof, Lean build or lab-fit assessment was performed for this dossier. Mathematical verification, numerical capacity and physical validation are separate obligations. No contact with researchers has occurred. This is a public-literature connection dossier prepared on 15 October 2026; targeted reading is identified below, and an incomplete later-work search is never evidence of absence.


## Navigation
[All connection dossiers](https://docs.google.com/document/d/1ZkjK2vhPFKr0C83eyvizK7xdZgdaWKXkNx4Nt_WXuBo/edit)
[GitHub reading copy](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-15-connection-dossiers/active-fluid-identifiability.md)

[Readable Google document](https://docs.google.com/document/d/1gaUOLbpjimwLGYkmVKzKLPsFCOYQ90EqVpIdECd270U/edit)
