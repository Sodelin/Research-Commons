# CWU connection: tau–MAP6 model admission and identifiable dynamics

## Executive summary

The published model provides a concrete system to audit. Before claiming a useful reduction or parameter inference theorem, we must preserve its actual update rules and clarify a numerical inconsistency. More computation alone cannot settle model identifiability or validate the biology.

## Primary source and exact scientific need

Kirimtay et al., including E. M. Craig, **Tau and MAP6 establish labile and stable domains on microtubules**, *iScience* 28(3), 111785 (2025); online 29 January, issue 21 March. DOI [10.1016/j.isci.2025.111785](https://doi.org/10.1016/j.isci.2025.111785); [full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC11879653/); [code archive](https://doi.org/10.5281/zenodo.14596990). Version: published article; model methods, parameter rationale and discussion inspected, code unexecuted.

The study supports complementary tau-rich labile and MAP6-rich stable domains. The Discussion proposes investigating responses of each MAP to dysfunction involving the other. The explicit Limitations section identifies the reductionist fibroblast setting and missing neuronal factors. STAR Methods acknowledges missing direct MAP6 binding/unbinding measurements and uses motivated parameter choices. These are physical validation/measurement needs, not a published quotient conjecture.

## Later work and established boundary

Sun et al., **Patient-derived forebrain cortical organoids reveal biphasic tau–MAP6–microtubule axis dysfunction in tauopathy**, *Alzheimer's & Dementia* 22(7), e71565 (July 2026), DOI [10.1002/alz.71565](https://pubmed.ncbi.nlm.nih.gov/42411568/). Primary metadata and publisher abstract-level material checked. This progresses beyond the earlier fibroblast setting; its full methods and any model-identifiability implications have not been audited. Do not call neuronal relevance wholly untested.

## Proposed interface and decisive proposition

The simulator is fixed-step lattice Monte Carlo. Candidate state includes occupancy, length and growth/shrink/stable mode, plus any update-order state required by the code. Freeze an initial-state domain, parameter range, intervention set and actual readout cadence. For a descriptor d, the G2-style gate is: whenever d(x)=d(y), the pushforward transition laws K_u(x,d⁻¹A) and K_u(y,d⁻¹A) agree for every admitted intervention u and measurable descriptor event A, with equal current readouts. This is a standard sufficient quotient criterion, not a newly discovered general theorem. A source-admitted violating pair refutes that descriptor's exact closure. Failure at one simulation step does not prove impossibility for every sampled-output representation.

G6-style parameter inference separately needs effective observation-law images and robust target-label separation. Neither property is established here. Resolve update competition, length rounding and parameter conventions first. Source prose equates 1/(4 ms) with 25 s⁻¹, whereas arithmetic gives 250 s⁻¹; figures use 25 s⁻¹. This is a clarification requirement, not a rejection of the study. Reported steady behavior is not a proved mixing bound.

## Gap classification and benefit

**Engineering/source admission:** exact program semantics and parameter discrepancy. **Mathematics:** conditional quotient and identifiability questions we propose. **Computation:** bounded simulation or certified forward-image approximation may help after admission; no resource bottleneck measured. **Experimental:** binding rates, perturbations and neuronal validation. Status: proposed study support; no new theorem or completed transfer. Reusable benefit to biology is precise observed-process semantics and avoiding unsupported reductions.

## Mathematical contract and verification boundary

The proposed connection is our operationalization, not a theorem claimed by the cited authors. G6 requires a declared source class, finite target labels, effective bounds on closures of forward observation images, and robust label separation for finite honest stopping. See the [G6 proof account](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md). That account is not a claim of a complete compiled Lean endpoint. G7's accepted exact affine-response finite-registry setting does not automatically cover noisy nonlinear experiments. G2 requires an actual transition-preservation criterion, not merely similar observables. The biological G3/G4 master recognition questions remain open.

No experimental replication, code execution, new proof, Lean build or lab-fit assessment was performed for this dossier. Mathematical verification, numerical capacity and physical validation are separate obligations. No contact with researchers has occurred. This is a public-literature connection dossier prepared on 15 October 2026; targeted reading is identified below, and an incomplete later-work search is never evidence of absence.


## Navigation
[All connection dossiers](https://docs.google.com/document/d/1ZkjK2vhPFKr0C83eyvizK7xdZgdaWKXkNx4Nt_WXuBo/edit)
[GitHub reading copy](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-15-connection-dossiers/tau-map6-model-admission.md)

[Readable Google document](https://docs.google.com/document/d/1YIJ6XOp_WZeVVqPGhjvXIkWRQTfimuXIfdKQG5o3O7A/edit)
