# Directed novelty assessment: fixed-lead nanowire nonseparation

**Prepared:** October 17, 2026, 00:21 UTC. **Author:** dot, working with Nolan. **Status:** source comparison for review; historical novelty is not established. No submission or new publication was made in this pass.

## Decision

The evidence supports a narrower contribution than a new physical limitation. The weak-contact mechanism is established physics, and its abstract positive-margin, arbitrarily-small-energy-separation consequence follows immediately from an existing two-mode formula. Keeping external leads fixed is also insufficient as a novelty distinction: prior microscopic simulations already use internal tunnel barriers.

The defensible contribution is the **audited realization in one explicitly declared finite Rashba-chain family**, followed by a reproducible finite-parameter certificate. Its mathematical content is the certified transverse crossing and endpoint weights, the microscopic Schur-complement limit with fixed contacts, and the exact finite example. I did not locate a prior theorem with this complete combination of assumptions and quantifiers. That is a bounded search finding, not proof of priority or of sufficient novelty for a journal or prize.

Suggested description:

> A computer-assisted, model-specific realization of known resonance-width physics: fixed microscopic contacts and one scalar-potential profile per field sweep permit opposite reflection-visibility margins while the complete lowest-energy curves become arbitrarily close. An independently replayed interval certificate supplies one explicit finite example.

“Independently replayed” refers to the recorded separate checker replay and source/hand review. It does not mean a separate implementation, external specialist endorsement, or Lean verification.

## Exact result under comparison

The [accepted asymptotic packet](https://github.com/Sodelin/Research-Commons/blob/caf7d4531c3027d19d0e899bee7129f672d1f342/research/2026-10-16-nanowire-fixed-lead-nonseparation/README.md) fixes 60 sites, length 0.6 μm, pairing, spin-orbit hopping, normal lead Hamiltonians and contact hoppings. For each fixed hopping in its certified interval and every positive observation-error radius, it constructs two finite scalar-potential vectors, each held fixed for the entire field interval. At the same field B = 2 meV their reflection determinants lie on opposite sides of ±0.1; their closed-wire lowest-energy curves have overlapping error balls in the uniform norm. The pair may depend on the error radius.

The [finite example](https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/README.md) fixes hopping to 25.08215 meV and end onsite coefficients to 1000 meV. It certifies −0.203 < TV− < −0.202 and 0.996 < TV+ < 0.997. The uniform energy-curve distance is at most 0.09999 μeV; a common midpoint is within 0.049995 μeV of each curve. This finite pair does not itself prove the claim for every smaller error radius.

Both results require zero internal dissipation and the declared potential class. Unbounded potentials are essential to the asymptotic sequence. Experimental feasibility of the 1 eV example is unestablished. Neither result proves exact equality of noiseless curves, a typical-device error rate, protected Majorana modes, or an error in the Taylor paper. Original Taylor lead/disorder implementation admission remains unresolved; its modified energy-plus-length unsupervised variant excludes this short length.

## Primary-source comparisons

### 1. Closest mechanism and immediate corollary

[Araya Day, Manesco, Wimmer and Akhmerov, *Identifying biases of the Majorana scattering invariant*](https://arxiv.org/pdf/2504.01069), §3.1, Eqs. (6)–(7), Fig. 2(a), and Appendix: the visibility depends on splitting and contact-induced widths. Their microscopic check uses two Gaussian tunnel barriers. Publication metadata identifies [SciPost Physics Core 8, 047, July 4, 2025](https://scipost.org/SciPostPhysCore.8.3.047/pdf); the body inspected here was arXiv v1, not a freshly readable final publisher PDF.

**Immediate algebraic corollary, not claimed as new:** in their effective model set ΓL = ΓR = γ > 0. Choose splittings E− = γ/2 and E+ = 2γ. Then

\[
Q_-=-3/5,\qquad Q_+=3/5,\qquad |E_+-E_-|=3\gamma/2\to0.
\]

The two models have the same effective couplings within each pair. This establishes the abstract positive-margin scaling directly from their formula. It does **not** supply a fixed-hopping microscopic scalar-potential realization, or a shared physical field sweep. Those are separate obligations discharged in our declared construction. The prior already removes any claim that resonance-width dependence or internal-barrier weakening is new.

### 2. Earlier coupling-sensitive scattering definition

[Akhmerov, Dahlhaus, Hassler, Wimmer and Beenakker, *Quantized conductance at the Majorana phase transition in a disordered superconducting wire*](https://arxiv.org/pdf/1009.5542), PRL 106, 057001 (2011), Appendix A.2–A.3: their operational finite-wire distinction explicitly compares the coupling between Majorana components with coupling to the ends. The present lead-sensitivity interpretation therefore has an older conceptual predecessor than the 2025 paper. The inspected argument does not give our particular full-field, scalar-potential two-branch certificate.

### 3. Splitting and broadening were already linked to visibility

[Das Sarma, Nag and Sau, *How to infer non-Abelian statistics and topological visibility from tunneling conductance properties of realistic Majorana nanowires*](https://arxiv.org/pdf/1603.00041), PRB 94, 035143 (2016), §§II, III.B and IV: visibility is studied against splitting, lead broadening and intrinsic dissipation; Eqs. (9)–(10) show the tunable contact and dissipative model. This is strong prior against a broad “finite energy resolution cannot establish topology” novelty claim. Its single-lead/dissipative setup and braiding discussion are different from our zero-dissipation, two-lead reflection-label theorem. Its time–energy discussion does not turn our error-ball argument into a Heisenberg uncertainty theorem.

### 4. Fixed-length smooth-barrier indistinguishability is established

[Vuik, Nijholt, Akhmerov and Wimmer, *Reproducing topological properties with quasi-Majorana states*](https://arxiv.org/pdf/1806.02801), arXiv v3 / SciPost Physics 7, 061 (2019), §§II–III, Eqs. (1)–(4), (10)–(16): a fixed-length Rashba model with smooth barriers has strongly unequal effective couplings and can mimic several Majorana signatures. They compute lowest-energy field dependence and suggest a different measurement regime. This is substantial prior on measurement ambiguity, including microscopic barriers. The displayed target is not our pair of opposite two-terminal reflection margins with a uniform curve-distance certificate; no exact import of that complete statement was found in the inspected sections.

### 5. An alternative topology target must remain separate

[Avila, Peñaranda, Prada, San-Jose and Aguado, *Non-Hermitian topology as a unifying framework for the Andreev versus Majorana states controversy*](https://www.nature.com/articles/s42005-019-0231-8), Communications Physics 2, 133 (October 25, 2019), Results Eqs. (1)–(5) and Methods: the classification uses exceptional-point bifurcation of an open-system complex spectrum and depends on wavefunction coupling asymmetry. This is relevant prior for why closed energies alone omit contact information. It is not the same label as our finite reflection determinant. Treating all uses of “topology” as interchangeable would manufacture a false comparison.

### 6. Inverse-scattering theory does not automatically provide this counterexample

[Gerald Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf), AMS (2000), §10.2 Eq. (10.54), §10.4 Theorem 10.12, and Chapter 11: reconstruction uses reflection data and discrete eigenvalues with norming constants; spectral deformations can alter Jacobi coefficients and scattering data. This supplies classical context for the difference between eigenvalues and boundary information. It does not, without an additional construction, preserve our fixed off-diagonal spin/BdG blocks, the prescribed Zeeman term, finite length, and one scalar potential across the field sweep. Missing norming constants alone is not a proof of noninjectivity for that constrained family.

### 7. A concrete isospectral lattice construction still has a contract mismatch

[Balasubramanian, Patoary and Galitski, *Solitons in lattice field theories via tight-binding supersymmetry*](https://arxiv.org/pdf/2103.02613), arXiv v1 (March 3, 2021), §4.2 Eqs. (4.2)–(4.9): the construction changes superpotential and superhopping, producing partner tight-binding operators and controlled reflection/transmission magnitudes. It is not a scalar-potential-only deformation of the fixed Rashba family. Its auxiliary scattering amplitudes also are not our particle-hole reflection determinant. The title’s “isospectral” therefore cannot be used as either a direct novelty refutation or a ready-made stronger exact-collision theorem here.

### 8. Relation to the motivating learning paper

[Taylor, Pan and Das Sarma, *Machine learning Majorana topology using unsupervised and supervised learning*, v2](https://arxiv.org/html/2512.13825v2), Eq. (2), Table 1, supervised-learning section and Appendix II: the supervised inputs are the lowest-energy curve and length; the paper evaluates a simulated distribution. Its publicly inspected text does not bind our exact contact and disorder-generation contract. A worst-case nonuniform-separation theorem can coexist with high test-distribution accuracy. The short-wire exclusion belongs specifically to the modified unsupervised variant. No claimed contradiction with the empirical results follows from our current packet.

## What is genuinely added, and what is standard

| Component | Current assessment |
|---|---|
| Coupling-sensitive finite reflection label | Established prior physics |
| Arbitrarily small energy difference with opposite fixed label margins in a two-mode model | Immediate corollary above |
| Weak effective contacts produced by internal barriers | Already present in microscopic prior work |
| Simultaneous fixed-contact, fixed-length, scalar-potential-only realization | Verified in our declared family; exact earlier match not located |
| One unchanged potential vector over the whole field sweep | Preserved by our construction; essential contract, not evidence of priority |
| Uniform whole-field energy estimate | Standard perturbation inequality applied to the constructed pair |
| Certified crossing, endpoint polarization and full finite reflection evaluation | Concrete auditable proof work; priority and publication significance unresolved |
| Specific rational 60-site pair and error budget | Reproducible benchmark; different numerical constants alone are not research novelty |
| Original Taylor implementation or realistic typical devices | Not established |

The proof is stronger than a floating-point plot or an unbound effective-model analogy because its inequalities and realization are checkable. That improves reliability. It does not by itself establish a new physical phenomenon, a new general mathematical method, or the first resolution of an externally posed open problem.

## Most useful improvements, ranked by scientific consequence

1. **Determine applicability to a meaningful physical class.** Authenticate the motivating implementation when an authorized source becomes available, or explicitly define a separate experimentally defensible class. No further inaccessible-source retries or contact were made here.
2. **Identify a measurable way to resolve the certified pair, with error margins.** An additional calibrated measurement that separates the same devices would turn the example into a concrete measurement-design benchmark. It would remain pair-specific unless a uniform theorem were proved. Root is evaluating this separately; no result is assumed in this assessment.
3. **Address bounded potentials, effective-contact floors and positive broadening as separate stated contracts.** These may exclude the present singular sequence. A theorem or counterexample there could change practical relevance substantially; simply relabeling the current unbounded/zero-dissipation result would not.
4. **Reduce the verification trust base.** Formalize the finite rational example with matrix-model fidelity, interval containment, inverse guards, scattering identities and spectral/error-ball consequences. Lean would improve assurance, not historical novelty. The existing Python checker is not a Lean proof.
5. **Seek specialist priority assessment after this exact comparison is reviewed.** A comprehensive historical novelty claim requires more than the search below. No author, mentor or external reviewer was contacted.

## Search coverage and stopping boundary

This extends the October 16 directed check rather than repeating its original-model access attempts. On October 17, 00:15–00:21 UTC, the pass searched combinations of Majorana/scattering/visibility with “isospectral,” “inverse spectral,” “identical spectra,” “indistinguishable,” “arbitrarily,” “tunnel barriers,” and “energy splitting”; it followed the closest paper’s 2011, 2016 and 2019 citations and checked an explicit lattice-isospectral construction and an author-hosted inverse-scattering reference. Eight primary works received targeted full-text inspection as described above, not exhaustive line-by-line audits of all papers and supplements.

The publisher-indexed metadata for the 2025 SciPost paper was readable; the direct final PDF returned a challenge page. Its arXiv body was available and was used transparently. The linked [Zenodo code record](https://zenodo.org/records/15058839) was discovered from the primary paper; indexed metadata lists a 14.8 MB archive, but direct retrieval through the available reader failed. Its contents were not inspected. A newer [transport-robustness paper](https://www.nature.com/articles/s41586-026-10567-8) was identified but its full-page read failed; no theorem from it is imported. Unread sources remain possible priority leads, not evidence of absence or overlap. No challenge or access restriction was bypassed.

This pass does not exhaust citation databases, theses, all versions, unpublished work, or code archives. Its conclusion is **known mechanism, verified specific realization, unresolved historical novelty**, with the explicit narrow contribution above. Public updating is held for root review.
