# One superconductivity-specific inference connection

Date: 15 October 2026. Author: dot (OpenAI).
Status: bounded literature and interface audit; no new theorem, experiment, computation, publication, or claimed transfer. Biological G3/G4 remains the primary programme.

## Finding

There is a concrete current author-posed open question: whether topology inference learned from a minimal simulated semiconductor–superconductor nanowire model transfers to actual experimental spectroscopy. G6 offers a precise conditional certification interface. Its hardest hypothesis, observation-fibre separation in a physically defensible model class, is unproved here. G7 does not apply directly. This is an inference/validation challenge, not a named mathematical conjecture already solved by our results.

## Original question, model and present status

Taylor, Pan and Das Sarma, *Machine learning Majorana topology using unsupervised and supervised learning*, PRB 114, 165418, published 21 September 2026; [latest arXiv v2, 6 October 2026](https://arxiv.org/html/2512.13825v2), Discussion: “One question remains open”. They ask whether their combined learning procedure works on experimental nanowire data as on simulations. Model/data and Table 1 use a single-band BdG wire with Rashba coupling, Zeeman field, induced pairing and Gaussian disorder; temperature and dissipation are zero. Its operator is H=[-∂x²/(2m*)−iα∂xσy−μ+V(x)]τz+Vzσx+Δτx. Experimental-side inputs are lowest-state splitting E_s(Vz) and wire length L; the supervised output includes reflection-determinant topological visibility TV(Vz). Their strongest clustering also uses TV, which is not directly observed. Simulation success and noise augmentation do not establish experimental transfer; they explicitly identify training-model/device mismatch. Finite-wire TV is continuous, so its sign is an indicator requiring a declared convention. [Version history](https://arxiv.org/abs/2512.13825); [published record](https://journals.aps.org/prb/abstract/10.1103/ywsw-29xc).

## Latest nearby progress checked

Jones et al., [MEDA v2, 16 August 2026](https://arxiv.org/html/2607.26208v2), accepted to IEEE QCE 2026, already predict periodic-disorder-invariant (PDI) maps from sparse four-channel conductance slices. Sections III and V evaluate simulated nanowires; the reported tenfold input reduction is prior progress. Section V-E and VII retain fragmentation/smoothing limitations and suggest eventual adaptive acquisition. Its PDI is defined by periodic extension of the microscopic disorder, not identical to TV or a direct proof of protected finite-device anyons. MEDA therefore prevents claiming sparse conductance learning or attention-based experiment prioritization as our invention. It does not supply the uniform certified label-fibre separation proposed below. [Current version record](https://arxiv.org/abs/2607.26208).

Pan and Das Sarma's April 2026 paper independently emphasizes that finite disordered-wire topology depends on the chosen physical context, and investigates exponential splitting protection: [PRB 113, 165420](https://journals.aps.org/prb/abstract/10.1103/2v41-yvs1). This makes a target-definition gate essential.

Searches through 15 October 2026 checked the exact main title/identifier, 2026 spectroscopy/inference work and MEDA follow-ups. No later resolution of the October 6 explicit experimental-transfer question was located. This is a bounded negative search, not an exhaustive proof that none exists. Main paper's relevant model, learning, Discussion and appendices-facing limitations were read; MEDA model, inference, evaluation and limitations were read. The April paper was inspected at abstract level only. No disputed experimental finding is adjudicated here.

## Proposed exact mathematical interface (our operationalization)

Freeze one finite tight-binding discretization and known length. Let θ contain a single device's disorder vector, material parameters and explicitly admitted lead/calibration nuisances. Every field setting must use this same θ. An ensemble average over different disorder realizations is not substituted for repeated measurements of this device.

Fix a finite field menu U and a test field u*. Initially choose the paper's model-specific indicator, not an assertion of protected MZMs: Θ−={θ:TVθ(u*)≤−τ}, Θ+={θ:TVθ(u*)≥τ}, for declared τ>0. Points between these sets are outside the two-label promise and require abstention. A PDI or exponential-protection target would be a separate target contract, not a synonym.

For each u, define an experimentally justified response law Qθ,u for the measured splitting, including extraction uncertainty, instrument resolution and nuisance parameters. If repeated samples can legitimately be treated as conditionally independent and binned into fixed finite outcomes, Φ_U(θ)=(Qθ,u)_u is a finite probability profile. Binning may destroy separation and must be included in the analysis. Otherwise G6's multinomial engine requires a replacement confidence theorem for the actual noise process.

Let I− and I+ be the corresponding sets of probability profiles, retaining all nuisance parameters. G6's relevant abstraction is: construct effective outer/inner closure clouds; intersect simultaneous confidence regions with them; emit a label only when all surviving targets agree. At a point whose robust fibre is homogeneous, an appropriate finite honest stopping conclusion is then available. With persistent corruption, one needs the appropriate positive separation after enlarging both image sets by the allowed corruption radius. Passing a neural-network confidence threshold is not this condition.

G6 source: [effective-certification PROOF.md, immutable 1f2e49a9](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md). Its statistical fibre logic is reusable only after these receiver obligations; its biological chain approximation and physical-source-size bound do not automatically transfer. The inspected G6 account is accepted hand mathematics, not a fully compiled application endpoint.

G7's inspected contract requires a complete finite original-ID census and exact affine D responses, with rank deletion and RCF policy/Pareto arguments. Here the hidden disorder is continuous, scattering/spectral responses are nonlinear and observations noisy. Consequently no G7 rank or optimal-budget claim transfers. A rigorous noisy finite-action design extension could select the next field to reduce remaining opposite-label fibres, but constructing such an extension is further work. Adaptive learning/experimental design itself is established prior.

## Missing premises and failure modes

1. **Correct target.** A sign of finite-wire TV, a PDI label and an operational protection certificate are different objects. The last needs additional spectral/localization/control guarantees.
2. **Device class coverage.** A finite simulated training set is not a complete catalogue. Gaussian disorder has unbounded support; bounding it for compact effective clouds changes the class unless accompanied by a justified tail-risk budget. Multiband physics, lead coupling, temperature and dissipation must be admitted or explicitly excluded.
3. **Effective images.** Finite matrix eigenvalues offer computable approximation routes, but scattering calculations need declared lead/self-energy conventions and controlled singularities. No complete interval cloud construction was supplied or executed here. Imposing positive broadening cannot silently replace the paper's zero-dissipation model.
4. **Noise and persistence.** Repeated scans can have drift, hysteresis and correlated spectral-fitting errors. These do not automatically form multinomial independent replicates. Unknown systematic error cannot be reduced merely by taking more scans.
5. **Separation.** Similar signatures, high test accuracy and a good cluster plot do not prove opposite-label image closures are disjoint. Exact identifiability also need not give a useful positive robustness margin.

## Smallest decisive next mathematical gate

For one explicitly frozen device class, fixed length, finite field menu, target margin τ and calibrated observation law, determine whether the opposite-label profile closures intersect. Stronger and more practically useful: certify a nonzero separation exceeding the stated instrument/model-error budget on a nonempty declared operating region.

A decisive negative result would be an admitted pair, or convergent sequences, with opposite margin-separated labels and the same (or arbitrarily close) complete selected observation-law profile, using the same instrument convention. Mere matching of one zero-bias peak, a change of length, or zero-noise numerical near-equality would not discharge this gate. A decisive positive result needs a uniform certified bound over all admitted disorder/nuisance values, not a finite training sample.

Generic identical-law impossibility and confidence-set inversion are established statistics, not proposed novelty. The potentially useful new work would be the nanowire-specific separation or obstruction with physical assumptions audited. Even that would address only a mathematical part of the authors' experimental-transfer question; validating the device model and measured response remains experimental work.

## Recommendation

Retain this as one evidence-backed candidate, with G6 as a conditional framework and G7 as a possible extension obligation. Do not launch a new model or claim successful physics transfer. The next authorization/design decision is whether a specific finite-wire response class and label can be frozen tightly enough to make the separation gate meaningful. No G3/G4 closure follows; a successful receiver-specific confidence-fibre adapter could be reusable infrastructure for biological certification, while exact unknown-size recognition remains separate.


## Navigation
[All individual connection dossiers](https://docs.google.com/document/d/1ZkjK2vhPFKr0C83eyvizK7xdZgdaWKXkNx4Nt_WXuBo/edit)
[GitHub reading copy](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-15-connection-dossiers/nanowire-topology-inference.md)

[Readable Google document](https://docs.google.com/document/d/1lt_IX0j0CrWa8sYBheG6Bf9NS9Nm75kUZz-HOKTNf2Q/edit)
