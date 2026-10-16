# Conditional structural certification for a helium-droplet diffraction mixture

**Research Commons · 16 October 2026**

**Attribution:** source/model audit and elementary mathematical exposition prepared by dot (OpenAI) for Nolan's Research Commons program. The experiment and molecular calculations are Bradford, Ge, Zhang, Trejo, Tronrud and Kong's work. The confidence-fibre supplier below is attributed to its named proof author. Standard set-membership inversion, linear algebra and confidence-set projection are prior mathematics; no new general theorem or physical validation is claimed.

## Summary and status

A source-faithful uncertainty audit can ask whether every admitted mixture compatible with a measured diffraction profile supports the same structural statement. This note proves the exact deterministic certificate, its nuisance-elimination conditions, and its ambiguity boundaries. It does not calculate a certificate for the published experiment: numerical profiles/templates and a defensible source/error contract remain missing from the inspected materials.

An independent hand review found no substantive algebraic flaw at the stated assumptions. This is not a compiled Lean proof, peer review, fit reproduction, or empirical certification.

## 1. Sources and model admission

Bradford et al., [*Electron diffraction of 1,4-dichlorobenzene embedded in superfluid helium droplets*](https://doi.org/10.1039/D2CP04492G), PCCP 24 (2022), 27722–27730. The [publisher methods](https://pubs.rsc.org/en/content/articlehtml/2022/cp/d2cp04492g) and [complete PMC manuscript](https://pmc.ncbi.nlm.nih.gov/articles/PMC9731815/) were inspected.

Equations (1)–(2) give

    s = (4 pi/lambda) sin(theta/2),
    I(s) = gamma + beta I_neat(s) + alpha_1 I_1(s)
           + sum_i alpha_2i I_2i(s)
           + sum_i alpha_3i I_3i(s)
           + sum_i alpha_4i I_4i(s).

There are 32 templates: one monomer, five dimers, ten trimers and sixteen tetramers. Gamma is baseline; beta scales measured neat helium. Grouped regression/AIC and qualitative pickup-plausibility filters select fits. Poisson models pickup, not detector noise. Quantitative coefficient restrictions and filter thresholds are not fully specified in the inspected methods. Low-angle observations are simulated before the pair-distance transform. The data statement offers supporting data on request. [Source, Sections II–III and data statement](https://pmc.ncbi.nlm.nih.gov/articles/PMC9731815/)

The [official ten-page supplement](https://pmc.ncbi.nlm.nih.gov/articles/instance/9731815/bin/NIHMS1852641-supplement-SI.pdf) contains binding-energy comparisons and illustrated structures. Extracted text was inspected throughout and tetramer figures visually checked. No numerical diffraction matrix/profiles, coordinate table, coefficient floor, quantitative filter or calibrated uncertainty contract was found; there are no embedded files. Fig. S6 marks **4merI (+11.7 kJ/mol)** as fitted; **4merE (+5.5 kJ/mol)** is a different geometry. The main-text Table 1 says 4merE while the prose says 4merI. The supplement supports the prose identification but does not resolve which regression column generated the tabulated coefficient. Supplement SHA256: `be3ae98ac9a1ff64a7da40e3bf1008a3b617074a1ff1abb20109e0c478a50c20`.

Two provenance readings therefore remain: **I**, the table row is mislabeled and its coefficient belongs to 4merI; **E**, the row is literal and the table and narrative differ. Neither may be silently repaired. A conservative audit may include both as separate branches and certify only conclusions shared by both. This is an explicit audit enlargement, not an assertion of equal physical probability.

Later-work boundary: the verified abstract of Cruz-Chú et al., [*Helium nanodroplet force field for advancing single-molecule serial electron diffraction imaging*](https://pubmed.ncbi.nlm.nih.gov/42773707/), 22 September 2026, DOI [10.1016/j.bpj.2026.09.028](https://doi.org/10.1016/j.bpj.2026.09.028), advances forward modeling and reports qualitative peak agreement. Its full text was not reviewed; no inverse-confidence theorem is inferred. This is not an exhaustive citation census.

## 2. Separate the scientific targets

A **selected-fit target** is the output of a particular regression/AIC/filter algorithm on a dataset. Reproduction requires its complete registry, solver rules, filters and ties.

A **physical-presence target** is whether a structure has positive abundance in an admitted physical state. Establishing that target from data requires a validated observation/source/error model. An insignificant fitted coefficient is not logically zero physical abundance. A significance filter is not a physical minimum-abundance assumption.

The reported structural interpretation uses selected fitting models and auxiliary physical reasoning. This note neither refutes that interpretation nor upgrades it to a uniformly honest all-state certification theorem. A thresholded contribution or dominance label may be scientifically useful, but must be explicitly chosen; it is not automatically the paper's target.

## 3. Exact mathematical contract

On the actually observed bins, let y be the measured profile, h the neat-helium profile, and S the numerical template matrix, with common units and preprocessing. Put N=[1,h], nu=(gamma,beta), and

    F(a,nu) = S a + N nu.

Let Theta be the complete declared admissible parameter set and H:Theta -> L a finite target. A finite union of model/provenance branches is allowed. Group indices must be mapped to actual scientific labels. Do not silently assume nonnegative regression, normalized coefficients, exact geometry, bounded nuisance parameters, or an exhaustive physical library.

Given a norm and residual allowance epsilon >= 0, define

    C_epsilon(y) = {theta in Theta : ||y-F(theta)|| <= epsilon}.

The allowance must cover the intended measurement and model errors. Without a calibrated stochastic contract, it is a deterministic sensitivity parameter.

## 4. Conditional certificate and exact margin boundary

**Proposition 1.** If theta_* belongs to Theta and ||y-F(theta_*)|| <= epsilon, every nonempty singleton H(C_epsilon(y)) equals H(theta_*).

**Proof.** The residual premise places theta_* in the compatible set, so its label belongs to the singleton. QED.

For label ell put

    r_ell(y) = inf {||y-F(theta)|| : theta in Theta, H(theta) != ell},

with the empty-set infimum infinity.

**Proposition 2.** If C_epsilon(y) is nonempty and epsilon < r_ell(y), its label set is {ell}. If epsilon > r_ell(y), a compatible wrong-label witness exists. At equality, distance alone does not decide feasibility unless the infimum is attained.

**Proof.** In the first case all wrong-label residuals exceed epsilon. In the second, the definition of infimum gives a wrong-label residual below epsilon. At equality, a minimizing state supplies a witness; a sequence approaching an excluded boundary need not supply one. QED.

Thus strict separation suffices without compactness. Any claim at equality must establish attainment or exhibit an admitted witness. Replacing an image by its closure is a conservative, separately declared convention. An empty compatible set diagnoses a failed model/error/computation contract, not a structural answer.

If a justified statistical model makes the residual premise hold uniformly with probability at least 1-alpha, Proposition 1 inherits that coverage. Sequential use requires a simultaneous all-time coverage event. AIC preference and individual post-selection coefficient errors do not establish it.

## 5. Nuisance elimination and forward error

**Proposition 3.** For unrestricted nu in R^2 and Euclidean norm, let P project orthogonally onto col(N)'s orthogonal complement. Then

    min_nu ||y-Sa-Nnu||_2 = ||P(y-Sa)||_2.

**Proof.** Orthogonally decompose y-Sa into its component in col(N) and its perpendicular component. Choosing Nnu equal to the first component removes it and leaves the second; every other choice adds a nonnegative squared norm. The column-space component has a preimage even if N's columns are dependent. QED.

This requires projecting both y and every template. If beta is constrained or coupled to a, unrestricted projection is only a relaxation. Positive relaxed separation can exclude a rival, but relaxed feasibility need not be physically admissible. A best-fit helium subtraction cannot be frozen across all rival models.

**Proposition 4.** Suppose the true columns and nominal columns obey ||S_i-S0_i|| <= eta_i, ||h-h0|| <= eta_h, and remaining error has norm at most epsilon0. Then

    ||y-S0 a-gamma 1-beta h0||
       <= epsilon0 + sum_i |a_i| eta_i + |beta| eta_h.

**Proof.** Substitute the true forward equation and apply the triangle inequality to its remaining-error term, each coefficient-weighted column error, and the helium error. QED.

A coefficient-independent inflated radius therefore needs justified coefficient bounds. Calling the model a mixture does not justify sum a_i=1. This propagation is conservative; it is not a calibrated physical discrepancy estimate.

For fixed certified matrices and rational polyhedral domains, coordinate-box error yields linear feasibility; Euclidean error gives convex quadratic/second-order-cone feasibility on each convex target component. Check every component of a finite union. Strict label inequalities require explicit treatment. An unsuccessful numerical search is not an infeasibility proof.

## 6. Obstructions and their exact scope

**Proposition 5 (unrestricted discrepancy).** If an arbitrary vector e in R^m is allowed as discrepancy, every admitted theta fits every y by e=y-F(theta). Hence no nontrivial deterministic target certificate follows from that contract. QED.

This does not claim the apparatus actually has arbitrary error. It identifies what an unspecified error model cannot justify.

**Proposition 6 (vanishing component).** Suppose Theta contains an absence state theta0 and states theta_t for arbitrarily small t>0, with the tested component positive at theta_t and

    F(theta_t) = F(theta0) + t v.

At y=F(theta0), both labels are compatible for every epsilon>0. If v=0, they are already exactly observationally equal.

**Proof.** Choose an admitted t>0 sufficiently small that t||v|| <= epsilon. The residual at theta0 is zero and at theta_t is t||v||. QED.

The path must remain in the **physical** admitted class. The inspected selection filters do not prove or refute that premise. No source-specific refutation of the paper is claimed. A positive abundance floor is a new promise unless independently justified.

The obstruction is asymmetric: it prevents positive-radius absence certification at the limiting absence state and forces zero uniform class separation. A strongly identifiable positive component may still be separated from the entire absence image and admit a pointwise presence certificate. Nearby intensities alone do not prove nearby observation laws; a stochastic impossibility result needs that additional adapter.

**Proposition 7 (two error balls).** Closed norm balls of radius epsilon around u and v intersect exactly when ||u-v|| <= 2 epsilon.

**Proof.** An intersection implies the inequality by the triangle inequality. Conversely their midpoint lies in both balls when the inequality holds. QED.

An explicitly witnessed opposite-label pair at this distance prevents a universally correct deterministic classifier under the full-ball contract. A class-distance infimum equal to 2 epsilon without attainment does not itself provide a pair. An infimum strictly smaller does. This is separate from Proposition 2's distance from one observed y to the wrong image. Non-ball uncertainty requires its actual difference set.

## 7. G6 supplier and limits of transfer

The exact supplier is [G6 proof account, commit 1f2e49a9e95b79f0d20dfb0da29e59f638676d22, Sections 4.5–4.6](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md), blob `9b1f725107e0f46c09d65653ca042eea10e26d1f`, attributed there to GPT-6 Astra Pro. Its finite-target image-closure/confidence-inversion logic motivates this adapter. Its biological effective-net construction and multinomial fresh-locus concentration do not transfer to a radial intensity vector. No full compiled Lean endpoint is claimed.

The relevant reusable principle is target homogeneity over a justified compatible set. That principle is established mathematics. The contribution proposed here is a study-specific, auditable certificate application after the necessary inputs are admitted.

## 8. Empirical block and precise execution contract

Required inputs:

1. Unrounded observed and neat-helium profiles on the fitting grid, with units, scaling, masks, preprocessing and observed/imputed distinction.
2. Actual simulated profile columns and geometry identifiers, including both dimer versions and the 4merI/4merE mapping; alternatively reproducible coordinates and the complete scattering recipe.
3. Original group membership and coefficient/significance/plausibility/tie rules for fit reproduction.
4. An explicitly approved audit class, finite target, norm/error region and provenance branches.
5. Replicate/dependence and uncertainty information supporting the error allowance; otherwise only an explicitly uncalibrated sensitivity curve in epsilon is possible.

Then validate the inputs, calculate residual-margin bounds over **every** admitted branch, preserve nuisance freedom, and independently check feasible witnesses or exclusion certificates. Exclude a label only with a verified lower residual bound strictly above epsilon. Retain a label when an explicit admitted witness meets epsilon. Unresolved numerical cases remain UNKNOWN. Certify only a nonempty singleton after all rivals and both unresolved provenance readings are addressed.

No numerical fit, solver execution, author contact or empirical certificate has been performed in this audit. Pictures and energy comparisons do not replace intensity columns or uncertainty bounds. The source/theory pass is complete at its stated scope; the actual study application remains blocked on the input packet.

## Navigation

[Research Commons home](https://github.com/Sodelin/Research-Commons) · [G6 supplier](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md) · [Original study](https://doi.org/10.1039/D2CP04492G)
