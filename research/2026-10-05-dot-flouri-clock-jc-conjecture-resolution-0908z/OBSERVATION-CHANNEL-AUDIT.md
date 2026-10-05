# BPP observation channels and the clock-JC conjecture closure

Author: dot (OpenAI), 5 October 2026. Read-only primary/source audit for independent review. No fitting, new statistical diagnostic, software execution or speculative extension proof. This audits the 2020 paper's model descriptions and the pinned current BPP4.8.7 source; it does not pretend to be a line-by-line audit of an unvendored2020 executable.

## Bottom line for the closure statement

The accepted bounded observation bridge directly covers **complete labelled haploid sequences, contemporaneous samples, a known normalized homogeneous stationary JC clock, and one shared genealogy across all sites of each locus**. For each fixed finite MSci source/panel, its finite-length equivalence concerns the route-marginal rooted timed-genealogy law in mutation units. It does not require that the demographic parameters themselves be identifiable. Coincident population rates, expansions and latent network ambiguities are not extra observation-channel gaps.

This matches the explicitly qualified clock-JC interpretation in CONJECTURE-RESOLUTION.md. Software support for unphased genotypes, unknown locus rates or relaxed clocks is not a proof for those different channels and is not a reason to withhold the stated baseline closure.

## Primary-paper scope

Flouri et al.'s2020 paper writes a likelihood integrating sequence likelihoods over one gene tree per locus; sites share that genealogy and loci are independent conditional on the source. It measures times and population sizes in mutation units and formulates the sequence-versus-timed-genealogy identifiability question. Its spruce analysis uses phased sequences and either constant or Dirichlet-distributed relative locus rates. JC is used for analyses; GTR+Gamma simulations do not themselves establish identifiability under a broader mutation model. These alternatives must be distinguished in the closure's hypotheses. [Primary paper, model/identifiability and empirical sections](https://academic.oup.com/mbe/article/37/4/1211/5673394).

The2022 restatement and bidirectional-introgression equivalences are addressed in the companion closure audit. This note supplies observation-channel typing, not a claim of historical novelty or priority.

## Exact baseline channel

Let P be the law of a contemporaneous n-labelled rooted metric genealogy T, ending at its sample MRCA, after population paths and routing flags have been marginalized. Let p_T(x) be its complete one-site DNA-pattern probability under Q with diagonal−1, off-diagonal1/3, and uniform independent root state at each site. For an ℓ-site locus:

    Q_(P,ℓ)(x_1,...,x_ℓ) = integral product_(s=1)^ℓ p_T(x_s) P(dT).

The product is INSIDE the genealogy integral. Replacing this by a product of one-site expectations redraws the genealogy across sites and changes the experiment. Likewise, treating inferred gene trees as observed or keeping MCMC route flags as observations changes the target.

Current source matches the normalization: locus.c sets JC frequencies to1/4; its JC transition matrix uses exp(−4b/3), where b is elapsed genealogy time times the locus multiplier. With a global clock, no population-path-specific mutation history is needed beyond T. The accepted theorem applies to this ideal probability law, not to finite floating-point outputs.

A stationary reversible mutation process alone does not identify a root position on an arbitrary nonclock metric tree. Contemporaneous ultrametric time geometry and known scale are essential parts of the stated channel. No stem above the sample MRCA is inferred. Calendar time is a different target: without an external mutation calibration, scaling generations/population sizes by c and mutation rate by1/c preserves mutation-scaled observations.

## Phase0 versus phase1

**Complete phase0 haplotypes:** each row is one labelled gene copy and its site bases are observed. This is the baseline alphabet. Ambiguous/missing bases, deleted sites, uncertain pairing or genotype errors add coarsening/ascertainment channels; their identifiability is not inherited merely by setting phase0.

**Ideal phase1 diploid genotypes:** a known pair of copies belongs to each individual. At each site, C replaces the two ordered nucleotides by their unordered genotype, encoded by a homozygous base or a two-base IUPAC symbol. The normalized one-site law is

    q_T(y) = sum_(x:C(x)=y) p_T(x),
    Q^dip_(P,ℓ)(y_1,...,y_ℓ) = integral product_s q_T(y_s) P(dT).

Equivalently this is the deterministic genotype projection of the complete haplotype-alignment law. It loses phase ACROSS SITES: haplotype pairs AC/GT and AT/GC both produce the genotype string RY, although they are not related by merely swapping the two entire haplotypes. Consequently, the earlier within-individual allele-swap-invariant genealogy diagnostic is not an injectivity proof for this observation channel.

Current diploid.c duplicates each declared diploid row into .1/.2 gene copies, fixes selected orientations at site patterns with multiplicity one to remove phase redundancy, and expands remaining site resolutions. locus.c then averages corresponding likelihood entries. These symmetry-reduced calculations and data-dependent normalization should not be mistaken for a literal normalized probability vector on all genotype observations at a fixed arbitrary labelled T. For an identifiability statement, use the generative genotype projection above and separately justify any implementation likelihood normalization/gauge reduction. The source README attributes analytical phasing to Gronau et al.; that existing inference method is not a general MSci genotype-channel identifiability theorem. [Gronau et al.2011](https://www.nature.com/articles/ng.937).

Pointwise, T and a within-individual allele-swapped T have the same genotype kernel. This does NOT by itself prove extra demographic nonidentifiability: admitted genealogy laws may already obey the relevant exchangeability. What remains to prove for a claimed extension is injectivity of the genotype observation map on the specified family of genealogy laws, or precisely the right quotient of that family. No such extension is claimed here.

## Locus rates: three different experiments

**Constant normalized multiplier1:** directly covered by the accepted homogeneous-clock theorem.

**Known fixed positive multiplier r:** the channel uses p_(rT), where all genealogy times are multiplied by r. A short rescaling corollary is submitted for review: replace epoch durations δ by rδ and coalescent pair rates λ by λ/r; routing is unchanged. This stays in the same bounded source class, and scaling T back is invertible. Hence the accepted finite-length bridge transfers to a known fixed positive r. For known locus-specific r_i, retain locus identities and condition on each known multiplier; the same reasoning applies locus by locus at a sufficient length. Equality of full data laws gives equality of the relevant marginals. This is not an assertion for any prescribed short empirical locus.

BPP's fixed-rate-file option normalizes the supplied positive relative rates to mean1 before fixing them. The theorem's known r_i must be those normalized values. Estimates from an outgroup used as plug-ins are not uncertainty-free observations in a broader statistical model. Zero-rate loci carry no mutation-time information and are excluded from this rescaling argument.

**Unknown locus-specific rates:** distinguish joint nuisance-parameter identifiability from a prior-integrated observation experiment. In the relative Dirichlet case with M loci and mean1, r=Mw for w on a simplex. Conditional on r the likelihood is a product of locus integrals. Marginalizing rates gives

    integral [product_(i=1)^M integral p_(r_i T_i)^(tensor ℓ_i) P(dT_i)] π(dr).

The rate prior may couple loci. This is not the baseline homogeneous kernel or generally independent repetition of one unmodified locus law. The average-rate constraint fixes a scale convention; it does not prove channel injectivity. An extension must specify whether rates/hyperparameters are fixed unknowns, observed covariates, or marginalized random variables, and then establish injectivity/deconvolution on that exact family. No unknown/Dirichlet-rate mixture conclusion follows automatically from conditional known-rate identifiability.

Current option parsing distinguishes constant, estimated and fixed-from-file rates. Estimation admits Dirichlet/Gamma-Dirichlet or hierarchical alternatives; dates can introduce an absolute mean-rate parameter. Relaxed clocks additionally make branch mutation lengths depend on population paths/rates, so ordinary route-marginal T may no longer be a sufficient latent object. These are separate contracts. [Official option reference](https://bpp.github.io/bpp-manual/bpp-4-manual/).

Site-rate mixtures are yet another ordering: conditional on T, independent per-site rate draws replace p_T by an averaged one-site kernel before taking its tensor power. A shared random locus rate instead lies outside that product. Neither ordering may be silently substituted for the other.

## Stronger existing results, with their own targets

- Allman, Ané and Rhodes prove identifiability of the GTR+Gamma model on a single phylogenetic tree, with broad parameter coverage including the four-state case. This is substantive prior theory for continuous rate heterogeneity; it is not the arbitrary MSci timed-genealogy-law/unknown-locus-rate mixture equivalence considered here. [Primary paper](https://arxiv.org/abs/0709.0531).
- Chifman and Kubatko establish generic identifiability of the unrooted species-tree topology under a coalescent model with time-reversible substitutions, discrete-gamma site variation and invariable sites. Thus some stronger mutation-channel assumptions have established results for a narrower target. This does not establish recovery of every timed-genealogy law or arbitrary reticulate source. [Primary paper](https://arxiv.org/abs/1406.4811).

No broad negative claim is made about the unresolved channels, and this bounded source search does not certify that no other relevant theorem exists. The correct closure remains affirmative for the specified complete-haplotype homogeneous clock-JC experiment, with each optional broader channel separately typed.
