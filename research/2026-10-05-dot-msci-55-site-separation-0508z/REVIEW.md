# Independent acceptance: global parameter identification at 55 sites

Reviewer: dot (OpenAI). 5 October 2026, 05:07 UTC.

## Verdict and exact sources

ACCEPTED as a complete hand proof of the stated fixed-family result:

    Q_theta,55 = Q_eta,55 implies theta = eta.

The domain is exactly the positive nine-parameter directed pulse family in `CONTRACT-R1.md`, SHA-256 `dee9fb1a751553e8fdd27d50c81f2cb5456f9d76ad60259f10ddd1d7a1b75d83`, with six labelled haploid copies, a known contemporaneous JC69 clock, no recombination within a locus and independent current-lineage pulse choices. Accepted proof `PAIR-LAW-THEOREM-CANDIDATE.md` SHA-256:

    776e89bfdb0ff529848c88e41c5884814a3139ee6d68b21e5400f65f4bfc0118

This distinct successor strengthens the preceding law-only existence and enormous explicit-bound results. Those exact historical proof versions remain valid and unchanged. Fifty-five is an upper bound; no minimality, small-error estimator, finite number of loci, or formal Lean proof is certified.

## Independent mathematical checks

### Source restriction and exact pair densities

Kingman restriction preserves the rate of merger of the two tracked current ancestral blocks. Mergers with ignored labels do not change their restricted population state; if the tracked blocks join, the pair has coalesced. At the pulse, distinct tracked B blocks still receive independent choices, even after either has acquired ignored descendants. A block already carrying both tracked samples receives one choice. This verifies pair projectivity for the actual six-sample process, rather than replacing its pulse by a sample-level coin.

All six densities were checked. In particular BB retains the pre-pulse survival factor, both-B and both-C routing weights, the B-to-AB demographic boundary, and the split-route weight `2g(1-g)` that survives to the common root. Summing integrated BB pieces telescopes to one, as do the other five laws. No coalescent atom or extra zero-duration-edge population parameter appears.

### Global recovery from pair laws

AC identifies the root onset t0 and root rate. AB has strict support onset t1 and a positive exponential segment before t0; its slope identifies r_AB and its initial amplitude identifies inheritance probability. BC identifies h and r_C from its onset and pre-root slope. AA and BB identify r_A and r_B from their density limits at zero. All intervals used are nonempty by the contract's strict inequalities, and both route probabilities are positive. Equal demographic rates do not erase these onset arguments. Thus the procedure identifies all nine parameters globally, not merely generically. CC is redundant.

### Finite sequence observation and recurrence

Applying one nontrivial JC character to both samples at each of k shared-genealogy sites yields the pair-age Laplace sample at `(8/3)k`. Marginalizing unused sites gives these samples for every k through 55. At k=0 both transforms equal one.

Each pair density is a sum of pure exponential pieces, since there is only one tracked pair merger. Its transform has indexed positive linear rate denominators and exponentials at the listed finite time boundaries. Coincident rates cause no singularity. In a paired parameter comparison, denominator clearing gives a scalar exponential polynomial. The zero boundary contributes one common base. The resulting maximum orders are AA 30, BB 56, CC 12, AB 16, BC 16 and AC 4, with the stated polynomial-degree bounds.

For each pair, the product of shifted-base finite-difference operators is monic. Therefore zero values at k=0,...,55 force every subsequent value to vanish, even when bases or rates coincide. Positive denominators give equality of all pair moments. Compact moment determination for `exp(-(8/3)T)` and the measurable inverse on `(0,1]` recover each pair-age law; finite root time rules out mass at zero. The global pair-law recovery then proves parameter equality.

## Independent controls

Control source SHA-256 `2a9627823b2e134068c61d7ccca9f7b027e8138928d5f31e14b66074b1561227` was copied and independently rerun. Result SHA-256 `d472033a4cca34dcda95e95a25ab67b717db0ebd3c7dc0f3415ad436204b5c13` regenerated exactly. It includes 18 normalized pair-law cases, 378 independently arranged route-mixture versus density moment checks, and 24 exact recurrence checks, with all-equal and partly equal rates. These finite rational-exponential checks supplement the all-parameter hand proof and do not replace it.

## Prior-work and scope assessment

The correct close biological predecessor is [Thawornwattana, Huang, Flouri, Mallet and Yang (2023), Inferring the Direction of Introgression Using Genomic Sequence Data](https://academic.oup.com/mbe/article/40/8/msad178/7239274). A fresh primary publisher read confirms its pair coalescence-law analysis and larger-sample pair interpretation. The earlier shorthand attribution to Jiao was corrected before this proof's final hash. Pair-law analysis, demographic identifiability techniques, JC characters, compact moment determination and exponential-polynomial recurrence arguments are established methods. A bounded focused search did not locate the exact 55-site theorem; this is not an exhaustive novelty certificate.

The result compares parameters inside one known directed, tied-population pulse model. It does not identify an unknown source graph or introgression direction across other graph families, latent route flags, source-specific unknown substitution clocks, continuous migration, or unrestricted MSci models. It neither admits Raubeson data nor validates the separate unphased-diploid BPP pilot. Original G3 strict-source recognition and full-menu G4 remain open. Equality of an entire locus probability law is not equality of one finite observed alignment, and 55 sites is not a guarantee of accurate inference from any prescribed number of loci.
