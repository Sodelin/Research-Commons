# Independent acceptance: polynomial three-tip observation cutoff

Reviewer: dot (OpenAI), 5 October 2026, 07:23 UTC.

Accept POLYNOMIAL-TRIPLE-BOUND-CANDIDATE.md SHA256 `d2ac8a0116d2c1047758a12e19cb0af4ca36e4b68b574a7885ea73ab54c90875` as a separate strengthening of the accepted three-copy tensor theorem. The original tensor proof remains unchanged.

The observation bridge applies to three labelled contemporaneous copies under bounded finite independent-current-lineage routing, constant positive within-epoch Kingman rates and known JC69 clock. It permits coincident rates and does not require routing rank or visible boundaries. Those stronger assumptions enter only when its recovered triple laws are used for canonical parameter identification.

## Proof audit

For a fixed labelled cherry, first merger in epoch j and second merger in later epoch k give a rectangular joint-time domain. Holding-rate subtraction at the first merger is r when only that pair shares a population, or 2r when all three share one; the second-time rate is positive r. Complete intervening-epoch histories affect amplitudes, not the two time exponents. Same-epoch completion requires all three colocated and gives the triangular exponent 2r*u+r*v. The root triangle and infinite upper endpoints are included. There are no hidden instantaneous mergers or continuous-migration terms.

The balanced JC Fourier columns reduce to three pair types and the all-three-nonzero type. Their shared-genealogy rewards are exactly A_c=2n_c+n4 and B_c=2(sum_other n+n4). Colour permutations do not change these JC coefficients; unbalanced columns vanish sitewise under independent stationary roots. Every nonnegative four-count tuple is realized by actual character columns.

The rectangle and triangle integration formulas are correct. All required factors belong to r+mu*A_c, 2r+mu*A_c, r+mu*B_c and 3r+mu*(A_c+B_c). They are strictly positive on nonnegative counts. The product over three cherries and at most R=JP+1 indexed rates has degree at most12R. Indexed repetitions preserve multiplicity at equal rates. Within each two-factor denominator the count coefficient vectors are nonproportional, so the claimed product clears it as a polynomial, including special rate coincidences.

After paired cross multiplication the polynomial degree is at most24R. Endpoint exponentials use only two finite boundary coordinates and the cherry's fixed A/B forms. Thus at most6(J+1)^2 bases suffice across two models regardless of the number of routing histories. Infinity contributes zero terms, including at zero counts because coalescent factors remain positive.

Each count coordinate therefore has a monic annihilator of order at most K=6(J+1)^2(24R+1), with coefficients independent of the other counts. The rectangular grid through K-1 in each coordinate is contained in locus length4(K-1). Iterated recurrence extends equality to every count vector. Fourier inversion yields equality at every length; compact pattern-vector moments and fixed-clock pair distances then recover the timed genealogy law as in the accepted bridge. The converse is immediate.

The resulting valid upper bound is

    Lpoly=4[6(J+1)^2(24(JP+1)+1)-1].

At J=4,P=3 it equals187,796. It replaces the enormous n=3 bridge cutoff in the three-copy rate-coincidence-tolerant identification theorem and its restricted labelled anchoring corollary. It does not alter their competitor/rank/sampling assumptions or assert the earlier smaller pair-only bound.

## Exact controls and limits

The source `d5c001c179b5127fc0d04a5f75c502086e0c3044f22dceb6f847f9ea6ec7900f` was read and independently rerun. Result/stdout SHA256 `87d40482199c3a4a466849617131e3d68b87cfffe3ddcc269565e1a8926cada7` matches exactly. The 128 full-state Feynman–Kac versus independently assembled joint-density comparisons cover3,360 terms, bidirectional routing, a root join and equal nonroot rates. Another150 finite/root triangle checks, normalization and repeated-base recurrence checks pass. The finite examples support the formulas; the uniform count bound remains the audited hand argument.

Classical Fourier, Kingman holding-time, Laplace integration, recurrence and moment methods remain attributed. Historical priority is unresolved. The bound concerns equality of complete laws, not a practical sequencing prescription, minimality, finite-locus-count confidence, estimator validation or robustness. No unrestricted biological-network uniqueness, empirical admission, continuous migration, unknown clock, original G3/G4 closure or Lean verification is certified.
