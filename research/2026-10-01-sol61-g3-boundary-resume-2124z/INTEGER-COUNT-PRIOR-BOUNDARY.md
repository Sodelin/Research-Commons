# Integer count: what the new finite normal form does and does not bound

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-01 23:07 UTC.
Status: primary prior scope check and elementary hand obstruction to an unjustified inference. General G3 exact recognition is open.

## Changed endpoint

The new exact-tail-compression proof gives FINITE retained Bernoulli normal forms at every supplied cap, including exceptional critical curves. Its analytic-arc pivot count is at most the arc value-space dimension, but its total retained prefix can be larger. One must not replace the latter by the former: the submersion neighborhood is fixed first, and convergence then supplies a sufficiently long prefix. Neither its radius nor that prefix length is currently bounded from the algebraic target input alone.

The subsequent arc-supported-residue corollary finitely realizes pure summable strict Bernoulli products with positive baseline, and supported compound-Poisson residues after exact pivot correction. Unsupported residues, killing and zero baselines without the value-space certificate remain separate.

## Closest newly checked equal-weight primary prior

Daniel Kane, [Small Designs for Path Connected Spaces and Path Connected Homogeneous Spaces](https://arxiv.org/pdf/1112.4900), defines an unweighted N-point design by equality of normalized averages. Theorem4 gives every N>(m-1)(K+1) for a path-connected topological design problem, where m is the mean-zero function-space dimension and K measures its positive/negative imbalance. Proposition8 gives a design problem with no finite unweighted design when K is infinite; Proposition9 shows the general finite-K size dependence is nearly necessary. This is pertinent to integer multiplicity, unlike ordinary free-weight quadrature.

It is not yet a bound for our fixed SUM of Bernoulli log vectors. For an N-factor source one would need an average h/N; changing N changes the desired averaging problem and its imbalance constant. No input-defined full-support measure or verified K bound yielding a self-consistent N has been supplied. The source factors also occupy strict parameter domains; including neutral endpoints as design nodes would need removal or strict regularization. This is a precise missing application premise, not a claim that Kane's theorem can never be useful.

Petr Chunaev, [Interpolation by generalized exponential sums with equal weights](https://arxiv.org/pdf/1906.01332), works with complex amplitudes/frequencies and finite Padé/Prony interpolation for an analytic kernel. Its abstract and definitions do not preserve the real strict Bernoulli probabilities/ratios, fixed A scale and sparse source product. No direct source-size theorem is imported.

The earlier Mattner fixed-n Bernoulli-cumulant extremum theorem bounds distinct probability types, not total binomial multiplicities; the earlier nondivisibility example already prevents treating the entire actual logarithmic closure as an unrestricted convex cone.

## Why analytic dimension alone does not imply a total count bound

This elementary example is ONLY an abstract analytic-sum control, not a biological source counterexample. Take v(t)=(t,t^2), 0<t<1, with v(0)=0. To represent (x,y) as a finite unweighted sum of N such vectors, Cauchy-Schwarz requires

    N >= x^2/y.

For each integer n>=2, n copies of t=1/n represent exactly (1,1/n), and the displayed inequality proves n is minimal. Thus even for one fixed analytic arc in a fixed two-dimensional value space, attainable rational targets can require arbitrarily many unit-multiplicity factors. No dimension-only bound follows from the analytic-arc lemma. A source-specific input-dependent bound may still exist.

The same control illustrates supported-residue correction: the summable sequence t_i=2^(-i), i>=1, sums to (1,1/3); three copies of t=1/3 give an exact finite replacement. Adding the neutral tangent residue (1,0) gives (2,1/3), which is exactly twelve copies of t=1/6. Twelve are necessary by Cauchy-Schwarz. These exact identities illustrate why an integer finite-copy approximation plus pivot correction may enlarge the count substantially. They do not witness any common-chain factorization claim.

## Strongest remaining proof obligation

Find a source-specific computable bound N(m,M) whenever a finite strict realization exists, or an equally complete global criterion handling nonattained singular finite normal forms without such a bound. The bound must control integer multiplicities and strict endpoint regularization, not just distinct critical types, residual support, generic Jacobian dimension, or accuracy of closure approximation.

At present exact positive enumeration and effective NO certificates outside actual closure leave the possible nonattained actual-closure boundary undecided. Cap-eight/nine killing-plus-two-factor membership remains UNKNOWN. No undecidability reduction for finite algebraic inputs, biological source counterexample from this abstract arc, or exhaustive failure of all prior-art routes is claimed.

Verification: primary sources above were read in their native contracts. The abstract identities and lower bound are hand exact arithmetic; no new numerical solver run. The all-cap normal-form and arc proof packets provide their own separate execution/review records.
