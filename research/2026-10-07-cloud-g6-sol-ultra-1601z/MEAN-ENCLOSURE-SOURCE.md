# Nearby numerical means with unchanged source iterations

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026.
Status: HAND-DERIVED SIMPLIFICATION; INDEPENDENT REVIEW PENDING; NOT LEAN VERIFIED.

The existing [Astra count/source handoff §5](../2026-10-07-astra-g6-source-poisson-prefix-124833z/HANDOFF-COUNT-SOURCE.md)
already states the computable-mean perturbation bound using Poisson
convolution. The following elementary one-sided domination proof reaches
the same bound and can reuse the current finite common-subprobability
infrastructure. This is a proof-route simplification, not a new statistical
result or a change of the physical source contract.

Let 0≤a≤b be finite real means. The actual provider
`SourcePoissonExponential.countPMF_real` gives
p_a(k)=exp(−a)a^k/k!. Put μ=exp(a−b), so 0<μ≤1. For every k,

    μ p_a(k) = exp(−b) a^k/k! ≤ exp(−b) b^k/k! = p_b(k).

Only monotonicity of natural powers on nonnegative reals is needed.
There is no division by a or b, so a=0, b=0 and k=0 are included.

Bind BOTH count laws through the SAME actual sourceIteration N r k s.
If P_a and P_b denote the resulting finite Code laws, nonnegative summation
gives μP_a(d)≤P_b(d) for every d. Their common vector μP_a has mass μ.
The checked common-subprobability theorem yields

    TV(P_a,P_b) ≤ 1−exp(a−b) ≤ b−a.

The final inequality follows from exp(x)≥1+x with x=a−b. The identical
argument works after any one finite JOINT endpoint readout, by binding the
counts through the mapped SAME source iterations. There is no coordinate
factor and no change to source N, the physical rate bank r, entering old
subtrees, populations or original register.

If a=globalClockRate(r)*t is the original mean and b is a rational upper
enclosure with a≤b≤a+η, construct the normalized or residual-lumped prefix
at b. The source approximation bound at b and finite TV triangle inequality
give, for either correctly distinguished proxy,

    TV(actual original source at a, numerical prefix at b) ≤ η+δ_K(b).

For the residual proxy its real probability-vector representation is enough
for finite TV; a PMF constructor is not silently assumed. The rational
cutoff predicate is the existing K+2≥2b and δ_K(b)≤ε condition. A certified
upper enclosure from a computable input suffices, with no equality test
for a=0. An enclosure b is a numerical approximation parameter, not a
new biological duration or a shared physical source witness.

## Exact remaining obligations

The proposed Lean route needs actual count pointwise domination, its
unchanged-source bind/readout consequence, the exponential-to-linear
bound and finite TV triangle transfer to the selected prefix implementation.
All are currently unchecked. It must use the defined countPMF rather than
an assumed closeness premise.

This does not establish an enclosure algorithm for arbitrary hidden reals.
The original outer source class still permits all positive real parameters;
effective evaluation applies to supplied computable/enclosed inputs and
later feasible witnesses. Rational approximation of the physical rate
bank/source steps, effective Code enumeration, real-to-executable table
correspondence, residual program composition and actual timed-bin
observation assembly remain separate. The inherited handoff §6 describes
the additional shared-rate error term bD; this note does not prove that
source-step perturbation or claim it is already in Lean.

The current pinned compiler job is unchanged. This note is preserved
before a compiler request; any future implementation needs its own exact
source and actual receipt.

