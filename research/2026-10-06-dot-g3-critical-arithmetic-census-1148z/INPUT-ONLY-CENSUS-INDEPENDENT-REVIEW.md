# Independent review: input-only algebraic-residue critical census

Reviewer: dot (OpenAI), 6 October 2026, 11:43 UTC. Hand review, after the fixed 10:03 scientific cutoff.

Accepted for exactly the stated finite-presentation predicate. Reviewed proof: INPUT-ONLY-ALGEBRAIC-CRITICAL-CENSUS.md, SHA256 55a34558bccb2e53890d8342db5b3136f7f56398a9a7e84df56849ece4e55dfc. Input is one positive effectively real-algebraic six-coordinate cap-seven COMMON tuple, with 0<m_1<1. The algorithm supplies the count bound itself; it does not receive a closure promise, an anchor, a residue, or a retained-factor count.

## Completeness and termination checks

- Membership in the drift/killing endpoint surface is genuinely algebraic: recover A=sqrt(m_3/m_1) and K=m_1/A, then check all six equations and 0<A,K<=1. Testing only the displayed Holder equality would not by itself justify an E0 decision; the proposed algorithm checks the full tuple.

- On E0, the desired critical-presentation list is empty. For a supplied algebraic residue, the old all-residue finite critical-locus theorem and positive pair loss turn any summable retained list into a finite multiset. The analytical probability-one variable e^(-a) r^Z product q_i^(Bernoulli_i), with positive Poisson parameter w/(1-r), is strictly positive and nonconstant. Holder interpolation between powers 1 and 6 is therefore strict: m_3^5<m_1^3 m_6^2. E0 gives equality, a contradiction. The Poisson variable here verifies the moment identity; it is not smuggled into the finite physical source class. Returning an empty critical list is not a source-NO answer, since ordinary sources lie on this surface.

- Off E0, choosing rational rho<m_1 is enough for the previously accepted compact endpoint algorithms: any E0 representation has A,K>=m_1, and the accepted K1 emptiness result places the upper endpoint envelope inside the drift/killing envelope. Thus the input lies outside both relevant compact envelopes. The endpoint-exclusion and uniform critical-loss arguments bound all possible paired-critical presentations for the same tuple; they are necessary-model algorithms and do not need prior closure membership. Their terminating search supplies an integer N.

- The accepted height proof R2 then gives the finite rational-residue census. Its use of the old Baker/projective result is indispensable: algebraicity of the observed tuple alone never implies algebraicity of a residue. Here the predicate expressly restricts the residue to be algebraic; on that branch the older theorem forces it to be rational. Critical-pair isolation, multiplicity enumeration and exact algebraic power-product comparisons then enumerate all successful presentations, with a,w represented by exact real logarithmic expressions.

- Lists are identified up to permutation. Positive loss bounds multiplicities, so the output is finite rather than merely a countable search. All entries refer to one coherent full six-coordinate tuple; no rowwise relaxation or independently chosen hidden kernels is introduced.

## What has and has not been decided

The result is an input-only decision and complete finite list for the algebraic-residue paired-critical presentation predicate. It is not an arbitrary actual-word length bound or a decision of actual source membership. A listed critical presentation may have a remote actual realization; the saddle examples already demonstrate this. The separately reviewed logarithmic-curvature filter can certify actual YES for suitable entries, while PSD and lower-rank survivors stay unresolved. Transcendental residues, extraction of a coherent tuple from positive-dimensional original joint fibres, other flags/interfaces and all competing cores remain outside this theorem.

No input-dependent endpoint search, height bound, census, root isolation, QE or source search was executed for this corollary. The earlier small universal integer-constant check is separate evidence. This acceptance does not change the fixed 10:03 scope record or close original G3.
