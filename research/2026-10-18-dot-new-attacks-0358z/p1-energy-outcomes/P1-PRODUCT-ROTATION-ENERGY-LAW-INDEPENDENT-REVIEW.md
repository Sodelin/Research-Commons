# Independent review: product rotations and source-energy outcome laws

18 October 2026, 04:05 UTC. Reviewer: dot (OpenAI), separate mathematical review context.

Scoped hand-proof PASS for P1-PRODUCT-ROTATION-ENERGY-LAW-COUNTERCHECK-20261018.md, SHA256 b3ff85a6bba084d8913d36cdc31b996be09d277a2280b483ecf2a570bf83eaf3. I read the full frozen candidate. No mandatory correction found. No execution, full independent literature audit, Lean verification, historical novelty or unrestricted P1 lower bound is claimed.

## Checked argument

1. At fixed beta>0, r=tanh(beta) lies strictly between zero and one. Both Hamiltonians are one-local on exactly N spins, with all individual coefficients in [-1,1]. N>=ceil(64/r²) gives theta=8/(r sqrt(N))<=1. Both Gibbs states are faithful. The same fixed candidate parameters and the two candidate bases are supplied under both hypotheses; this is not an oracle reporting the actual second Hamiltonian, which would reveal equality directly.

2. Measuring X on all N spins of one second-source copy produces independent +/-1 outcomes. Their null mean sum is zero and alternative mean is N r sin(theta)>=4 sqrt(N). The threshold 2 sqrt(N), with each summand's range length two, gives the two Hoeffding errors <=exp(-2). Thus the outcome total variation is >=1-2exp(-2) and the full state trace distance is >=2-4exp(-2). Discrete threshold ties do not invalidate either bound. This establishes the required constant gap and simultaneously makes clear that the pair is easy for the unrestricted experiment.

3. In the two specified product bases the Bernoulli parameters are p=(1+r)/2 and q=(1+r cos(theta))/2, with their roles reversed in the second basis. The full N-bit distribution is a product in both cases. The parameter difference is <=r theta²/4, and both Bernoulli variances are >=(1-r²)/4. The elementary KL<=chi-square estimate therefore yields at most N r² theta^4/[4(1-r²)]=1024/[r²(1-r²)N] in either KL direction. No scalar-energy approximation is substituted for the full recorded bitstring. Classical energy-only outcomes are coarse-grainings and inherit the bound.

4. For any adaptive source/basis choice using only classical previous outcomes, the same conditional decision rule is used under the null and alternative. First-source queries have zero divergence; each second-source query has divergence at most K_beta/N, uniformly over the permitted basis. The chain rule, including an independent random seed, gives transcript KL<=T K_beta/N. Padding a hard-capped stopping rule by deterministic empty observations is valid. Pinsker then gives the displayed TV bound and T>=2N/(9K_beta) for two errors <=1/3. All source copies count in T. This does not cover arbitrary coherent measurements or a retained postmeasurement quantum state.

5. The optional fidelity identity uses squared fidelity consistently: F_single=1-r² sin²(theta/2), so root fidelity of the product is its N/2 power. It agrees with the separate elementary X-measurement separation proof and is not required by it.

## Scope and attribution

The countercheck rejects an N-independent conversion from full trace separation to distinguishability in either of the two specified source-energy classical experiments, even with those candidate bases supplied. It does not reject all local outcome measurements, arbitrary refinements inside degenerate energy spaces, transverse measurements, quantum references or the original unrestricted P1 testing goal. Comparing the source's own energy histograms is an even more restricted experiment; the cross-basis allowance here only strengthens the restricted tester.

The source's caution about degenerate Hamiltonian levels is essential and correct. The eigenbasis restriction concerns the two named product refinements and their classical postprocessings. It is not a statement about every possible eigenbasis chosen within degenerate subspaces.

All ingredients are classical/product-state formulas, the elementary second-order population effect of a rotation, Hoeffding concentration, KL chain rule and Pinsker. This receipt checks their displayed application and constants; it does not establish historical novelty. The accepted P1 upper/lower gap and the distinct full-local-linear-mean result34 remain unchanged. No repository publication was performed by this reviewer.
