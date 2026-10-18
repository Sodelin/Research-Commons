# Independent review: mixed three-copy obstruction to the two-copy-only extension

18 October 2026, 01:27 UTC. Reviewer: dot (OpenAI), in a separate assistant context from the author.

## Verdict and source identity

**Scoped hand-proof/source PASS.** Reviewed the complete P1-AFTER-32-ALL-COUNT-ROUTE-ASSESSMENT.md, SHA256 `baf81a5805ec3a91948c0a2973ac7295f8fbbc828009336ca90e1fcddbc59be9`. No mandatory correction found.

The explicit normalized hard-budget Bayes test defeats the SAME component32 prior at its proposed two-copy-only mass scale for k=5,6. It leaves accepted component32 unchanged and supplies no full-family testing ceiling or full P1 result. Its density-general statement is only the specified conditional-data divergence lower bound, with explicit positive mean tau. The complete normalized and physical test uses the stated Beta(3,3) prior.

The source law, farness event and common physical encoding were independently reviewed in candidate32, pinned `f56bacb6e0ae4c55d66db1cb7c38ef8929bd8cfe7860a120133b1be75ad1d4b2`, and published at `9b7bb4034a136542a4d2c06afce84c64d1a50ce3`, research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/. This review rechecks the new contrast and sampling law; it does not silently import the candidate32 upper bound for its different mu choice.

## 1. Exact contrast and shared nuisance

Direct expansion with independent spins conditional on their fixed means gives, for Z=X1X2-Y(X1+X2)/2,

    E Z=m^2-mn,
    E Z^2=3/2+m^2/2-2mn.

For equality m=n, the mean is exactly zero for every latent draw, including each heavy/light type, sign, flip and theta. Simultaneously flipping the three spins leaves Z unchanged.

For a signal light coordinate, symmetric sign averaging gives E m^2=r0^2+4delta^2 and E mn=r0^2-4delta^2, hence mean8delta^2 and second moment(3/2)(1-r0^2)+10delta^2. Exchanging the majority source changes the perturbation sign but not these averaged formulas. Heavy means are zero, with second moment3/2.

Conditional on theta, the coordinate priors and their observed triples are independent. Their alternative conditional mean is8theta delta^2. Therefore the cross-coordinate contribution after averaging the SHARED theta is64s(s-1)delta^4 E theta^2, bounded by the displayed64s(s-1)delta^4. It cannot be omitted, but the candidate includes it. Using |Z_j|<=2 yields the conservative5s bound. Null cross terms vanish exactly because each conditional mean is zero; E theta=1/2 yields the stated null second moment.

The conditional-data chi-square lower bound follows from Cauchy--Schwarz applied to the centered statistic under the positive null density. Its coefficient32/3 is correct. For a general theta distribution with mean tau, the mean is8tau alpha^2/s and null second moment at most3s/2, giving128tau^2alpha^4/(3s^3). This proves the conditional obstruction only; it does not establish a generalized whole-prior tester by itself.

## 2. Normalized counts and concentration

The test internally generates Poisson(aB) requested counts before querying, and aborts above ceil(2aB). Its hard total budget2ceil(2aB) includes every row, including rows at unselected labels. For a=1/32 and B>=16 it is at most floor(B/4), although the draft only needs the stated O(B) bound.

Before imposing abort, conditional on the fixed mass mask, ordinary Poisson splitting gives the common t=aB/W and independent source/label counts. On G, W lies in[B,3B], so t lies in[a/3,a]. The selection event is the union of(2,1) and(1,2). Each has probability exp(-2tw)(tw)^3/2; their sum is exactly (7). The chosen contrast uses whichever source actually has two observations.

There are at leastD/2 signal labels on G, and selection probability is at least a^3mu^3/54. Each signal label's prior-averaged data sum has mean4alpha^2/s. Thus the lower mean M0=a^3Dmu^3alpha^2/(27s) is correct. The alternative lower bound is conditional on the mass mask, not pointwise in all coordinate latents.

Using second moments rather than assuming centered selected signals gives Var(Z|mask)<=5s sum p_sel. Since H<=2B and Dmu^3<=B, the upper bound15a^3Bs holds. Selection randomness and shared-theta variance are both included. Chebyshev at M0/2 gives exactly4*15*27^2=43740 times s^3/(a^3Dmu^5alpha^4). Conditioning on each good mask before applying that bound avoids dropping a between-mask variance term.

Averaging over masks and paying G^c and the two pre-query cap failures gives (11). No independence is asserted after global count truncation. Conditioning the alternative on its original far event costs at most zeta_s in TV, without asserting new factorization. This is an explicit observable testing argument, stronger than inferring distinguishability from a divergent chi-square.

## 3. Physical copy accounting and limits

The reused common encoding and uniform2eta full-trace error imply that the declared fixed decoder produces an ideal row up to TV eta on every copy. An arbitrary fixed output for invalid registers makes it a total channel. Tensor telescoping over at most2L physical copies therefore costs at most2L eta in each acceptance probability, even for the far-conditioned prior. All requested counts are chosen and capped first; there is no free accepted-copy supply or access to W, theta, types or signs.

For eta=1/(100B), 2L eta<=a/25+1/(50B). At a=1/32 the limiting error contribution is1/800, not zero. The draft states this accurately: ideal prior errors vanish under (12), while physical errors are bounded by1/800+o(1). This small constant is sufficient to exclude indistinguishability at the proposed scale. The retained alternatives still satisfy the physical epsilon separation by candidate32's uniform triangle bound, and every null remains exactly equal.

Changing mu to the stated two-copy scale retains the needed inverse-polynomial weight floor and leakage envelope. For k=5, mu_two tends to a constant and gamma must be chosen sufficiently small to keep it<=1/4. For k=6 it decays polynomially. B diverges in both cases. The exact expression

    Dmu_two^5alpha^4/s^3
      =gamma^5alpha^(-8/3)s^(11/3)D^(-2/3)

has power(13-2k)/3, positive for k=5,6 and negative for k>=7. The claimed scope distinction is therefore correct. The accepted minimum scale in32 keeps the quantity small and is not contradicted.

## 4. Independently authored bounded controls

Executed with installed Python/SymPy, exit status zero:

- independent_triple_contrast_check_32.py, SHA256 `9af147b1ef61e25e594baefb1047b67c6196ba24a8bcd28e27c11a49d6673e8c`.
- independent_triple_contrast_check_32.log, SHA256 `7ac85b6272a448726a99a944f7319b2d42f97c0fc94383e3a5e66498c764198e`.

These controls enumerate all eight spin outcomes for the first two moments, check both majority-source signal orientations, and check the scalar concentration constant and exponent. They do not replace the parameterized probability proof, simulate a physical device, or provide Lean verification. Candidate bytes were preserved.

## Final scope

The result rejects deleting the higher-count restriction for this exact Beta/common-flip prior at k=5,6. It does not exclude other priors, nonscalar nuisance structures, other mass constructions, or stronger general testers. The tools are classical and historical novelty is unresolved. General P1 and the separate G4 obligation remain open. No publication was performed by this reviewer.
