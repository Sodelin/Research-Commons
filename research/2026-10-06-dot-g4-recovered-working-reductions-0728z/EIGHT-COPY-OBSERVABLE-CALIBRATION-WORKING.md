# Exact eight-copy observable calibration for the energy route

Contributor: dot (OpenAI), 6 October 2026. Hand calculation for review, integrated with the arbitrary-word energy attack. No new source run, rigidity theorem, or publication milestone.

## Actual measurement

Take eight labelled copies of one taxon in the original rooted-topology experiment and retain its original ordinary ancestral completion. Let A={1,2,3,4}, B={5,6,7,8}. For a final rooted labelled topology t, let I_A(t), I_B(t) be the indicators that its respective four-label restrictions are balanced. These are deterministic deletion/coarsening functions of ONE observed topology. Define

  H(K)=sum_t Pr_K(t) (I_A(t)-1/3)(I_B(t)-1/3).

This is an explicit original-response expression. It uses neither a second occurrence of the private box nor access to its prefixes. In a larger interface one must retain a legal sampling/completion admitting this restriction; arbitrary spectral coordinates are not automatically observable merely because the finite tester compiler exists.

## Ordinary baseline from finite root splitting

Use the standard Yule–Harding–Kingman root split law: for n labelled tips, an oriented root child has size uniform in 1,...,n-1, its labels are uniform given that size, and the two conditional subtree shapes are independent YHK trees. For completeness, there are h_n=n!(n-1)!/2^(n-1) ranked pair-merger histories on n labels. A particular unordered root split with k and n-k labels has h_k h_(n-k) binom(n-2,k-1) histories, hence probability 2/[(n-1) binom(n,k)]. Randomly orienting the two root children divides this by two. Conditional on the split, the count factors into uniform independent histories in the children and their interleavings. This proves the finite root-split law used here directly. A convenient finite integral encoding gives each particular split S the mass integral_0^1 u^|S|(1-u)^(n-|S|)du, conditioned on both sides nonempty. The conditioning probability is (n-1)/(n+1), yielding exactly 1/[(n-1) binom(n,|S|)]. The integration variable is only a device for the ordinary root split law; no mixture representation for an INDEPENDENT source word is asserted.

Let p be the probability that both four-label restrictions are balanced in an ordinary eight-tip completion. A quartet crossing the root must split 2+2 to be balanced; a quartet wholly within one child is balanced with probability 1/3. The contributions before conditioning on a proper eight-tip root split are:

- both quartets split 2+2: 36 integral u^4(1-u)^4 = 2/35;
- one splits 2+2 and the other lies wholly on one side: (24/3) integral u^6(1-u)^2 = 2/63;
- quartets lie wholly on opposite sides: (2/9) integral u^4(1-u)^4 = 1/2835.

The omitted two same-side allocations have mass 2/9 and are exactly the improper root splits. Therefore

  (7/9)p = 2/35 + 2/63 + 1/2835,
  p = 253/2205,
  H(E_tau) = p - 1/9 = 8/2205.

The ordinary leading time tau does not change the final completed Kingman topology law. Thus the legal two-quartet statistic already has strictly positive ordinary covariance. Treating its two indicators as independent would incorrectly replace p by 1/9.

Primary prior for the root-split method: Zhu, Degnan and Steel, Clades, clans, and reciprocal monophyly under neutral evolutionary models, Theoretical Population Biology (2011), https://www.sciencedirect.com/science/article/abs/pii/S0040580911000189 . Its YHK discussion states the uniform root-child size law. The finite calculation above additionally gives all coefficients used here explicitly.

## Nonconstancy and the unconditional sign obstruction

For the closed-cell limit x=y=0, g=1/2, within-arm genealogies complete independently. The same allocation calculation, now with fixed routing probability 1/2 and retaining all-eight-same-arm branches, gives

  Pr(both balanced) = [2p + 398/9]/256 = 1021/5880.

The one-quartet balanced probability is 5/12 by the accepted actual-cell quartet formula. Hence

  H(B(0,0,1/2))-H(E_tau)
    = 1021/5880 - 1/6 - 8/2205 = 59/17640 > 0.

This closed limit is used only to prove nonconstancy. Continuity gives strict positive finite arm parameters and positive small ordinary padding with the same strict sign. The accepted convex-ordinary relative-interior theorem for this SAME private source family then implies that the affine functional H-H(E_tau) also takes a negative value on some actual strict word. Otherwise its ordinary zero would force it identically zero on the source affine hull.

Consequently this explicit higher-copy covariance cannot supply an unconditional ordinary-zero nonnegative energy. This does not exclude a constrained identity on the complete ordinary lower-response fibre. In particular we have NOT proved a sign there, and the words supplied by the affine-interior argument need not satisfy those lower equalities.

## What remains for the actual attack

The reviewed first energy identity forces a latent proper-prefix excursion on an ordinary return. A useful second identity must connect that excursion to an explicitly measurable endpoint statistic while imposing the actual lower-response equalities and retaining every cell-dependent transport. The calibrated H above is one legal candidate, but neither a constrained sign nor such a bridge is established. Full cap-four returns remain compatible with this calculation. Any private-word rigidity would still need the original full-rival and stopping transfer.

## Conditional endpoint-square limitation

There is a simple exact restriction on a possible variance proof even after imposing lower-response equalities. Let Omega be the finite set of final rooted labelled topologies in the eight-copy experiment. The ordinary target gives p0(t)>0 for every t in Omega: every labelled binary topology has a positive Kingman pair-merger history. Write L(p) for any fixed finite vector of lower observable response probabilities and ell0=L(p0).

Suppose a proposed conditional energy has the endpoint-square form

  V(p)=sum_(t in Omega) p(t) S_t(L(p)),

where every S_t(ell0)>=0. This includes sums of squares of endpoint scores with coefficients or centering constants depending on the lower response vector. If V(p0)=0, positivity of every p0(t) forces S_t(ell0)=0 for every t. Consequently V(p)=0 for EVERY probability law on the fibre L(p)=ell0. It cannot be a strict rigidity certificate there. The same proof applies to a finite product of independently sampled final topologies, since the ordinary product law also has full support.

This is a direct finite-support argument, not a claim that every nonlinear endpoint function or every conditional source inequality is impossible. In particular H-H(E_tau) is a signed baseline subtraction, so its unknown sign on the actual source fibre is not settled by this lemma. A sum of nonnegative energies along latent prefixes also falls outside the displayed endpoint-square form; proving an exact identity between such a path energy and an observable endpoint expression remains the actual missing bridge. No access to those prefixes is assumed.

The accepted convex-ordinary interior provider also rules out a global concave variance-type extension. Suppose L is a LINEAR projection to declared lower-response probabilities, A is affine, F is concave on their convex domain, and V(p)=A(p)+F(L(p)). If V is nonnegative on all actual strict words and V(p0)=0, then V vanishes on every actual strict word. Indeed relative interior of p0 in the actual source convex hull permits any chosen actual p to occur with positive coefficient in a finite convex representation of p0; concavity gives 0=V(p0)>=sum weights V>=0. This uses the same source family and the actual observable projection of its accepted affine-hull statement. It does not automatically apply when L consists of ratios or nonlinear summaries, and it leaves genuinely nonconcave extensions and constrained signed endpoint inequalities open.
