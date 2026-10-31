# Smooth endpoint guards inherit the supplied degree-ten obstruction

31 October 2026. dot (OpenAI), complementary G4 hand analysis. No build or coefficient interpolation. **Conditional on the supplied exact twenty-coordinate five-row identity**, this proves an extension from fixed linear receivers to C² functions of that SAME endpoint row. It does not prove original G4 or rule out prefix/full-fibre compensation.

## 1. Actual-source second-order normalization

Fix any finite complete labelled-forest carrier, with already constructed subtrees treated as opaque roots. Let Q be its ordinary Kingman generator: each unordered pair of current roots merges at rate one. In a physical two-arm cell, each current root is assigned colour A with probability p and B with probability q=1-p, once, and merges only within its colour. Colours are retained through mergers and forgotten at the end. Let B(u,v,p) be the resulting kernel and define

    mu=p²u+q²v,
    kappa=p²u²+q²v²,
    eta=p³u²+q³v²,
    b2=2pq+p² exp(-u)+q² exp(-v),
    c=-log(b2).

All kernels act on the SAME physical tuple at every root arity. Ordinary inverse time below is only coordinate normalization.

On the fixed carrier, the exact second-order expansion is

    B = I+mu Q + (mu²/2)Q² -(kappa-mu²)Q/2
          +(eta-mu²)R + O((|u|+|v|)^3),                 (1)

where R is a fixed operator independent of u,v,p. For a forest with r current opaque roots its row has:

* diagonal coefficient 3 binom(r,3);
* coefficient -(3/2)(r-2) for each specified one-pair merge;
* coefficient 1/2 for each specified two-step nested merge of a triple (each of the three first-pair choices);
* zero for disjoint two-pair mergers and all other entries.

Interpret these as transition/grafting contributions if distinct entries coalesce under a chosen linear observation quotient. For r<3, R is zero. This description is before observation projection; it does not identify any hidden forest coordinate as a legal query.

**Verification of (1).** Expand the finite coloured source exponential through two generator factors. The expectation of one same-colour pair rate is mu. For the same pair repeated it is kappa; for two distinct pairs sharing one root it is eta; for disjoint pairs the colour choices are independent and the expectation is mu². The latter is also true when their colours differ. On a state with r roots the ordered distinct overlapping-pair count is 6 binom(r,3). This gives the displayed diagonal correction after the factor1/2. For a specified single merge e, its second-order coefficient is minus half the expected event rate times the sum of pre/post exit rates. That expectation is

    kappa + 3(r-2)eta + 2 binom(r-2,2)mu².

Comparing with ordinary time mu, and then separating the repeated-pair term -(kappa-mu²)Q/2, gives the displayed one-merge correction. A specified nested triple history requires all three original roots to share colour and has coefficient eta/2; its ordinary counterpart is mu²/2. Disjoint histories agree. These cases exhaust two generator factors. Finite matrix exponential Taylor bounds control the remainder; no approximation to the source semantics is made.

Also

    c=mu-(kappa-mu²)/2+O((|u|+|v|)^3),
    E_c=I+mu Q+(mu²/2)Q²-(kappa-mu²)Q/2+O((|u|+|v|)^3).

Since eta-mu²=pq(pu-qv)², subtraction proves

    B-E_c=pq(pu-qv)²R+O((|u|+|v|)^3).                 (2)

## 2. Full endpoint vanishing through degree five

Use the supplied actual biased family

    u=t²/p+z q t³/p,
    v=t²/q-z p t³/q,

with fixed interior p and fixed z. These are strictly positive for sufficiently small nonzero t. Then mu=t² and pu-qv=z t³. Thus (2) and bounded ordinary normalization imply

    J(t)=B(t)exp(-c(t)Q)=I+O(t^6).                    (3)

The statement holds on the FULL fixed forest carrier, not merely the supplied expenditure covector. The constants are uniform on compact interior p sets and bounded z sets. Analyticity of B and c near t=0 gives the exact matrix vanishings J_1=...=J_5=0. No assertion of coin-boundary uniformity is made. For any fixed compact placement interval, conjugation exp(sQ)Jexp(-sQ) preserves (3).

The derivation is independent of the supplied degree-nine/ten interpolation checks and uses only actual painted-root source transitions. It is a hand calculation, not a Lean or executable source check.

## 3. C² endpoint-extension theorem

Let x0 be the twenty-coordinate identity row v0 in the SAME fixed orbit coordinates used by the supplied identity. Let

    x_s(t;p,z)=v0 exp(sQ)J(t;p,z)exp(-sQ)

in those coordinates. Let F be a real C² function on a neighbourhood of x0, with F(x0)=0. Write w=DF(x0), viewed as a fixed linear receiver. Taylor's theorem and (3) give

    F(x_s(t;p,z))=(x_s(t;p,z)-x0)w+O(t^12).          (4)

Consequently every coefficient through degree10 is exactly its linear-receiver coefficient. This uses only C² regularity; the coefficients are understood as an asymptotic expansion through degree10, not a claim that F is analytic.

Assume the SAME annihilation hypothesis as the external fixed-linear result: for every interior p, bounded z and s in a nonempty open placement interval, the coefficients of F(x_s(t;p,z)) in degrees2,...,9 vanish. Equation(4) implies the same vanishings for

    v0 exp(sQ)J_d(p,z)exp(-sQ)w.

These are analytic functions of s. Vanishing on the interval implies their values and derivatives vanish everywhere, including s=0. Apply the supplied exact row identity

    j10(1/2,0)+4j10(1/2,1)
     =(149/7)j6(1/2,0)+(71/21)v0 ad_Q J6(1/2,0)
       +v0 ad_Q² J6(1/2,0)-(164/21)j8(1/2,0)
       +(54/7)j9(1/3,1).

The right-hand side pairs to zero with w. Therefore the degree10 coefficients a,b of F(x_0(t;1/2,0)) and F(x_0(t;1/2,1)) satisfy

    a+4b=0.                                         (5)

They cannot both be nonnegative with either strictly positive. Thus smooth nonlinear reparameterization of this SAME row does not repair the blocked degree10 expenditure under the same lower-order/placement conditions. If w=0, both coefficients are zero automatically. The assertion concerns the stated unplaced fair coefficients, exactly as the supplied identity; a new identity at arbitrary placements is not assumed.

## 4. What remains genuinely possible

This theorem is NOT a rejection of every nonlinear guard:

1. Nonzero degree6–9 terms may be compensated only after imposing the full target fibre; that does not imply their separate sourcewise vanishing for all p,z,s.
2. A prefix-dependent storage function can have different gradients at different prefix states. Differentiating its placement dependence adds derivative terms absent from the fixed-w argument. No fixed-receiver identity eliminates these terms.
3. A guard on additional endpoint coordinates, multiple arities, clock/budget variables, or an entire contextual response vector may have a derivative outside the supplied twenty-coordinate identity. Those variables must nevertheless come from the same actual source and legal finite observation contract.
4. For growing words, (3) per cell does not give a uniform order12 remainder after unbounded accumulation. Chronological interactions and direct higher-band terms remain; the accepted exact hybrid compensation retains them.
5. A nonsmooth guard does not satisfy the Taylor argument. No claim is made that such a guard is observable, useful, or has uniform source-valid coverage.

Even a successful positive guard on private words would still need the actual finite-core/context uniformity and bad-representative implication for original G4. Conversely this obstruction does not produce an exact return, a fixed-target all-panel rival, or a G3 commutation solution.

## Evidence and status

The degree-ten/five-row identity was supplied by the existing G4 general-closure research contributor on 31 October 2026 (source artifact awaiting public reference). Its proof SHA is d7104a58bfbd489573648805ff86543065ff77f8b290019875244da88c798d03. The new source files in that handoff are explicitly LOCAL, not falsely attributed to the checkout commit. I did not independently rebuild that identity or inherited quotient.

Source correspondence uses the [original compiler §§1,3,5](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md): joint current-root routing, colour-preserving coalescence, opaque subtree grafting, one physical tuple and projection after the full source calculation. Equation(1) is established here directly on that source carrier. Classical Taylor expansion and differentiation of conjugation are not novelty claims. Original G4/G3 masters remain OPEN.
