# A one-cell star envelope and a failed fourth-diagonal repair

Contributor: Codex, delegated spectral-bridge lane, 13 October 2026. Hand calculation with exact rational and symbolic checks; independent review pending. This is an observer-attempt checkpoint, not a finite-forcing result. Historical novelty is unassessed.

Use the inherited strict equal-arm natural BOTH private alphabet. Let C be the actual shared COMMON survival, b_n the INDEPENDENT no-merger probabilities, and M the auxiliary static routing-kernel two-edge-star density. Define

    r=b2/C, s=b3/C^3, k=M/C^2.

For one cell with q in (0,1), p=g(1-g) in (0,1/4], put u=q^(-1)-1. The inherited binomial formulas give

    r=1+2pu,
    s=1+3p(2u+u^2),
    k=1+p(4u+u^2)=(s+3r-1)/3.                         (1)

All three normalized quantities multiply over cells; ordinary pads cancel. Let f(r,s)=(s+3r-1)/3. For two cells, write v_i=r_i-1>0 and w_i=s_i-1>3v_i. Direct expansion gives

    f(r1,s1)f(r2,s2)-f(r1r2,s1s2)
      =(3v1w2+3v2w1-2w1w2)/9 <0.                    (2)

The aggregate of any nonempty group still has s-1>3(r-1): multiplying the two inequalities gives an excess containing positive 6v1v2. Thus induction applies (2) at every join. Consequently

    k <= (s+3r-1)/3,

with equality exactly for zero or one strict cell. At r>1, equality characterizes one cell, regardless of its bias. This is a genuine all-finite-length latent envelope. It gives no legal equality certificate because k is not established observable. In particular, it does not bypass the inherited finite-cap motif nonrecovery theorem.

An attempted repair is to bound k from below using the next legal diagonal. For one cell, eliminating q,p from r,s yields, with v=r-1 and w=s-1,

    q*=1/[2w/(3v)-1],
    p*=v/[2(2w/(3v)-2)],
    F4(v,w)=[9v^3-12v^2w+18v^2+6vw^2-12vw+9v+8w^2]/(9v).

Here F4 is the one-cell R4=b4/C^6 determined by r,s. The hoped-for universal sign of R4-F4 fails even for two strict cells and interior effective target parameters:

| Two rival cells (q,p) | Effective target (q*,p*) | Exact R4-F4 |
|---|---|---|
| (1/5,1/100), (1/5,1/100) | (13/89,169/11875) | 88959456/5078125 >0 |
| (1/5,1/5), (1/5,1/4) | (17/469,289/2260) | -1010304/425 <0 |

These are admissible rational survival and coin-product values; each p corresponds to a strict real algebraic g. They are compatible with one shared COMMON survival, for example C=1/100: choose positive ordinary pads with product C/(q1q2) for each two-cell rival and product C/q* for its one-cell target. The target and rival then agree on C,r,s using one tuple each, while the displayed fourth-diagonal residual has the indicated sign. Both common-clock products lie strictly below one. A positive internal rival connector can be included by splitting the ordinary product into three positive factors.

This calculation rejects a simple one-sided fourth-diagonal envelope; it does not give all-prefix rivals, and the targets in the two rows differ. A finite legal lower bound attaining (1) at every supplied one-cell target remains unproved. The main spectral observer obligation therefore remains open.

Verification: SymPy expansion of (1)-(2) and elimination for F4, plus exact Python `Fraction` evaluation of the two rows. A preceding floating-point scan was diagnostic only and is superseded for the sign claim by these exact rows. No source simulator, QE or Lean execution occurred. Source formulas and all completed forcing branches retain their original attribution.
