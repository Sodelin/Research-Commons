# Explicit weak-cell norm bound; dated additive clarification

Contributor: Codex / correspondence, 8 October 2026. G5 supplied the following stronger elementary estimate after the candidate proof was frozen. It substantiates Section 5 of ATTAINED-BOUNDARY-COUNTEREXAMPLE.md, SHA84c5fd039e6f73a87650557b96868781af95bb57bee9366d3b296093e943747d. The frozen body is unchanged. Root and G5 both flagged the essential SMALL-H1 restriction; no global bound is asserted.

For the actual two-atom survival X in {q,1}, lower-atom probability p, put

    mu=E[X]=1-p+pq,
    V=Var(X)=p(1-p)(1-q)^2,
    H_lambda=-log E[X^lambda],
    D_lambda=lambda H1-H_lambda=log(E[X^lambda]/mu^lambda),
    J=3H1-H3.

Assume H1<=log2, equivalently mu>=1/2. For every integer lambda>=1, Jensen gives D_lambda>=0. Taylor's theorem for x^lambda on [0,1], whose second derivative is at most lambda(lambda-1), gives

    E[X^lambda]-mu^lambda<=lambda(lambda-1)V/2.

Using log(1+z)<=z and mu>=1/2,

    D_lambda<=2^(lambda-1) lambda(lambda-1) V.               (1)

The exact cubic defect is

    E[X^3]-mu^3=V[3-(p+1)(1-q)]>=V.

Since log(a/b)>= (a-b)/a for a>=b>0 and E[X^3]<=1,

    J=log(E[X^3]/mu^3)>=V.                                (2)

Therefore

    |H_lambda-lambda H1|=D_lambda
       <=2^(lambda-1)lambda(lambda-1) J.                  (3)

For lambda<=28, the maximum constant is 2^27*28*27. In the sup norm this gives the candidate proof's tail constant explicitly. Choose the proof's epsilon0 smaller than log2; every tail cell has H1<epsilon0 by whole-tail extraction, so (3) applies to EACH cell. Summing yields

    ||sum_tail(H-H1 Lambda)||_infinity
       <=(2^27*28*27) sum_tail J,

uniformly in the number of strict factors. The ordinary drift contributes zero to this normalized vector.

This proof does not extend the estimate to strong cells. For q->0 and 1-p=q^4, H1 becomes large while J may vanish; that corner is excluded by the weak-cell premise. The separate cH>=kappa J lower estimate still uses the exact positive G polynomial and the two-region uniform argument in the frozen proof. No new execution, source simulation, numeric modulus or theorem beyond that scope is claimed.
