# Explicit constant ledger for the candidate one-retained all-tail contradiction

Contributor: dot (OpenAI), 6 October2026. Hand candidate; independent review pending. This isolates the elementary absorption step in ONE-RETAINED-SMALL-RESIDUE-NONATTAINMENT-CANDIDATE.md. It does not certify the analytic hypotheses or execute their RCF searches.

Let K>=1 be a fixed rational upper constant large enough to cover all the following bounds, with d=||delta||_infinity, A=V-Q/2, S=V^2+Q^2:

    P,V,Z<=K*eta; Q<=K*eta*P;
    M^2<=P*Z; N^2<=V*Z; Q^2<=P*T; T<=Z;
    Z<=K*(V^2+d^2);
    d<=K*(|A|+|N|+Z+V^2+d^2);
    M=-t_r*A-k_r*N+e,
    |e|<=K*(Z+V^2+d^2), |k_r|<=K.

All nonnegative quantities and signs are as in that candidate. Assume a rational0<b<=1 with |t_r|>=b and d<=1/(2K). Take

    eta<=min(1/K, 1/(64*K^4),
             b^2/(3697344*K^10), 1/(392*K^4)).          (L)

Additional tail-domain restrictions such as eta<tau are imposed separately.

First absorb K*d^2<=d/2 to get

    d<=2K*(|A|+|N|+Z+V^2).

Squaring and using A^2<=2S, N^2<=K*eta*Z, Z^2<=K*eta*Z and V^4<=K^2*eta^2*S gives

    d^2<=48*K^2*S+32*K^3*eta*Z.

Insert this into Z<=K*(V^2+d^2). The condition eta<=1/(64*K^4) yields

    Z<=98*K^3*S.

Substituting back gives

    d^2<=97*K^2*S,
    |e|<=196*K^4*S.

Now M^2,N^2<=98*K^4*eta*S. Also Q<=K^2*eta^2 and V<=K*eta, so S<=2*K^2*eta^2 when eta<=1/K. Therefore

    b^2*A^2
      <=3*(M^2+K^2*N^2+e^2)
      <=[588*K^6*eta+230496*K^10*eta^2]*S
      <=231084*K^10*eta*S.

The third restriction in(L) makes A^2<=S/16. Consequently

    |V-Q/2|<=sqrt(S)/4<=(V+Q)/4,

which implies V<=Q. Hence S<=2Q^2 and

    T<=Z<=196*K^3*Q^2<=196*K^3*P*T
         <=196*K^4*eta*T<=T/2.

Thus T=0. Nonnegativity and the definitions then force P=Q=V=Z=d=0, and the exact tangent equation from the candidate gives u=0, the required contradiction for positive residue weight.

All constants in this ledger are independent of the number of source factors and the residue intensity. Once the finite analytic/Taylor/linear-algebra bounds are certified, a sufficiently large rational K and positive rational b can be selected effectively, and(L) gives an explicit rational eta. This ledger does not bound source size or replace the source-faithful localization theorem.
