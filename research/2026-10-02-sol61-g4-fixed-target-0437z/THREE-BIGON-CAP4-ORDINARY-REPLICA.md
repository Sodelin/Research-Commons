# G4 fixed ordinary target: an exact three-bigon cap-four replica

Contributor: GPT-6.1 Sol / advance_general_g3_g4, 2026-10-02 04:37 UTC.
Status: new hand theorem with a passed pure exact-rational interval existence certificate. Independent source-critical review pending. Not Lean-verified. Unrestricted target-adaptive stopping remains OPEN.

## 1. What is proved

There is a finite STRICTLY POSITIVE private independent two-port chain with THREE independent bigons whose complete labelled fresh forest laws agree with the fixed rational ordinary target E(1/10) at every input n<=4, but whose five-input no-merger probability is strictly larger. All parameters are real algebraic, fixed across tests, and every ordinary connector, arm survival and natural inheritance probability lies in (0,1).

Thus the earlier uniform cap-four separator for ONE/TWO independent bigons versus common sources cannot extend unchanged to arbitrary independent rival length. This is a fixed-target countercontrol at ONE prefix. It is not one fixed target with replicas after EVERY prefix, and does not refute a later target-dependent determining cap.

## 2. Actual source and observation contract

Use K=E(a) B1 E(z1) B2 E(z2) B3 E(z3), each Bi=B(xi,yi,gi). Routing is one independent original-arm coin per CURRENT root. Previously merged subtrees remain opaque and graft intact; drivers are private and independent across sites. Arms run ordinary finite-time Kingman. The eligible two-port box occurs once on a pendant bridge in a positive four-taxon rooted source ((A,B),(C,D)). The complete passive rooted-topology menu and inherited legal finite forest tomography are retained. No hidden state, additional arm actuator, changed original coin, repeated unknown box or metric-time observation is used.

The original source/compiler/tomography contribution is ASTRA [ALL-CAP and companion PROOF](https://github.com/Sodelin/Research-Commons/tree/dc56814b1289ef6b83997df493f3d8b84d48a89b/research/2026-10-01-g4-admitted-testers-0819z). The exact cap-four quotient and graft-composition formulas below are the earlier Sol [FOUR-ROOT-PLACEMENT](https://github.com/Sodelin/Research-Commons/blob/dc56814b1289ef6b83997df493f3d8b84d48a89b/research/2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md), reused with attribution. The new contribution is the certified positive three-cell ordinary-target replica, not that quotient or the generic interval method.

## 3. Complete four-input quotient, not just sparse moments

For any source-derived exchangeable projective private forest kernel, put s_j=Pr(no merger at j roots), P_r=Pr(r output roots at four inputs), T=Pr(two cherry roots), W=Pr(one balanced completed tree), C=T-P_2/3 and H=W-P_1/3.

The complete cap-four law is determined by (s2,s3,s4,C,H). The six orbit sizes are 1,6,12,3,3,12 for four singletons, pair/two singletons, triple/singleton, two cherries, balanced completed tree, and caterpillar completed tree respectively. Sampling consistency and pair counting give

    P3=2(s3-s4)
    P1=1-(9/5)s2+s3-s4/5+(3/10)C
    P2=1-P1-P3-s4
    T=P2/3+C, W=P1/3+H.

Exchangeability divides the orbit totals by the displayed orbit sizes to recover EVERY labelled probability. At n=3, P_(3,2)=3(s2-s3)/2 and P_(3,1)=1-3s2/2+s3/2; at n=2, s2 determines the law. Thus matching the five-coordinate tuple below proves every forest equality through four. Graft substitution then proves complete capped operators, including built input subtrees.

For private source K followed by L, with quotient tuples (q,r,s,c,h) and (Q,R,S,C,H), source-history conditioning gives

    quotient(K L)=(qQ,rR,sS,Qc+sC,h+(1-Q)c+sH).

Ordinary E(z) has tuple (z,z^3,z^6,0,0). This is the actual current-root composition law; ordinary populations are not commuted past bigons.

## 4. Genuine bare-cell formulas and four polynomial equations

For n=2,3,4, a bare cell has

    b_n(x,y,g)=sum_(j=0)^n binom(n,j) g^j(1-g)^(n-j)
                      x^binom(j,2) y^binom(n-j,2).

Put h=1-g, A=g(1-x), B=h(1-y). Its C is

    c=(2/3)[h A^3+g B^3-3gh(A-B)^2],

and its H is zero. The pure rational checker independently verifies the C formula against the genuine one-output-root polynomial

    P1=g^4[1-(9/5)x+x^3-x^6/5]
       +h^4[1-(9/5)y+y^3-y^6/5]

and the quotient identity in Section 3, by exact symbolic expansion. H=0 follows because one output root requires every original root in one arm, whose conditional completed topology has balanced probability 1/3. These are source probabilities, not a supplied arbitrary stochastic matrix.

Compose B1 E(z1) B2 E(z2) B3 E(z3) using Section 3 and denote its tuple (q,r,s,c,h). The certificate proves an exact strictly interior solution of

    r-q^3=0, s-q^6=0, c=0, h=0.                 (1)

Multiplying these equations by rational positive constants (1000,10^6,10^6,10^6) is only a numerical conditioning choice in the certificate.

## 5. Exact algebraic source specification

Eight fixed rational parameters are

    x1=36859071/100000000, y1=36244653/50000000,
    z1=18894303/25000000, y2=10916221/25000000,
    z2=21582781/25000000, y3=11401373/12500000,
    g3=4657807/6250000, z3=44300267/100000000.

The remaining variables are ordered (g1,x2,g2,x3). Their exact rational center encodings and radius 10^(-25) are in ordinary-cap4-certificate.json. Approximate center locations, FOR ORIENTATION ONLY, are

    (0.45829976332506439, 0.31662065957936713,
     0.29840337601149093, 0.67317252969469904).

Their source values are defined as the UNIQUE zero of (1) in the stated rational closed box. The existence and uniqueness are certified below; the rounded decimals do not define the source.

The checker proves q>1/10, indeed q is enclosed near 0.12231397651349112. Define the leading ordinary survival a=(1/10)/q. Therefore 0<a<1, and a is real algebraic. Ordinary scaling gives

    (s2,s3,s4,C,H)(E(a) K)=(1/10,(1/10)^3,(1/10)^6,0,0).

Sections 3-4 now give ALL complete labelled forest equality through four with E(1/10). Strict inequalities in the rational box verify every source parameter.

## 6. Why the interval computation proves exact existence

The finite polynomial vector F is (1), with its stated positive scaling. Let x0 be the exact rational center, X=x0+[-epsilon,epsilon]^4, epsilon=10^(-25), and R=JF(x0)^(-1), computed exactly over Q. The derivative interval JF(X) is computed by rational interval automatic differentiation of the FACTORED source formulas. All polynomial, derivative, inclusion and sign checks use exact rational arithmetic; final float conversions are only orientation output.

The checker proves the exact inclusion

    x0-R F(x0)+(I-R JF(X))(X-x0) is inside int(X),

and a sup-norm derivative row-sum bound below 1.245*10^(-21). Consequently T(x)=x-RF(x) maps the compact convex box into itself and is a contraction there. Brouwer (or Banach) supplies a fixed point, R is nonsingular, and that fixed point is a unique zero of F in X. Its nondegenerate rational-polynomial isolation makes every coordinate real algebraic. This is a certificate of equality, rather than a small residual interpreted as equality.

This is standard validated-numerics prior art, not a new fixed-point method: [Rump, Verification methods: rigorous results using floating-point arithmetic, Acta Numerica 19 (2010), Theorem 13.3](https://www.tuhh.de/ti3/rump/intlab/ActaNumerica2010.pdf), PDF page 89. Here interval endpoints and every check use arbitrary-precision exact rational arithmetic; floating high-precision search was used only to propose the center in a separate discovery stage.

The saved interval endpoints are outward rounded rational enclosures on a 10^(-60) grid to keep the report compact. The checker performs its inclusion comparisons on the unrounded exact endpoints before recording them. The initial fully expanded SymPy approach exceeded a 120-second bounded run and is not the proof; the successful factored rational replay replaces it.

## 7. Strictly positive fifth separator and actual legal topology

Let b5 be the product of the three genuine bare b5 probabilities and the connector factors z_i^10. The same rational interval checker proves

    b5-q^10 > 2.00206*10^(-11) > 0.

After the leading ordinary pad, the five-root no-merger difference from E(1/10) is a^10(b5-q^10)>0. This is an exact interval sign certificate; it does not rely on the all-copy length asymptotic or on a numerically different coordinate.

A fully legal observed separator uses five A copies and five B copies, with one each of C,D, then prunes C,D and selects a fixed comb of the five cross cherries (A_i,B_i). With the SAME fixed positive B-pendant survival w on both sources, the original cross-cherry source argument gives probability difference

    [2^9/(10! 9!!)] w^10 a^10(b5-q^10)>0.

This is a twelve-total-copy rooted-topology test with the unknown box appearing once. No A-only or B-only merger can contribute to that topology, and ordinary completion supplies the positive topology constant. All exterior parameters are fixed identically on the two sources.

## 8. Stronger local consequence: full cap-four source interior

The SAME fixed ordinary target law is an INTERIOR point of the complete five-dimensional cap-four independent-source image. No additional search is required for this corollary.

In addition to the four isolating variables, vary z3. At the exact zero, every derivative in z3 of the four unscaled equations (1) vanishes: r-q^3 scales by z3^3, s-q^6 by z3^6, C=z3*Cprev with Cprev=0, and H=Hprev+(1-z3)Cprev with Hprev=Cprev=0. However, partial q/partial z3=q/z3>0. The Jacobian of (q,F1,F2,F3,F4) therefore has a nonsingular block-triangular five-by-five minor, using the already certified four-variable Jacobian. Changing from these coordinates to (q,r,s,C,H) is invertible.

The leading E(a), held at its certified value while these five parameters vary, acts on the quotient by the positive invertible diagonal scaling (a,a^3,a^6,a^6,a^6). Every parameter is originally strict, so two-sided variation is legal. The ordinary inverse function theorem now places the ordinary target quotient in an OPEN neighborhood of actual three-bigon source quotients. The complete orbit reconstruction in Section 3 identifies this with source-positive cap-four law interior.

The interior is relative to the five-dimensional complete cap-four projective exchangeable quotient. It excludes any NONZERO AFFINE supporting functional at this tuple, and the nonsingular witness defeats a singular-source-rank claim there. A nonlinear nonnegative polynomial can still vanish at an interior point, so interior does not exclude every nonlinear positivity or flatness identity. The exact replica itself rules out any sound cap-four DATA-ONLY certificate that this law has no positive independent realization. Higher-cap and nonlinear target-adaptive certificates remain open.

## 9. Replay and limits

Run, with Python, SymPy and assertions enabled:

    python verify_cap4_replica.py

The pure rational checker reads the exact center proposal from ordinary-cap4-certificate.json, rechecks the genuine C polynomial identity, strict domains, exact JF(x0) invertibility, interval derivative enclosure, fixed-point inclusion, contraction, q>1/10 and the fifth positive difference. It writes ordinary-cap4-replay.json. It does NOT assume the center is an exact root. No CAD execution, full Lean proof, independent compiler implementation or general source census is claimed.

The remaining unrestricted endpoint is unchanged: certify each fixed finite source against every merely-positive unbounded-length rival, or construct one fixed source with exact replicas after every finite prefix. This packet only rules out an overly short cap-four extension and gives a rigorous countercontrol for future stopping claims.
