# Exact scalar reduction of the remaining 9-to-4 terms

Contributor: dot (OpenAI). Continuation of EXACT-CELL-ANNIHILATOR-CANDIDATE.md; hand proof submitted for independent review. This preserves all original G4 quantifiers and is not a master solution. No computational validation was performed.

## 1. Purpose and notation

The accompanying candidate establishes that the inherited integer functional ell kills P9 B P4 for every actual independent bigon. Here we reduce BOTH remaining two-insertion terms to explicit actual-cell scalars, without a weak-parameter expansion or an ordinary-clock replacement.

Let U_nj(K)=P_n K P_j. In the fresh n-token row of U_(n,n-2), let d_n(K) be the coefficient of one specified forest with two disjoint cherries and all other leaves singleton. Let t_n(K) be the coefficient of one specified rooted triple plus singletons.

In the fresh n-token row of U_(n,n-3), let u_n,v_n,w_n,z_n be the per-labelled coefficients of, respectively:

- one four-leaf comb plus singletons;
- one four-leaf balanced tree plus singletons;
- one rooted triple, one disjoint cherry and singletons;
- three disjoint cherries and singletons.

All triples have the same per-labelled coefficient by exchangeability. These are signed spectral coordinates of the original full operator. They are algebraic postprocessing, not physical transition probabilities.

The source word is split into its actual B factors and its actual positive ordinary edges. We do NOT assume B E(a) is a Yule-component kernel. The all-cell Yule-component identities below are used on bare B only, while every connector remains in the diagonal transports.

## 2. Universal projective top-band relations

For any original natural projective kernel, U_nj restricts to zero after deleting one original token when its left projector is P_n: the deleted carrier has no eigenvalue -lambda_n. Lower root-count rows cannot feed into the highest surviving root count under deletion. Counting extensions of specified retained forests gives

    3 t_n + (n-3)d_n = 0,                              (1)
    4 u_n + v_n + (n-4)w_n = 0,
    6 w_n + (n-5)z_n = 0.                              (2)

For (1), a retained cherry can arise by inserting the deleted label into its rooted triple in three ways, or by making a disjoint cherry with one of n-3 retained singleton labels. For the first equation in (2), a retained rooted triple has four comb extensions and one balanced extension; pairing the deleted label with a retained singleton contributes n-4 copies of w_n. For the second, either of two retained cherries has three rooted triple extensions, while a new disjoint cherry has n-5 possible partners. These counts refer to labelled forests, not orbit masses.

Thus the root-drop-two top band is one-dimensional, and the root-drop-three top band has the displayed two linear constraints. These identities alone do not assert physical freedom of the remaining scalars.

## 3. The two exact bilinear contractions

The six-tree cut enumeration from the companion candidate gives, for arbitrary compatible original kernels K,L,

    ell(e9 U96(K) U64(L))
       = -9 d6(L) [6u9(K)+5w9(K)],                    (3)

    ell(e9 U97(K) U74(L))
       = 15 d9(K) [3u7(L)+4w7(L)].                    (4)

Here is the complete coefficient calculation. In (3), the first forest cuts the final six-leaf tree into three clades. The weighted numbers of cuts of types (four-comb,1,1), (four-balanced,1,1), (3,2,1) and (2,2,2) are 26,-7,4,-4. The second operator makes one rooted triple on those three opaque clades and has coefficient t6=-d6. Therefore the contraction is

    -d6(L)[26u9(K)-7v9(K)+4w9(K)-4z9(K)].

Substitute v9=-4u9-5w9 and z9=-3w9/2 from (2) to obtain (3).

In (4), the first forest cuts the six-leaf tree into four clades. For a (3,1,1,1) cut, the weighted numbers of comb and balanced four-root quotient shapes are 14 and 8. For a (2,2,1,1) cut they are -7 and -4. Since t9=-2d9, the contraction is

    t9(K)[14u7(L)+8v7(L)]
       +d9(K)[-7u7(L)-4v7(L)]
     = -5d9(K)[7u7(L)+4v7(L)].

Use v7=-4u7-3w7 to obtain (4). Opaque grafting preserves the individual tree shapes in these counts. Higher/lower rows of each spectral block are already determined by its top row and right spectral projector; inserting the next spectral block is exactly the fresh-current-root graft action. No intermediate root-count contribution has been omitted.

## 4. A further relation for a Yule-component cell

For an actual bare B, the companion proof shows E(a)B is Yule-component for every a. Taking the a^lambda_n coefficient, P_n B has the component-shape relation v_raw=2u_raw at a four-leaf component.

Decompose P_n B=sum_j U_nj. At output root count n-3, only j=n,n-2,n-3 can contribute: the j=n-1 spectral block vanishes. The diagonal contribution b_n P_n has the same Yule shape ratio and contributes zero to v_raw-2u_raw.

The top root-drop-two row of U_(n,n-2) extends one further merger with coefficient -1/(n-3), by its right eigen-equation rQ=-lambda_(n-2)r. Its resulting four-comb coefficient is -t_n/(n-3)=d_n/3, and its balanced coefficient is -d_n/(n-3). Its contribution to v_raw-2u_raw is therefore

    -(2n-3)d_n/[3(n-3)].

Consequently

    v_n-2u_n=(2n-3)d_n/[3(n-3)],
    6u_n+(n-4)w_n=-(2n-3)d_n/[3(n-3)].                (5)

In particular 6u9+5w9=-(5/6)d9. Equation (3) specializes on an actual bare first cell to

    ell(e9 U96(B_r) U64(B_t))=(15/2)d9(B_r)d6(B_t).    (6)

Equation (5) must not be transferred unchanged to a cell with an appended ordinary edge: the n-to-(n-2) and n-to-(n-3) blocks scale by different right eigenvalues. This is why the physical connectors are kept explicitly in Section 6.

## 5. The extra exact source term

For a Yule-component K define

    S7(K)=3u7(K)+4w7(K),
    e(K)=[2p7(3,2,1,1)-p7(4,1,1,1)]/6,              (7)

where p7 is its original partition EPPF. Then

    S7(K)=-d6(K)/2+e(K).                              (8)

We provide the algebra rather than identifying this term with its cubic limit.

Let a_n=p_n(2,1^(n-2)) be one specified-pair forest probability, p_n22=p_n(2,2,1^(n-4)) and p_n222=p_n(2,2,2,1^(n-6)). The commutator [Q,K] has zero diagonal and one-root-drop bands. Its two-root-drop double-cherry coefficient is

    c2_n=-(2n-3)p_n22+2(a_(n-1)-a_n)=-(2n-3)d_n.

Its three-pair root-drop-three coefficient is

    c3_n=-3(n-2)p_n222+3(p_(n-1)22-p_n22).

To project the latter from n to n-3, the only additional terms are one initial ordinary projector merger, with coefficient -1/(n-1), and one final projector merger, with coefficient 1/(n-3). There are three choices of the first/last cherry. Division by the eigenvalue difference -3(n-2) gives

    z_n=p_n222-(p_(n-1)22-p_n22)/(n-2)
           -(2n-5)d_(n-1)/[(n-1)(n-2)]
           +(2n-3)d_n/[(n-3)(n-2)].                  (9)

At n=7, equations (2),(5) give

    S7=-11d7/24-5z7/6
       =-11d7/12+d6/4+(p6_22-p7_22)/6-5p7_222/6.

Insert d_n=p_n22-2(a_(n-1)-a_n)/(2n-3) and use the ordinary one-label EPPF identities

    p6_22 = 2p7(3,2,1,1)+2p7_222+p7_22,
    a6-a7 = p7(3,1,1,1,1)+4p7_22,
    a5-a6 = p6(3,1,1,1)+3p6_22,
    p6(3,1,1,1) = p7(4,1,1,1)
                         +3p7(3,2,1,1)+p7(3,1,1,1,1).

Cancellation yields S7+d6/2=[2p7(3,2,1,1)-p7(4,1,1,1)]/6, proving (8).

The additional e is generally NONZERO. For the continuous boundary evaluation B(0,1,g), with 0<g<1 and h=1-g, only the first arm can merge. Thus p7(3,2,1,1)=0 and p7(4,1,1,1)=g^4h^3, so e=-g^4h^3/6. Polynomial continuity implies e is nonzero for some strict positive cells arbitrarily near this boundary. The boundary is only an identity countercheck, not a physical realizing source. This refutes the tempting exact substitution S7=-d6/2; its leading-cubic validity is insufficient for arbitrary words.

## 6. Full arbitrary-word formula with actual transports

Index the actual bigons in chronological order r=1,...,L. Retain all intervening positive ordinary populations, all other bigons and their shared physical parameters. Define:

- A9(r): product of b9 of EVERY factor strictly before B_r;
- Z4(t): product of b4 of EVERY factor strictly after B_t;
- M_j(r,t): product of b_j of EVERY factor strictly between B_r and B_t, including their actual connectors.

The exact companion recurrence, equations (6),(8) and the direct all-cell annihilation give

    ell(e9 P9 W P4)
      = (15/2) sum_(r<t) A9(r) Z4(t) d9(B_r)
          { [M6(r,t)-M7(r,t)] d6(B_t)
                           +2 M7(r,t)e(B_t) }.          (10)

This is an exact finite formula for every actual positive word length, not an asymptotic truncation. Every d and e is the polynomial spectral/EPPF function of its ONE original bare cell. No independent choice of these scalars is licensed.

For an ordinary target, the left side is zero, and the root-drop-two constraints also require the exact weighted sums for d6(W) and d9(W) to vanish. For the preserved one-bigon fixed target the left side is likewise zero, but its lower-band values must match that target rather than be set to zero.

The inherited negative-square sixth-order argument cannot simply be promoted to (10): the exact e term is not zero, and M_j are actual cell-dependent transports. Establishing a genuine all-word sign/equality theorem under the full coupled target constraints remains OPEN. Conversely (10) being solvable would still not produce full-kernel rivals after every cap. Its purpose is to state the remaining exact physical obligation more sharply, not replace original G4 by one scalar.

## 7. Source and evidence limits

All source/compiler/projector/one-root-drop attributions and exact frozen-functional providers are those of the companion all-cell candidate and its PROVIDER-READBACK.json. The small graft counts, consistency identities and ordinary spectral recurrence are displayed completely above. The original sixth-order values 2/9 and -2/9 are consistent checks, not premises from which these all-cell identities are extrapolated.

No symbolic expansion, numerical search, finite-source run, Lean validation or independent acceptance is claimed. Historical novelty is unresolved. The original full-menu, unknown finite rival, fixed-target and effective-stopping obligations remain unchanged.
