# Actual positive free-word coding and the two-channel PCP gate

Contributor: dot, G3 recognition lane. 9 October 2026, 15:34 UTC.
Status: hand candidate with exact quotient-arithmetic checks; root review requested. General G3 remains open.

## 1. Direct source construction

Positivity and exchangeability do not erase every word code. Two explicit actual strict INDEPENDENT source words below generate a free binary semigroup already visible in the inherited cap-four quotient. This does not establish a PCP reduction: no finite original menu has been shown to force all competing cores to use these letters.

## 2. Inherited exact quotient

The complete cap-four coordinates b2,b3,b4,C,H obey, for chronological K followed by L,

    C(KL)=b2(L)C(K)+b4(K)C(L),
    H(KL)=H(K)+(1-b2(L))C(K)+b4(K)H(L).

For E(z), b2=z, b4=z^6, C=H=0. Therefore

    F=C/b2, chi=b4/b2,
    F(KL)=F(K)+chi(K)F(L),
    chi(KL)=chi(K)chi(L).                              (1)

The second established affine coordinate is T=C+H:

    T(KL)=T(K)+b4(K)T(L).                              (2)

These are actual current-root forest identities. Provider: `research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-witness-bound/attempt4/JOINT-MODE-FULL-FOREST-GUARD-AUDIT.md`, blob `f5af03bbaea87c6509ba72b03af7452e50fe294a`, Section3, attributing the complete quotient to `FOUR-ROOT-PLACEMENT.md`. Fresh full read at `0459262a23a83f6e0b4bf9b21f6cb77b45d2dc4b`.

## 3. Explicit rational strict letters

Let B be the bare independent bigon with both arm survivals1/2 and inheritance1/2. The inherited routing formula gives

    b2(B)=3/4, b4(B)=81/512, C(B)=1/96, H(B)=0.

Define

    K0=E(1/4) B E(1/2),
    K1=E(1/2) B E(1/4).

Every ordinary, arm and inheritance parameter is strictly interior. Concatenation gives an admitted private word; adjacent positive ordinary populations may be merged by the source semigroup identity. No inverse or zero-duration operation is used.

Exact quotient values are

    b2(K0)=b2(K1)=3/32,
    b4(K0)=b4(K1)=81/134217728,
    C(K0)=1/786432, C(K1)=1/24576,
    F(K0)=1/73728, F(K1)=1/2304,
    chi(K0)=chi(K1)=rho=27/4194304 <1/2.               (3)

These exact two chronological placements and their C values are already explicitly recorded in the accepted `integration/ROOT-FIFTH-G3-EXACT-COMPRESSION-AND-CERTIFICATE-REVIEW.md` in the same 1253z packet (fresh search at commit `b731591582de323ed5dd8591e7978906022e91a6`). Thus the endpoints are inherited, not a new collision. The present additional argument is the elementary all-word injection in Section 4. The difference is chronological placement of the ordinary passages; diagonals agree. The retained Fraction script checks these values using inherited routing and quotient formulas. It is not a full forest simulator.

## 4. All finite binary words are distinguished

For w=i1...iL let K_w=K_i1...K_iL. Then

    chi(K_w)=rho^L,
    F(K_w)=sum_(j=1)^L rho^(j-1)t_(ij),
    t0=1/73728, t1=1/2304.

Different lengths have different chi. For distinct words of the same length, let j be the first differing position and Delta=t1-t0>0. Its contribution has absolute value Delta rho^(j-1), whereas the absolute sum of later differences is at most Delta rho^j/(1-rho), strictly smaller. Thus F differs. The empty word has chi=1. The two actual strict sources therefore generate a free binary semigroup, already distinguished at cap four.

This is an elementary affine coding consequence, not a historical novelty claim. It supplies neither forced factorization by these letters nor arbitrary affine-matrix realizability.

## 5. Exact failure of the immediate two-channel PCP prescription

At a common coding base beta in(0,1), a standard affine encoding of a string u has dilation beta^(length(u)). Suppose a tile-to-source prescription assigns

    chi(K_i)=beta^(length(u_i)),
    b4(K_i)=beta^(length(v_i)).                        (4)

Every actual strict source has b2(K_i)<1. Since b2=b4/chi, (4) implies length(v_i)>length(u_i) for EVERY tile. Summing over any nonempty index word makes the concatenated strings have unequal lengths. This prescribed alphabet cannot represent a PCP instance having a solution.

Multiplying both dilations by the same positive letter clock leaves their ratio unchanged. Different clocks alter the affine word code and require a new exact equivalence proof. Final normalization alone does not undo clocks inserted at intermediate translations.

This rejects only this particular use of the two established cap-four channels. A higher-cap quotient, different code, or language reduction not assigning lengths to these characters remains outside it.

## 6. Missing full original correspondence

A full reduction still needs:

1. Two synchronized source-faithful coding channels realizing the intended word comparison, retaining all extra forest coordinates and physical parameters.
2. One finite original menu for which EVERY fitting source, across all admitted cores and arbitrary fresh words, implies an accepting encoded word.

No second suitably independently controlled quotient has been authenticated here. Two separate private slots cannot be assumed to share one hidden index sequence. Finite protected IDs do not enforce an unbounded fresh alphabet.

The fixed-alphabet pair-budget theorem also remains applicable if the input identifies b2: (3) makes it (3/32)^L, so any positive fixed pair target bounds L. Leaving that coordinate latent avoids this bound but does not supply the missing converse.

Thus actual sources have genuine free-word capacity, but the PCP adapter and original-G3 undecidability remain unproved.

## 7. Attribution and checks

The exact quotient and equal-arm C formula are inherited. The construction lane identified the affine quotient and has a separate reviewed identical-diagonal/opposite-C example; the simpler moving-ordinary-passage pair here does not depend on that newer fixture.

The retained Fraction script was executed. It checks (3) and compares all 511 binary words through length8. The all-length proof is Section4, not the finite computation. No original observation compiler, all-core alphabet test, PFA reduction, QE or Lean build was run.
