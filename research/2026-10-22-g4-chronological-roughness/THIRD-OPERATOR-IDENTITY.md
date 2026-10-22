# Direct labelled-forest proof of the third-order operator identity

22 October 2026. dot (OpenAI-assisted research), prepared for Nolan. Hand derivation for independent review; no new execution.

## Statement and source convention

On the complete labelled rooted-forest source with r current opaque roots, independently assign fair signs to those roots. Write H=G_left+G_right and D=G_left-G_right for the two ordinary within-arm coalescent generators, with the assigned colour inherited after each merger. Let Q be the ordinary generator on all current roots, with rate one per unordered pair. Matrices act on row distributions; their diagonal entries are minus the outgoing rates.

For physical arm durations 2k t^2 +/- A t^3, pair normalization J=B exp(-cQ), c=-log b2(B), has the coefficient

    [t^6]J=k^3 U3+A^2 V3,
    U3=(4/3)E[H^3]+Q^2/2-Q^3/6,
    V3=(1/2)E[D^2]+Q/4.                                   (1)

The claim is the FULL OPERATOR identity

    V3=-(3/4)U3.                                          (2)

In fact, from any forest with r current roots, the nonzero U3 entries are:

- diagonal: -binom(r,3);
- each specified one-pair merger: (r-2)/2;
- each specified rooted triple (one chosen cherry then attachment of the third root): -1/6.

All two-disjoint-pair and three-merger outputs have coefficient zero. Existing subtrees are opaque and are grafted into each resulting tree, so these statements cover arbitrary incoming forest rows and all original labels. No exchangeable quotient or selected covector is used in the proof.

## Why (1) is the actual normalized coefficient

One has E[H]=Q/2 and E[H^2]=(Q^2-Q)/4. For the latter identity, two off-diagonal mergers impose two independent equality constraints, giving probability 1/4. For a specified one-merger output the conditional diagonal rates before and after have expectations lambda_r/2+1/2 and lambda_(r-1)/2; the resulting coefficient is -(lambda_r+lambda_(r-1)+1)/4, exactly the coefficient of (Q^2-Q)/4. Row sums determine the diagonal.

For a fixed assignment H and D commute because the arm generators act on disjoint root sets. Hence B=E exp(2kt^2 H+At^3 D). The fair-sign symmetry removes odd powers of A. Also c=kt^2-k^2t^4/2-A^2t^6/4+O(t^8). Multiplication by exp(-cQ), using the two preceding identities, gives (1) directly.

## Two-merger outputs

A specified rooted triple has one prescribed two-merger path. In D^2, all three participating colours must agree; this has probability 1/4, and the product of the two signed rates is one. Thus E[D^2] contributes 1/4 and V3 contributes 1/8.

For H^3 with that two-merger path, the extra factor is one diagonal step. Put Lambda=lambda_r+lambda_(r-1)+lambda_(r-2). Conditional on the required triple being monochromatic, the expected H rates at the three stages sum to Lambda/2+2. The additional 2 is (binom(3,2)+binom(2,2))/2. Therefore its E[H^3] coefficient is -(Lambda/2+2)/4. Its Q^2 coefficient is one and its Q^3 coefficient is -Lambda. Substitution in (1) gives

    U3=-(Lambda/2+2)/3+1/2+Lambda/6=-1/6.

For two disjoint pairs there are two prescribed orders; analyze either order separately. In D^2 the pair colours are independent fair signs, so their signed-rate product has expectation zero. Conditional on each pair being monochromatic, the three expected H rates sum to Lambda/2+3/2: there are two forced pairs initially, one after the first merger, and none after the second. Thus per order

    U3=-(Lambda/2+3/2)/3+1/2+Lambda/6=0.

This gives (2) for all two-merger outputs.

## Three-merger outputs

Every fixed three-merger history imposes exactly three independent colour-equality constraints on the original current roots: its final blocks have total sum of (block size minus one) equal to three. Its monochromatic probability is 1/8. Consequently the three-off-diagonal part of E[H^3] is exactly Q^3/8. It cancels in U3, since (4/3)(1/8)=1/6. V3 has no three-merger outputs. There are no outputs with more than three mergers in (1).

## One-merger outputs: V3

Fix the merged pair. Conditional on it being monochromatic, write its colour as sigma and let S_other be the sum of the r-2 other independent fair signs. The signed total rate before the merger is

    d_r=(r-1)(2sigma+S_other)/2,

and after it is

    d_(r-1)=(r-2)(sigma+S_other)/2.

The merged pair's signed off-diagonal rate is sigma. Including the probability 1/2 of monochromaticity gives

    E[D^2]_(one pair)=-(1/2)E[sigma(d_r+d_(r-1))]
                    =-(3r-4)/4.

Therefore V3=-(3r-4)/8+1/4=-3(r-2)/8 for this specified pair.

## One-merger outputs: U3

Let m=r-2. Conditional on the pair being monochromatic, let K~Binomial(m,1/2) count other roots of that colour. The H rate after the merger and its decrease at the merger are

    R=binom(K+1,2)+binom(m-K,2)
      =K^2+(1-m)K+(m^2-m)/2,
    D0=K+1.

The H rate before is R+D0. Thus the coefficient of E[H^3] is

    (1/2)E[(R+D0)^2+(R+D0)R+R^2]
      =(1/2)E[3R^2+3RD0+D0^2].

For transparent moment verification, put X=K-m/2. Then R=X^2+X+m^2/4 and D0=X+m/2+1. The exact binomial moments are

    E X=E X^3=0, E X^2=m/4, E X^4=(3m^2-2m)/16.

Consequently

    E R^2=(m^4+2m^3+3m^2+2m)/16,
    E RD0=m(m^2+3m+4)/8,
    E D0^2=(m^2+5m+4)/4,
    E[3R^2+3RD0+D0^2]
       =(3m^4+12m^3+31m^2+50m+16)/16.

Here lambda_r=(m^2+3m+2)/2, lambda_(r-1)=(m^2+m)/2, so

    lambda_r+lambda_(r-1)=(m+1)^2,
    lambda_r^2+lambda_r lambda_(r-1)+lambda_(r-1)^2
       =(3m^4+12m^3+19m^2+14m+4)/4.

Using the Q^2 and Q^3 coefficients in (1) gives

    U3=(2/3)E[3R^2+3RD0+D0^2]
       -(lambda_r+lambda_(r-1))/2
       -(lambda_r^2+lambda_r lambda_(r-1)+lambda_(r-1)^2)/6
      =m/2=(r-2)/2.

This is exactly -4/3 times the V3 coefficient.

## Diagonal and completeness

Every H,D,Q has zero row sum, including the signed D. Their positive powers and the combinations in (1) also have zero row sums. Therefore the established off-diagonal identity forces the diagonal identity. The U3 diagonal is explicitly

    -binom(r,2)(r-2)/2 + [3binom(r,3)]/6=-binom(r,3).

For r=1,2 all listed coefficients vanish, as pair normalization also shows directly. This proves (2) for all r and, in particular, the entire complete cap-six matrix needed by COMPACT-FAIR-NO-RETURN.md.

## Attribution and verification boundary

The physical source expansion and the identity were already present as exact archived finite labelled checks on Oct20; this document supplies a direct hand derivation of the load-bearing identity, not a new source model or rank claim. It has not yet been independently reviewed. No runtime, symbolic algebra tool, numerical test, or compiler was executed in preparing it.

The original complete-forest and pair-normalization conventions are retained from:
https://github.com/Sodelin/Research-Commons/tree/08001e2b298d461cade7bdcd2eda4079b5cd82c3/research/2026-10-21-g4-graded-quotient

This operator identity alone proves neither a positive common zero nor any original G4 master alternative.
