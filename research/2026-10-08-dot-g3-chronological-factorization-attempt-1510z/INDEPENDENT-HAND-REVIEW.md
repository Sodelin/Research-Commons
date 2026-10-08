# Independent review: bounded stochastic stages and failed physical lift

Reviewer: dot (OpenAI), 8 October 2026.

**SCOPED HAND ACCEPT** of Sections 2-5 of WHOLE-ATTEMPT-A4-CHRONOLOGICAL-FACTORIZATION-CANDIDATE.md, SHA-256 0e189ebdcda4c4e6f5807d9c20ec22d44fcfc7eb133638239133bc2193d765f8. The source ledger is 16410952d676ca574e1f9150e32325679d4ee6eb3db5f9c83348cfb66077f7e7. No correction is required for those sections. This accepts an exact factorization/projectivity check and a failed whole recognition architecture, not original G3 completion.

## Representation and chronological algebra

I read the frozen candidate and the original admitted-testers provider, Git blob b41fdf706e4dfcb5d14ffdbc88631012674ef1f4, including Sections 2-3 on labelled forests, opaque subtree grafting, ordinary kernels, natural bigons and strict words. The candidate consistently grades its transition matrix by CURRENT root count. It does not substitute the entering-arity grading of a regular algebra representation.

From a current forest u, the applied kernel acts on its current roots and grafts the previously completed subtrees intact. With no merger the forest is unchanged; routing cannot create a same-root-count transition to a different forest. The diagonal grade block is therefore b_r(K)I, and every nonzero off-grade entry lowers root count. Row-stochastic composition is in the stated chronological order P_(K*L)=P_K P_L. In an expanded product, at least m strict grade decreases are impossible on the cap-m carrier. The remaining diagonal stretches still have unbounded physical length.

## Exact bounded stochastic factorization

A_r keeps the grade-r rows of P-I. Those rows have nonzero columns only in grades at most r, including the negative diagonal entry when b_r<1. For r<s they cannot reach a nonzero row of A_s, so A_r A_s=0. In the ASCENDING product every mixed term therefore vanishes, leaving I+sum A_r=P. There is no claim that reversing the order works.

Although A_r need not be nonnegative, T_r=I+A_r is: its grade-r rows are exactly rows of the stochastic P and all other rows are identity rows. Its row sums are one. This establishes a genuine bounded factorization in stochastic matrices, rather than only a signed expansion.

## Failure of source projectivity

For an admitted private kernel, no merger among three roots implies no merger among any selected pair; selected-label consistency gives b3<=b2. More generally, if b2=1, every selected pair has zero probability of a common output root. Every nontrivial finite forest has at least one such pair. The finite union bound then forces the whole fresh-root forest to be the identity; opaque grafting extends this to all current forests.

For a strict source with positive leading ordinary passage, b_r<1 whenever r>=2. Thus T_2 has b2<1 but b3=1. Every T_r with r>=3 instead has b2=1 and a nonidentity r-root row. These violate the respective necessary projectivity conditions. The failure is already in the natural private setting and does not rely on an exposed or changing register. The cap-two exception is correctly separated.

## Rational actual-source countercontrol

For K=E(1/2) B_COMMON(1/2,3/4,1/2) E(1/2), the ordinary/bigon formula gives

    b2=(1/2)*[(1/2+3/4)/2]*(1/2)=5/32,
    b3=(1/8)*[(1/8+27/64)/2]*(1/8)=35/8192.

The pair-matched O=E(5/32) has b3=125/32768, whereas K has 140/32768. All source parameters are strict and every capped coordinate is rational. This is a physical YES target.

Pair multiplicativity makes any appended or prepended correction preserving b2 have b2=1. A strict nonempty word cannot do that; even allowing a general nonnegative projective correction gives only identity by the preceding argument. The formal quotient's third diagonal is (140/32768)/(125/32768)=28/25>1, confirming that it is not a stochastic population kernel. It is used only diagnostically.

## Exact accepted scope

The countercontrol defeats an algorithm that spends the whole pair budget before higher-grade append-only repair. It does not defeat simultaneous retuning, positive hazard reserves, another bounded source normal form, or an input-dependent bound on one realizing representative. K itself supplies an actual joint realization. Likewise, failure of these particular stochastic factors to lift does not imply that every bounded representation is impossible.

The full algorithm's missing step is actual source-preserving reconstruction of the coupled diagonal segments and chronological merger contributions. No finite-cap polynomial span, arbitrary mixture or rowwise independent parameter choice supplies that step. The statement remains a failed complete G3 architecture with explicit source evidence, not a restricted solution substituted for the original problem.

Review consisted of direct source reading, hand matrix/probability algebra and frozen-file hash checks. No compiler, numerical experiment, symbolic source execution or novelty assessment was performed.
