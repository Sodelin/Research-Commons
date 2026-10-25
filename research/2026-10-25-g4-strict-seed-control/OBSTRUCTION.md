# Strict-seed local control: an exact separating cone at the first unmatched cap

25 October 2026. dot (OpenAI-assisted research), prepared for Nolan.
Status: hand derivation for review. No execution, numerical search, formal verification, or novelty claim. This is a restricted obstruction to a proposed induction strategy, not a no-return theorem or resolution of G4.

## 1. Actual source domain

Use finite strict natural INDEPENDENT private serial words, with current-root routing, opaque previously merged subtrees, and one tuple across every entering-root arity. Write K_n(W) for the COMPLETE labelled-forest/graft kernel through cap n, b_r(W) for no merger at arity r, h(W)=-log b_2(W), and E_h for ordinary passage. Positive ordinary connectors are allowed. No source multiplier with negative time is physically used.

A strict seed W0 contains at least one genuine cell. Its hazard h0 is positive. It may be an accepted full cap-five ordinary return. Every claim below concerns actual words or local variations of their physical parameters, not arbitrary stochastic matrices. Parameters vary in an open neighborhood of a strictly interior tuple, so sufficiently small variations preserve the grammar and positivity.

## 2. First scalar obstruction, with arbitrary word count

For n>=3 set

    delta_n(W)=log b_n(W)-lambda_n log b_2(W),
    lambda_n=n(n-1)/2.

The source no-merger product gives delta_n(AB)=delta_n(A)+delta_n(B), and delta_n(E_t)=0 exactly. If delta_n(W0) is nonzero, continuity supplies a physical neighborhood U of W0 on which its sign is fixed. EVERY finite nonempty concatenation of blocks in U, with arbitrary positive ordinary connectors, has the same sign of delta_n. It cannot equal ordinary passage at cap n. There is no bound on the number of blocks needed for this conclusion, and blocks need not individually satisfy the lower-return equations.

In particular, the accepted sufficiently small positive cap-five seed family has negative sixth diagonal defect. Fixing any one such strict seed, repetition, connector adjustment and local block retuning cannot lift it to cap six. A nonordinary submersive endpoint may have an open image wholly inside delta_6<0; a rank condition does not force that image to meet delta_6=0.

This is an exact local semigroup consequence of the already accepted diagonal defect, not a newly computed sixth-order coefficient.

## 3. Full-row obstruction when the next diagonal is already correct

Suppose instead that W0 satisfies complete lower equality through n-1 and b_n(W0)=exp(-lambda_n h0), but has a nonzero full cap-n residual. On the relative physical fibre

    R_n={W: K_(n-1)(W)=E_(h(W)),
             b_n(W)=exp(-lambda_n h(W))},

put v(W)=exp(lambda_n h(W))(K_n(W)-E_(h(W))). The accepted exact projective theorem places v in J_n, the signed kernel space whose lower rows and highest singleton coordinate vanish. It proves J_n^2=0 and, for physical blocks W_i in R_n,

    v(W1...WL)=sum_i T_(s_i)(v(W_i)),
    T_s(v)=exp(lambda_n s) v E_s,

where s_i is the TRUE total suffix hazard after block i, including ordinary connectors. All complete labelled-forest coordinates are retained.

Let Q be the ordinary right-graft generator in this finite faithful action. It is diagonalizable: its diagonal block at r current roots is -lambda_r times identity, transitions strictly decrease root count, and the rates lambda_1,...,lambda_n are distinct. Equivalently the product of Q+lambda_r I over r=1,...,n annihilates Q; on each strictly descending block path the distinct scalar diagonal values give the corresponding divided difference, which vanishes for this polynomial. Thus the spectral projections Pi_r are real polynomials in Q. Since v has no singleton output, its Pi_n component is zero; at least one v0 Pi_r, r<n, is nonzero.

Choose a real linear functional f on that eigenspace with f(v0 Pi_r)>0 and define ell(v)=f(v Pi_r). Then

    ell(T_s(v))=exp((lambda_n-lambda_r)s) ell(v).

Continuity gives a relative physical neighborhood U of W0 in R_n with ell(v(W))>0. For every nonempty finite concatenation of blocks from U and arbitrary positive ordinary connectors,

    ell(v(product))
      =sum_i exp((lambda_n-lambda_r)s_i) ell(v(W_i))>0.

Therefore it cannot be a complete cap-n ordinary return. This is an ACTUAL transported separating functional, not a free-coefficient cone approximation. The conclusion allows arbitrary block counts and arbitrary connector durations. It requires the stated relative-fibre equations for EACH block; it does not exclude coordinated variations which break those equations individually and restore them only in the final product.

## 4. Consequence for a fixed nonempty seed and for fixed exposure

The accepted completed single-taxon normal form implies a genuine nonempty strict word cannot agree with ordinary passage at every cap. Hence every fixed seed has a finite first unmatched cap. At that cap either Section 2 applies or Section 3 applies. Repeating that same seed, with arbitrary ordinary padding, cannot erase its first unmatched full-kernel defect. The relative-neighborhood statement identifies the precise local cone that a proposed blockwise induction must leave.

At one fixed total hazard H there is also a simple domain guard. Shrink the physical neighborhood so h(W)>=h0/2 throughout it. A word made from L such blocks and positive connectors has hazard at least Lh0/2. Thus L<=2H/h0. Arbitrarily many repetitions of a FIXED positive seed cannot be used as cost-free controls at one fixed target. This does not exclude cap-dependent seeds with hazards tending to zero, different nonlocal blocks, or full joint retuning of an expanding word.

## 4a. Fixed-budget strengthening: joint local retuning need not stay in the lower fibre

Fix H>0. The full-row obstruction extends to sufficiently small physical variations of all repeated blocks, even when the INDIVIDUAL varied blocks break the lower-return equations. This uses the fixed budget essentially.

First take every block exactly W0. Write a word with L blocks and L+1 nonnegative ordinary gaps, allowing zero gaps only for the compactness argument. Its normalized cap-n defect has ell value

    sum_(i=1)^L exp((lambda_n-lambda_r)s_i) ell(v0)
       >= L ell(v0)>0.

This statement uses the exact relative-fibre formula only for these unperturbed blocks. With all physical blocks sufficiently near W0, each has hazard at least h0/2. Therefore any admissible total-hazard-at-most-H word has L<=floor(2H/h0). If this integer is zero there are no such words. Otherwise there are finitely many possible positive L. For each, all ordinary gaps lie in the compact box [0,H]^(L+1).

Define on arbitrary nearby actual products P, not necessarily in the lower fibre,

    F(P)=ell(exp(lambda_n h(P)) [K_n(P)-E_(h(P))]),

extending ell linearly to the entire finite signed matrix space. This is continuous in every block parameter and every gap. On the unperturbed repeated-block set just described it is bounded below by ell(v0)>0. Uniform continuity on a compact closed parameter neighborhood of the strict seed, and the finitely many gap boxes, gives ONE smaller physical neighborhood U_H for which F(P)>0 for every such product of nearby blocks. The restriction to total hazard at most H only shrinks this set. Strict positive connectors are included in the compact box used for proof.

Hence no such product is an ordinary cap-n return, even if its final lower equations are restored by coordinated variations which violate them blockwise. This is a local fixed-budget no-lift statement around repetitions of one fixed strict seed, not a prohibition on nonlocal joint source retuning. Adding arbitrarily weak new cells changes the allowed block architecture and is NOT covered by U_H; neither is moving the seed toward a boundary as cap grows. The neighborhood may depend on H and on the seed.

## 4b. Arbitrarily many pair-fine connector cells do not remove this fixed-budget obstruction

The accepted full-forest weak-factor estimate further allows arbitrary finite weak-cell words BETWEEN the strong blocks. Keep the fixed H and a neighborhood U_H from Section 4a, chosen so the collapsed product has F>=a/2, where a=ell(v0)>0. Suppose every genuine cell in each intervening connector word has pair loss at most eta. Replace each entire such word by ordinary passage of the SAME pair hazard. This preserves total hazard and all strong blocks. The collapsed word is covered by Section 4a.

In the faithful stochastic right-graft matrix norm, the inherited weak-factor bound is

    d_n(A,E_(h(A))) <= D_n h(A) sqrt(eta),
    d_n(A,B)=one half ||M_A-M_B||_infinity.

Stochastic telescoping through the complete actual product, including all strong blocks, gives

    d_n(P,P_collapsed)<=D_n H sqrt(eta).

No inverse is applied to a physical source and no error depends on the number of fine cells. Let ||ell|| be the dual norm relative to the matrix infinity norm. Since pair hazards agree exactly,

    |F(P)-F(P_collapsed)|
      <=2 ||ell|| exp(lambda_n H) D_n H sqrt(eta).

For H>0, taking

    sqrt(eta)<a/[4 ||ell|| exp(lambda_n H) D_n H]

forces F(P)>0, so P is not a complete cap-n ordinary return. Section 4b as written uses the full-row hypotheses of Section 3. Section 2 remains the separately proved scalar sign obstruction.

This permits arbitrarily many weak connector cells and arbitrary positive ordinary connectors at bounded total hazard, but retains strong blocks in a fixed neighborhood of W0. It does not permit inserting unbounded ordinary exposure inside each strong block and treating the altered block as unchanged. Non-weak correction blocks, nonlocal source retuning, or cap-dependent seeds remain outside the theorem. This is an interleaved application of the inherited weak-factor and projective estimates, not a new weak-factor theorem.

## 5. What a genuine IFT induction would still need

At a strict actual cap-n ordinary return, a surjective derivative of the complete endpoint map, including its hazard coordinate, would yield a local source chart. Holding the hazard fixed would then permit pivoting onto the remaining independent endpoint coordinates. Positivity would persist locally because the base tuple is strict. This is the legitimate local IFT use, but it starts at an ACTUAL cap-n zero, not merely a cap-(n-1) zero with an unmatched cap-n offset.

The present obstruction shows why repeating a fixed strict lower return and obtaining more tangent directions does not supply that zero. An actual induction must produce blocks outside the separating neighborhood with coupled opposite defects, or a genuinely joint source correction not constrained blockwise, and solve every full labelled-forest equation at the same tuple. It must additionally control total hazard uniformly in cap to yield one fixed ordinary target. None of those suppliers is established here.

This does not refute accepted cap-four/five returns, which already solve coupled equations using varied source factors. It does not assert that every positive word has one common signed charge. The separating functional depends on the chosen seed and first unmatched layer. No higher-cap numerical ladder is warranted by this result alone.

## 6. Attribution and exact prior scope

The main algebra and the known sixth-diagonal defect are inherited from:
https://github.com/Sodelin/Research-Commons/blob/4691d85e8d605bc2adc2ee996f9b025dc6c83a3b/research/2026-10-08-dot-g4-projective-hazard-0807z/EXACT-PROJECTIVE-LAYER-AND-REPAIR-COST-CANDIDATE.md
Its acceptance/status companion:
https://github.com/Sodelin/Research-Commons/blob/4691d85e8d605bc2adc2ee996f9b025dc6c83a3b/research/2026-10-08-dot-g4-projective-hazard-0807z/README.md

The earlier exact failed induction and cap-dependent cofinality costs were read before this derivation:
https://github.com/Sodelin/Research-Commons/blob/8c9a35c38de1e5f2f31b721164eab72b1e155d01/research/2026-10-08-dot-g4-ordinary-cofinality-1402z/ATTEMPT-A4-ORDINARY-COFINALITY-AND-EXTENSION-GAP.md

All-law normal-form acceptance:
https://github.com/Sodelin/Research-Commons/blob/125360b75c9fad294e1ca737834e9bed4117e83e/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-ALL-LAW-COMMONIZATION-ACCEPTANCE.md

The local transported-cone formulation is a deduction from these providers, not a claim that their underlying spectral/projective theory is new. It has not received independent review. Original G4 remains open.
