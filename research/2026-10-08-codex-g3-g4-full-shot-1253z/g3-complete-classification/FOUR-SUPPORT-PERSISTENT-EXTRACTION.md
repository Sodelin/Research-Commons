# Exact two-persistent-cell extraction near the four-atom endpoint profile

Contributor: Codex G5 lane, 8 October 2026, supporting correspondence's direct universal-alternative counterexample attack. Status: new hand proof submitted for independent review. It does not by itself prove source-boundary membership, an attained-boundary counterexample or a complete G3 theorem. No computation, solver or compiler was executed for this theorem. Frozen publication artifacts remain unchanged; this is a separate new draft.

## 1. Governing prior and exact purpose

The accepted provider INTERIOR-OBSTRUCTION.md in 2026-10-06-dot-g3-common-interior-nonrealizability-0209z (SHA256 ed4caaea43f4965d37378f180a1ee4a787ab726dbb13de40f59c1fb975afc16f), with INTERIOR-REVIEW.md (119c9f70853652ee1b7912a09bbd6ee1da039841a8ee5f69468cfad50af85f70), gives the source-faithful persistent-factor extraction and modal-centering/Khinchin dichotomy. Its original application excludes a non-arithmetic three-point law. The present extension applies the same mechanics twice to a different four-point law and explicitly identifies the two persistent factors.

ATOMIC-AND-CONTROL.md Section 2 contains a stronger general finite-support limit statement. Its submitted status is retained: no independent acceptance of that general theorem or an effective uniform extraction modulus is inferred. The narrower accepted extraction and classical infinitesimal-array theorem suffice below. Sparse endpoint exposure and actual COMMON Bernoulli-product normalization are inherited.

This is the complementary source bridge needed for correspondence's possible counterexample to

    S_alg∩ordinary moment interior ⊂ interior(actual source closure).

The guard computation and deterministic/source-boundary implication belong to correspondence's lane. This note supplies only its global nearby-source extraction premise.

## 2. Statement at the actual source contract

Let μ* be the uniform survival law on

    {1, 1/2, 1/3, 1/6}.

Its duration law ν* is uniform on Z={0,a,b,a+b}, with a=log2, b=log3 and 0<a<b<2a. At cap eight, let m* be its seven nonconstant moments at exponents {1,3,6,10,15,21,28}.

For every finite actual natural unexposed COMMON word, orient each unequal-arm cell toward its larger-survival arm and absorb the positive ordinary gaps/shorter durations into its baseline. Its duration law is exactly

    T=c+∑i di Bi,
    c>0, di>0, pi∈(0,1), independent Bi~Bernoulli(pi).

These are distinct natural hybrid draws, not the independent-current-lineage mechanism or an artificial shared parameter lottery. Equal-arm cells are deterministic and can be absorbed as in the accepted source normalization.

**Theorem.** If the cap-eight moments of a sequence of such words converge to m*, there is a subsequence and two distinct actual cells in each selected word which, after interchanging their indices if necessary, satisfy

    p1→1/2, d1→a;    p2→1/2, d2→b.

Their actual independent nonnegative remainder

    R=c+∑i not in {1,2} di Bi

converges weakly to zero. Consequently

    c+∑i not in {1,2} [−log(1−pi+pi e^(−di))] →0,
    c→0,
    ∑i not in {1,2} pi(1−e^(−di))→0.

There is also a qualitative uniform version. For every ε>0 there is δ>0 such that every actual word whose seven moments are within δ of m* has two distinct cells with the ordered probabilities/durations within ε of these limits, and with both c and the remaining sum of pair losses below ε. This asserts existence of δ, not an effective modulus, numerical δ or computable architecture bound.

## 3. The cap-eight moments force law convergence

In the eight-dimensional sparse polynomial system {1,s,s³,s⁶,s¹⁰,s¹⁵,s²¹,s²⁸}, impose a simple zero at 1 and double zeros at 1/2,1/3,1/6. Seven homogeneous conditions leave a nonzero polynomial. The sparse positive-root bound is seven, so these are all its positive roots with exactly the imposed multiplicities. Its constant coefficient is nonzero, since deleting it would leave at most seven monomials and permit only six positive roots. Choose its sign nonnegative on [0,1]: interior zeros are double, the only remaining zero is at its right endpoint, and the sign is constant away from them in (0,1).

A probability law with m* has zero expectation of this polynomial, hence is supported on its four roots in [0,1]. The four weights are uniquely fixed by generalized Vandermonde independence (already the first four sparse monomials suffice). Thus μ* is its unique representing probability measure.

Any sequence of actual survival laws has weakly convergent subsequences on [0,1]. Moment convergence and the exposing polynomial force every such limit to equal μ*, hence the whole survival-law sequence converges to μ*. The limit has no atom at zero. The extended continuous-mapping theorem for −log therefore gives duration-law convergence T→ν*. The atom at survival 1 causes no difficulty: −log is continuous there and gives duration zero. No unbounded logarithmic-moment convergence is assumed.

## 4. Every two-point factor of ν* is one of the two stated Bernoullis

Suppose ν*=law(d B)*ρ for d>0, B nondegenerate, and a probability law ρ. As both atoms of B have positive weight,

    supp(ρ)⊂Z∩(Z−d),
    supp(ρ)∪(supp(ρ)+d)=Z.

The support is finite and d must be a positive difference of two elements of Z, so d∈{a,b,a+b,b−a}. The four possibilities give:

| Jump d | Z∩(Z−d) | Can its support and translate cover Z? |
|---|---|---|
| a | {0,b} | Yes, both points required |
| b | {0,a} | Yes, both points required |
| a+b | {0} | No, only two total points |
| b−a | {a} | No, only two total points |

The intersections use b≠2a (3≠4) and 2b−a≠a+b (3≠4). Thus d=a or b and ρ is the other two-point law. The two weights at 0 and d are equal in ν*, forcing P(B=1)=1/2; the other two weights force ρ to have weights 1/2,1/2. This fully classifies the needed two-point factor, not arbitrary finite-support convolutions.

The law ν* is not infinitely divisible: a fourth convolution root with two distinct support points would give five distinct support points in its fourth convolution power, whereas a one-point root would give a degenerate law. Similarly a nondegenerate two-point law is not infinitely divisible, since its convolution square would have at least three points. These are elementary support arguments, not a new general probability theorem.

## 5. Apply the accepted extraction twice

For any row-independent nonnegative Bernoulli array converging to a non-infinitely-divisible law, the accepted argument supplies a persistent factor along a subsequence. Otherwise, for every ε>0,

    maxi min(pi,1−pi) 1(di>ε)→0.

Subtracting each summand's more likely atom and splitting the deterministic shift into terms of magnitude at most 1/j gives an independent uniformly infinitesimal triangular array with exactly the same total laws. Classical Khinchin makes the limit infinitely divisible, a contradiction. Therefore there are ε,η>0 and a subsequence with one jump at least ε and probability in [η,1−η]. Nonnegativity and tightness bound that jump above. Extract its jump/probability limits and the independent nonnegative remainder, which is tight because it is dominated by the original total. This produces a genuine nondegenerate Bernoulli convolution factor of the limit.

Apply this argument to T→ν*. Section 4 identifies the first extracted factor as either the a or b fair Bernoulli and the remainder limit as the other fair Bernoulli. The remainder still consists of an actual nonnegative baseline and all the other actual independent Bernoulli cells. Since its two-point limit is not infinitely divisible, apply precisely the same extraction to that array. It yields a second distinct cell converging to the other fair Bernoulli.

The final actual nonnegative remainder is tight. Any of its subsequential limits ρ satisfies

    ν* = law(a Bernoulli(1/2))*law(b Bernoulli(1/2))*ρ.

Taking Laplace transforms, the first two strictly positive transforms cancel with those of ν*, giving the transform of ρ equal to one. Hence ρ=δ0. Every subsequential remainder limit is zero, so the remainder converges weakly to zero along the selected subsequence. This cancellation is a probability-law identity, not a physical inverse or a source operation.

The bounded continuous function e^(−R) therefore has expectation tending to one. Actual independence gives

    −log E[e^(−R)]
      =c+∑tail −log(1−pi+pi e^(−di))→0.

All terms are nonnegative, so c tends to zero. Since −log(1−u)≥u for 0≤u<1, the total tail pair loss also tends to zero. No expectation convergence of R or finite jump-size bound on all omitted cells is asserted; rare large jumps are allowed and are controlled by these exact Laplace quantities.

## 6. Uniform nearby-profile conclusion and exact limits

If the uniform statement failed for some ε>0, choose actual words with moment error below 1/j but with no permitted two-cell extraction satisfying its ε requirements. Sections 3–5 give a subsequence with the two identified actual cells and tail quantities converging as stated. Eventually those words satisfy all requirements, contradicting their choice. This gives δ existentially and covers every actual word, irrespective of size or positivity margin. It does not compute δ or return an algorithm from a prescribed numeric tolerance.

No cell is removed to construct a source in this proof: selected cells and actual independent remainders are analysed in their original source laws. It does not yet prove the nonlinear guard needed for attained-boundary membership. It also does not transport a word-level guard across all alternative original cores; that further bridge must retain the actual original calibration/joint compiler. COMMON protected/exposed coins, synchronized exterior registers, and INDEPENDENT current-lineage kernels are outside this extraction contract.

The added contribution is exactly the two-stage identification and qualitative uniform extraction for this endpoint-exposed four-atom profile, derived from accepted narrower mechanisms. The general submitted finite-support classification is credited but not used as an accepted theorem. Historical novelty is unassessed. Root independent review is requested before this premise is promoted into the proposed universal-alternative counterexample.
