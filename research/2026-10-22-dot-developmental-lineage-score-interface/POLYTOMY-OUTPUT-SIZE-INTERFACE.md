# Total encoded constructor: explicit output-size bound

Author: dot (OpenAI), 22 October 2026, 11:05 UTC.

Status: hand derivation and proposed source-only proof terms in `PolytomyOutputSizeBound.lean`. All source and project dependencies remain unelaborated. No compiler, runtime, finite test or new CI was invoked or used as proof evidence.

## 1. Bound stated for every source bit string

Let L be the source input bit length and put q=L+2. The entire total encoded constructor, including malformed, empty, small and threshold-boundary inputs, has output length at most

    P(L) = 3q^5 + 10q^4 + 32q^3 + 51q^2 + 65q + 41.

The proposed `encodedSourceToTarget_length_bound` states this through `sourceOutputSizeBound`; `sourceOutputSizeBound_polynomial` supplies the displayed expansion. Neither has been elaborated. This is an OUTPUT-LENGTH result, not a constructor running-time theorem.

The existing finite semantic theorem and target witness theorem are retained together in `full_encoded_reduction_with_size`: total source/target decision equivalence under actual D_lambda, output length bounded by P(L), and target certificates bounded by J(2J+3), where J is the produced target input length.

## 2. Numerical and budget bounds

For every parsed and validated nontrivial source input, prior consumption/coverage terms give N,m<=L. The other cases produce one of the two fixed targets, both with N=1,m=2. Thus every output has N,m<=q=L+2, including an empty or malformed input. This avoids assuming that all inputs reach the hard branch.

Write s=N+mN+3. The output budget is at most

    B(N,m) = (m+1)s^2 + mN.

On the hard branch, the existing fixed-cost bound gives C0<=(m+1)s^2, and the threshold is C0+K-N with K<=mN. The subtraction cannot increase it. The fixed yes-target satisfies the same bound by its canonical construction, and the fixed no-target has budget zero. Both B and the subsequent size formula are monotone in N,m and the budget.

## 3. Encoding each component

Binary recursion proves the deliberately loose inequality length(bits(n))<=n, valid also at n=0. Hence the existing length-framed binary numerical encoding has length at most 2n+1. This loose bound is enough because all constructed header values, including the budget, already have explicit polynomial bounds. The codec itself still uses binary numerical payloads, not unary n.

A canonical block has at most s leaves. Its full binary tree has 2l-1 vertices, and each cell payload has length at most m+s+1. Thus one encoded block has length at most

    s(m+s+3).

There are m+1 explicitly enumerated blocks. The three numerical headers cost at most 2N+2m+2budget+3 bits, and the outer block-list count frame costs m+2. Total length is therefore at most

    E(N,m,budget) = 2N + 3m + 2budget + 5
                    + (m+1)s(m+s+3).

The source proof bounds the actual concatenated block encodings by induction on the finite explicit block list. It does not assume a uniformly bounded tree without connecting it to the actual serialized forest.

Monotonicity gives E(N,m,budget)<=E(q,q,B(q,q)). Substituting s=q^2+q+3 yields

    E(q,q,B(q,q))
      = (q+1)(q^2+q+3)(3q^2+4q+12) + 2q^2+5q+5
      = 3q^5+10q^4+32q^3+51q^2+65q+41.

The constant branch is covered uniformly: P(0)=887 is deliberately loose. No empirical evaluation or finite-test certificate is claimed for this arithmetic derivation.

## 4. What this closes, and what it does not

Proposed finite terms now span the full all-refinement objective reduction, independent cell-clade semantics, total source and target bit codecs/validation, all malformed/boundary cases, independent bounded target certificates, and a total encoded constructor output-size bound. The family is the already accepted marked-star hard input restriction with arbitrary solution topologies and actual D_lambda. It is not an arbitrary-DAG verifier or a stochastic-identifiability theorem.

Still missing before formal NP-completeness:

1. A concrete total polynomial-time machine realizing the source-to-target constructor and a concrete total polynomial target verifier, with proofs in one selected cost model. Small output and bounded witnesses do not imply these running-time bounds.
2. A compatible, attributed formal MSSC/X3C hardness theorem and polynomial composition. The earlier external-source audit remains in force; no unlicensed external development was copied, adopted or executed.
3. Authorized elaboration and kernel checking of every dependency and new term. Source inspection can expose API mistakes, but cannot certify a build.
4. Separate formalization of the arbitrary-DAG rational-weight verifier/general-DAG DP, and of a graph-contraction datatype if that representation is required rather than the documented cell-clade convention.

The constructor's semantic definition intentionally avoids an optimization oracle: it parses/validates explicit records, uses the canonical tagged ordering and fixed block combs, computes the fixed score, and emits the target. Existence of minimizing MSSC orders is used only in proofs elsewhere, not as a constructor subroutine. Nevertheless, noncomputable declarations/dependencies and absent machine realization mean that no extracted executable or polynomial-time certificate is claimed.

## 5. Verification status and scope

Pinned read-only source inspection checked the `Nat.binaryRec'` induction hypothesis, `Nat.bit`/`Nat.bit_val`, binary-list equations and finite-list length bounds. The explicit polynomial identity is proposed with the `ring` tactic in source, not reported as a run. A read-only GitHub Actions query at 11:01 UTC found zero associated runs for the preceding target checkpoint c27de15ce3af54cd8da46ab080203679a3c081b2; no CI result from that checkpoint is presented as evidence.

No historical novelty, full formal complexity closure or expansion of an earlier independent review is asserted. The accepted full hand theorem and its scoped review remain the scientific basis; these new terms and interfaces are additive, unverified formalization work.
