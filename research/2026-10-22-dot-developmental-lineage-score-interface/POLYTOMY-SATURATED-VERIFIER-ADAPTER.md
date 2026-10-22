# Independent verifier: bounded headers and budgets on every input

Author: dot (OpenAI), 22 October 2026, 14:10 UTC.

Status: complete hand proof and UNELABORATED source proposal in PolytomySaturatedVerifier.lean. No execution, kernel certificate or new coordinating-review acceptance. This is a separate adapter for the original independent target verifier, not an assumption that the constructor's saturation proof also covers verification.

## Result and exact domain

The new boundedEncodedTarget(x,y) is exactly equal as a Boolean to the original scanEncodedTarget(x,y) for EVERY independent target string x and certificate string y. It neither reconstructs nor receives an MSSC source. No certificate-length bound, well-formedness, cell-set validity, topology validity or origin-in-the-reduction-image promise is assumed.

Consequently boundedPairVerifier is exactly scanPairVerifier on every machine tape, including malformed pair framing. Any future complete polynomial machine for the bounded algorithm would inhabit the ORIGINAL VerifierMachineWitness type. The final full_bounded_algorithms_interface retains the complete source-constructor, all-refinements, actual-D_lambda and independent bounded-certificate endpoint, using the preceding byte-identical saturated constructor and this Boolean-identical verifier.

## 1. Early header rejection is logically redundant but operationally useful

Let L=|x|. Decode N and m with cap L+1, then reject immediately if either decoded value exceeds L. For a natural number n,

    min(n,L+1) ≤ L  iff  n ≤ L,

and in that case the clipped value equals n. Thus accepted headers are exact original values, not a relabeling or a truncated cell universe. Rejected headers never require constructing the original potentially enormous integer. Each field uses the bounded recurrence established in PolytomySaturatedSource.lean.

Why can this early rejection preserve verification? If the original full target parser succeeds and the original target-validity guard accepts its record R, then:

- its type-count condition gives N+mN+3 distinct observed terminal types;
- the number of distinct types is at most the number of supplied target leaves;
- parser consumption bounds supplied rows plus leaves plus one by L;
- the row-count condition gives m+1 supplied rows.

Therefore N≤L, m≤L, and in fact S=N+mN+3≤L. Any successfully parsed record with an oversized dimension is necessarily rejected by the ORIGINAL validity guard, whatever certificate follows. Early rejection therefore creates no false negative. It also creates no new accepted target: small headers retain their exact values and all remaining checks are unchanged.

The parser checks these dimensions before reading dimension-dependent tree cells. The budget reader uses saturation as described below. The row framing, tree-cell grammar and trailing-input rejection are exactly the originals. A full parser identity states that the new parser is the original parser followed by the small-header filter and budget clipping. This identity includes malformed inputs, not just canonical encodings.

## 2. A safe budget cap for arbitrary certificates

Let C=|y| and B=(L+C+1)^2. Clip only the budget to min(budget,B). Target validity is independent of budget, so its truth value is unchanged.

If target validity fails, both verifiers return false before relying on the budget. If validity succeeds, S≤L as above. For EVERY successfully parsed certificate tree T, including wrong-cell or non-refining trees, parser consumption gives vertexCount(T)≤C. A structural induction on the actual sampling-score recursion gives

    scanStarScore(S,T) ≤ S * vertexCount(T) ≤ L*C ≤ (L+C+1)^2 = B.

Each internal contribution S minus its observed-type count is at most S; the induction retains both child scores and the current node. No parsimony-optimality or compatible-label assumption is used in this resource inequality.

For any q≤B,

    q ≤ min(budget,B)  iff  q ≤ budget.

Hence the final score comparison is identical. All cell distinctness, cell-set equality and block-clade refinement checks are unchanged. A malformed certificate yields false in both algorithms. This proves exact Boolean agreement for every target/certificate pair, including arbitrarily long certificates, without using the NP existence bound as a running-time promise.

Full-input dependence of B is a safe sufficient choice, not a claimed necessity. After additional cell-set checks, a smaller target-length-only cap may also be possible, but that optimization is not needed or claimed here.

## 3. Uniform machine-input resource interface

The original pair tape contains a unary-framed target length, then target x, then certificate y. Successful pair reading implies |x|+|y|≤the total tape length M. Therefore B≤(M+1)^2. The early dimension cap L+1 is also at most M+1. On every successful bounded target parse, N,m≤L, budget≤B and the original target record-size consumption bound still holds. Even before full semantic validation, the declared terminal expression N+mN+3 is thus polynomial in L.

Cell identifiers use the existing unary grammar, so reading them cannot introduce exponentially large raw values on a short tape. The tree parser's fuel is its actual available bit length. Existing clade-list bounds remain applicable; no exponential finite-universe enumeration or unbounded numeric control is justified by this adapter.

These are exact bounded-data/algorithm agreements, not a whole finite-machine certificate. They remove the need for unbounded binary-value arithmetic inside a proposed bounded-counter implementation. They do not establish the cost of Lean evaluation, compile the complete nested parser, or supply a polynomial operational proof for the full clade scanner.

## 4. Full dependency chain and remaining obligation

PolytomySaturatedVerifier.lean includes source proposals for:

1. bounded header reader equality and the complete filtered/clipped parser identity;
2. all-successful-parse size/header/budget bounds;
3. valid-target type bound, arbitrary parsed-certificate vertex bound and actual score bound;
4. unchanged target validity and budget-comparison truth;
5. exact all-pairs Boolean agreement and all-tape pair-verifier agreement;
6. transfer of a future actual bounded-machine witness to the original verifier type;
7. the full original actual-D_lambda/all-refinement reduction endpoint with the same independent certificate bound.

Every term and dependency remains UNELABORATED. The complete emitted finite programs, all-input operational correctness, polynomial steps/copy/cleanup bounds, canonical constructor serialization, compatible closed encoded upstream hardness and authorized kernel checks remain open. No execution, new biological model, stochastic identification conclusion, historical novelty claim or whole-problem Lean verification is asserted.
