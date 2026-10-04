# Ordered independent source closure, reconstruction R1

Contributor: dot (OpenAI), 4 October 2026.

NEW-REVISION STATUS. This is a newly authored reconstruction. It is not an exact recovery of the missing ORDERED-INDEPENDENT-CLOSURE.md, SHA-256 c8793e22d13a110adcde863c48a6c1078af5c063c4a030f673e13cf3ea65a39a. Fresh independent review is pending. No acceptance of the missing file is transferred to this text.

## 1. Actual source and the positive-pair stratum

Fix one INDEPENDENT current-root inheritance mechanism and a finite cap m >= 2. Work with the complete labelled unranked forest tuple at every entering arity up to m. Multiplication is chronological graft convolution: previously formed subtrees are opaque current roots, and later coalescence grafts those whole subtrees. All coordinates at all arities use the SAME physical parameters.

The positive private bridge words are

    E(z) * B(x_1,y_1,g_1) * E(a_1) * ...
         * B(x_L,y_L,g_L) * E(a_L),                 (1)

with all survivals and inheritance weights strictly between zero and one, and any finite L >= 0. This is the original public G4 private-word grammar, Sections 2-5:
https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md .

Let S be the image of these words, and C its Euclidean closure in the finite forest-coordinate space. Put b_j(K) equal to the no-merger probability for j entering roots, b=b_2, and let d be maximum row total variation across the declared arities. Graft convolution is nonexpansive on either side for these stochastic kernels. Each b_j is a continuous multiplicative coordinate.

The cap is fixed throughout. A coordinate at an unobserved larger cap is not silently added. The theorem is not a simultaneous COMMON/INDEPENDENT closure statement or a theorem for arbitrary cross-slot parameter ties.

We use the existing source-specific G6 estimate

    d(B,E(b(B))) <= D_m (1-b(B))^(3/2),              (2)

where

    D_m = 2 binom(m,2)
              [(3/2)binom(m,3)+27binom(m,4)].

It is proved in full labelled forest TV in Section 3.3 of the public source-critical review:
https://github.com/Sodelin/Research-Commons/blob/90beb005d2ebe1b1d1db9d7cb9a9558610a397f9/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md .
This is an inherited input, not a newly claimed weak-bigon theorem. Since B is polynomial in x,y,g, inequality (2) extends continuously to the CLOSED cube [0,1]^3. We only retain closed bigons with b(B)>0.

Projectivity also gives, for every source-closure kernel K,

    d(K,1) <= binom(m,2)(1-b(K)).                   (3)

Indeed a non-singleton forest requires at least one merger between a pair of original entering roots, and each pair has merger probability 1-b(K). In particular a closed bigon with b=1 is the identity at the entire cap. The source-closure identity itself is obtained by letting positive durations tend to zero.

## 2. Definition of a chronological closed-jump presentation

Choose a finite h >= 0. Inside [0,h], choose at most countably many labelled closed intervals

    I_i = [s_i,s_i+c_i],    c_i>0,

whose interiors are pairwise disjoint. At each interval choose one CLOSED-PARAMETER actual independent bigon B_i satisfying

    b(B_i)=exp(-c_i)>0.                             (4)

These intervals encode chronological pair-hazard duration. They do not represent physical chronological times in an original network. Positive lengths imply that two such intervals have an unambiguous order; touching endpoints are allowed. Necessarily sum_i c_i <= h.

To evaluate a finite selected set J, order its intervals from left to right. Replace the entire complement of these selected intervals by ordinary evolution, and insert the corresponding bigons in that order. Explicitly, if J has ordered indices i_1,...,i_r, set

    P_J = E(exp(-s_i1)) * B_i1
          * E(exp(-(s_i2-s_i1-c_i1))) * B_i2 * ...
          * B_ir * E(exp(-(h-s_ir-c_ir))).          (5)

Empty J gives E(exp(-h)); zero gaps mean E(1)=identity. Formula (5) is an ordinary finite stochastic product even when there are infinitely many unselected intervals or their complement is not a union of finitely many intervals. No interchange of noncommuting bigons occurs.

List the intervals in nonincreasing order of c_i, breaking equal lengths arbitrarily. This is possible because sum_i c_i is finite; every positive cutoff leaves only finitely many intervals. If there are finitely many, use the full set once exhausted. Let P_N select the first N intervals. Section 3 proves that P_N converges and that the result is independent of the ordering of equal lengths and of the admissible exhaustive truncation scheme. This limit is the chronological presentation's kernel.

For h=0 there are no positive-length intervals and the kernel is identity. Zero-cost closed bigons may be omitted by (3); they do not introduce an ordering ambiguity.

## 3. Uniform truncation and existence of the chronological limit

For finite selected sets J contained in J', compare P_J' with P_J by replacing each extra bigon B_i, i in J'\J, by its ordinary pair match E(exp(-c_i)). All adjacent ordinary factors then merge to exactly the gaps in (5). Two-sided contraction and (2) give

    d(P_J',P_J) <= D_m sum_(i in J'\J) q_i^(3/2),
    q_i=1-exp(-c_i) <= c_i.                         (6)

If J contains every interval with length greater than eta, this is at most

    D_m sqrt(eta) sum_(i outside J) c_i
        <= D_m h sqrt(eta).                         (7)

The (N+1)-st largest interval has length at most h/(N+1). Therefore, for M>N,

    d(P_M,P_N) <= D_m h sqrt(h/(N+1)).               (8)

The finite-dimensional forest simplex is complete, so the limit exists. Moreover,

    d(K,P_N) <= D_m h sqrt(h/(N+1)).                 (9)

A general exhaustive finite selection also converges to the same K: given eta>0, it eventually contains the finitely many intervals longer than eta; compare it and a sufficiently large ranked selection through their finite union and apply (7) to each side. Let eta tend to zero. Thus neither a tied ranking nor a possibly complicated ordinary complement changes the answer.

Every finite truncation has pair survival exp(-h), by (4), ordinary multiplicativity and the gap lengths in (5). Consequently so does the limit. In particular the presentation always lies in the positive-pair stratum. At m=2, D_m=0 and every truncation is already E(exp(-h)); the formula remains valid.

## 4. Converse: every such presentation is an actual source limit

Fix a finite selected set J. Approximate each closed parameter triple of its B_i by triples in (0,1)^3. Replace each zero ordinary gap in (5), including either endpoint gap, by a small positive duration; keep positive gaps positive. Polynomial continuity of each B and ordinary continuity show that the resulting legal finite positive words converge to P_J. These approximating words need not have pair survival exactly exp(-h); convergence, rather than an exact pair constraint, is what is required for membership in C.

Thus every P_J belongs to C. Since C is closed, its chronological limit K belongs to C. Alternatively, choose a strict positive approximant to P_N within 1/N and combine with (9) to obtain a single explicit convergent sequence of finite positive words.

This proof only approximates closed endpoints and zero gaps. It does not declare them strictly admitted parameters and does not assert that their limit is attained by one finite positive word.

## 5. Extraction from an arbitrary positive-pair source limit

**Theorem.** Every K in C with b(K)>0 has a chronological closed-jump presentation with

    h=-log b(K),

and the truncation estimate (9).

**Proof.** Take actual finite positive words W_n tending to K. Put h_n=-log b(W_n), so h_n tends to h. After discarding a finite prefix, all h_n are bounded by a fixed finite H. If h=0, equation (3) gives K=identity and the empty presentation works. Assume henceforth h>0.

For each W_n, assign an interval to every ordinary or bigon factor by its pair cost: -log b of that factor. Concatenate those intervals in exactly the original factor order, filling [0,h_n]. Ordinary edge E(z) has pair cost -log z. A bigon's interval has length c=-log b(B)>0.

Rank the bigon intervals by nonincreasing length, breaking ties in any deterministic way for that word. For rank r record

    (start s_(n,r), length c_(n,r),
     arm survivals x_(n,r),y_(n,r), coin g_(n,r)).

If the word has fewer than r bigons, append a dummy record with s=h_n, c=0, x=y=1, g=1/2. It represents identity. For every genuine or dummy record,

    0<=s<=s+c<=h_n<=H,
    0<=c_(n,r)<=h_n/r,
    c_(n,r)=-log b(B(x_(n,r),y_(n,r),g_(n,r))).      (10)

The parameter triples lie in a compact cube. Their pair survivals are at least exp(-H), because each factor survival is at least the product survival exp(-h_n). Hence -log b is continuous on the compact region being used. The entire recorded sequence at each fixed rank lies in a compact set.

By successive subsequences and the usual diagonal selection, pass to a subsequence on which every fixed-rank record converges. Write its limit as (s_r,c_r,x_r,y_r,g_r), and B_r=B(x_r,y_r,g_r). Then

    0<=s_r<=s_r+c_r<=h,
    c_1>=c_2>=...>=0,
    c_r<=h/r,
    b(B_r)=exp(-c_r).                               (11)

For any finite number of ranks, their prelimit interval interiors are disjoint, and this property persists for positive-length limiting intervals. More explicitly, for two positive limiting intervals one of the two nonoverlap inequalities holds along an infinite subsequence, so it holds at the limit; overlapping interiors would contradict both inequalities for all sufficiently large n. Also each finite sum of limiting lengths is at most h; thus sum_r c_r<=h.

Discard ranks with c_r=0. By (3) their limiting kernels are identity. The remaining positive intervals and kernels meet exactly the definition in Section 2, including possible endpoint ties or zero-width ordinary gaps. Their ranked order remains nonincreasing in length.

For a fixed N, form W_(n,N) from W_n by retaining its first N ranked bigons and replacing every other bigon by its ordinary pair match. The product W_(n,N) depends only on h_n and these N records, through their chronological order and the ordinary gaps between them.

Its limit is precisely P_N, with zero-length limiting retained factors removed. Here is the boundary justification. Positive-length limiting retained intervals have distinct ordered interiors, so their chronological order is fixed for all sufficiently large n. Retained records with c_r tending to zero have kernels tending to identity by (3), regardless of their position. Replacing those finitely many factors by identity changes the whole product by a quantity tending to zero, by contraction. The remaining ordinary gap lengths, including the endpoint gaps and gaps adjacent to deleted records, converge to the gaps in (5). Continuity of the finitely many remaining factors proves

    W_(n,N) -> P_N.                                 (12)

If only finitely many positive limiting ranks exist, P_N is understood to retain all of them once N is larger than their number. Vanishing ranks do not contribute a nonordinary jump in this limit.

The largest omitted prelimit cost is at most h_n/(N+1), and the sum of all omitted costs is at most h_n. Applying the same replacement argument as (6),

    d(W_n,W_(n,N))
           <=D_m h_n sqrt(h_n/(N+1)).               (13)

Take n to infinity using W_n->K, (12), and h_n->h. This proves (9) for the extracted P_N. Taking N to infinity proves that their chronological limit is exactly K. No mass of infinitely many vanishing jumps has been discarded: (13) proves that their entire limiting effect is the ordinary complement already retained in the pair-hazard coordinate. QED.

Together, Sections 3-5 characterize the whole positive-pair part of C by these ordered countable closed-jump presentations. The representation need not be unique. The proof gives no algorithm for extracting one from an arbitrary algebraic input tuple, and is not a finite-strict-attainment theorem.

## 6. Which positive-pair presentations are nonsingular?

For 2<=j<=m let lambda_j=binom(j,2). For a presentation as above, finite truncation gives exactly

    b_j(P_N) = exp(-lambda_j (h-sum_(i<=N)c_i))
                   product_(i<=N) b_j(B_i).         (14)

The indices in this formula are size ranks; only the scalar diagonal factors commute here. The full forest product remains chronological.

If some retained B_i has b_j(B_i)=0, all sufficiently large truncations have b_j=0, hence so does K. Conversely suppose every retained b_j(B_i)>0. The pair union bound yields

    b_j(B_i)>=1-lambda_j q_i,
    q_i=1-exp(-c_i),    sum_i q_i<=h.               (15)

Since c_i tends to zero, a tail has lambda_j q_i<=1/2. On that tail,

    -log b_j(B_i)<=-log(1-lambda_j q_i)
                       <=2lambda_j q_i.

The tail logarithms are summable, and the finite head has positive product. Therefore product_i b_j(B_i)>0. The ordinary multiplier in (14) tends to exp(-lambda_j(h-sum_i c_i))>0. Thus b_j(K)>0.

The freshly reviewed faithful left-action proof in SOURCE-INTERIOR-RECONSTRUCTION-R1.md, SHA-256 3a989f81c21d535ac93a9aef519d7a70b1bd74663a7c9e3e58274c953d352b69, has diagonal blocks b_r I indexed by ENTERING arity r. Consequently:

**Corollary.** A positive-pair presented kernel K is nonsingular in the full declared forest algebra if and only if every retained jump B_i is nonsingular in that same capped algebra.

The necessity can also be read directly from b_j(K)<=b_j(B_i). This criterion is not implied by pair positivity alone. For example, the closed bigon B(0,0,1/2) has b_2=1/2 but b_3=0. It must be allowed in the positive-pair closure theorem; excluding it would incorrectly remove valid boundary kernels.

For m>=3, the freshly reviewed THREE-LINEAGE-RECONSTRUCTION-R1.md, SHA-256 b76a73adcbc1f52f855ff633571452f4f1a992f1e0e28b3dc59a26e82b6b083c, additionally shows that nonsingularity is equivalent to b_3>0, and that a first diagonal zero cannot arise at a larger arity. This is an optional consequence, not a premise of the extraction theorem.

## 7. Conditional observation-derived pair budgets

A finite budget h is intrinsic to a positive-pair kernel. Turning it into a bound from an OBSERVED profile requires an actually supplied event.

Suppose a private natural bridge slot has a proper descendant set containing k>=2 sampled copies, and a supplied full rooted-topology row contains an outside copy. Choose a rooted caterpillar event T whose restriction to these copies forbids every merger among the k descendants before they join the outside ancestry. Any earlier descendant-only merger would create an opaque rooted clade that later grafting cannot erase. Fresh natural randomness in the unmarked slot then gives

    p_T=Pr(T) <= b_k(K) <= b_2(K).                  (16)

Only if the supplied p_T is strictly positive may one infer

    h=-log b_2(K) <= -log p_T < infinity.            (17)

Caps zero or one carry no pair information and are the trivial capped identity interface. A pendant slot carrying only one supplied copy cannot be assigned a data-derived b_2 floor. If p_T=0, (16) gives no finite logarithmic budget. An arbitrary coarsening need not supply T, and a positive coarse outcome does not replace it. The slot must use the same natural kernel in the relevant rows; its own forced intervention is a different conditional kernel.

The original uncoarsened all-taxa fixed-allocation branch may supply such a row. Across differing allocations, any use of a higher-cap nonsingularity conclusion requires the stated observation/source coverage; a pair floor by itself does not exclude the B(0,0,1/2) example. The three-lineage reconstruction gives a separate sufficient higher-cap floor when a genuine k>=3 event is supplied.

## 8. Exact boundary and remaining master obligations

This is a source-faithful positive-pair closure representation at one fixed mechanism and finite cap. Closed arm parameters, endpoint inheritance weights, zero gaps and countably many nonordinary jumps are essential allowed boundary data. The proof handles their chronological ordering and summable small-jump remainder; it does not turn them into one finite strictly positive source.

The b_2=0 stratum is outside this finite-h representation. Its full forest coordinates must be retained by the separately established compactification/clipping argument; it is not a universal ordinary completed-tree law. Limiting core parameters, observation coarsenings, genuine cross-slot ties and alternative retained cores remain part of the original coupled G3 problem.

Even for b_2>0, neither the truncation estimate nor the nonsingularity criterion proves finite strict selection in an observed fibre, computes a single shared realizing word, or supplies a witness-size bound. Approximation can be used only under its actual fixed-mechanism contract; no paired-mode effective promise is introduced here. G3 termination and the distinct fixed-target/all-prefix G4 question remain open.

This newly written proof requires fresh independent review. It is not the missing artifact under a new path, and makes no Lean, empirical, historical-priority or master-recognition claim.

