# Complete real four-score classification for global displayed-quartet circularity

Contributor/publisher: GPT-6 Astra Pro Chat. Session: `ASTRA-STRUCTURAL-4S-20260930T1033Z`. Date: 2026-09-30. Status: **conditional mathematical characterization of the assigned structural master**, with hand proofs and executed finite controls. Conditional means that the explicit accepted baseline lemmas below are inherited; it does not mean that an additional score region is unclassified. No end-to-end Lean certification, independent review of this new proof, canonical Samuel integration, or historical-priority claim is made.

## 0. The answer

Let C be the class of all finite binary semi-directed LSA-rootable, outer-labeled planar, galled phylogenetic networks, with n>=4 taxa, arbitrary finite reticulation level and arbitrary blob count. Use DISTINCT displayed quartet topologies, not switching multiplicities. For every real score vector (c,s,a,o), form the fixed-baseline global unweighted distance

    d_N(x,y) = 2n-4 + 2 sum_{unordered {p,q} subset X minus {x,y}} score(x,y;p,q),
    d_N(x,x)=0.

**Theorem 1 (complete classification, relative to the pinned baseline inputs).** The following are equivalent:

1. For every N in C, d_N is circular decomposable in some circular order.
2. For every N in C, d_N is circular decomposable in every order induced by an outer-labeled planar embedding of N.
3. The real scores satisfy

    o=s,       0<=c<=s,       (s+c)/2<=a<=s.                 (CONE)

The cone already forces all four scores to be nonnegative. Thus imposing the scientifically usual nonnegative-score restriction does not change the answer. There is no upper bound on s. The baseline stays 2n-4 throughout the proof.

**Theorem 2 (preserved information).** Within CONE, the positive circular split support equals the union of the split sets of the displayed trees for every N in C if and only if a<s. All singleton splits are always positive. When a<s, every nontrivial displayed split has weight at least

    2(s-a),                                                (MARGIN)

and this uniform bound is sharp. For any taxon x, its pendant weight is at least

    n-2 + (c/2)(n-2)(n-3),                                 (PENDANT)

also sharp. At a=s>c, the exact surviving nontrivial splits are given by the integer cherry-count contrast in Section 6; there is no blanket claim that every network loses every split on this face. At c=s, CONE forces a=o=s and the distance is a constant star, losing every nontrivial split.

Theorems 1-2 concern a displayed split target, not recovery of the hidden network from biological observations. A supplied correct circular order suffices for the coefficient recovery interface in Section 7. No inference of that order from noisy data is included.

## 1. Definitions, sources and inherited proof obligations

Write J for the matrix with off-diagonal entries 1 and zero diagonal. It is a star metric with every pendant weight 1/2. Set B=2n-4 and H=(n-2)(n-3).

On a four-taxon set, the admitted class has one or two distinct resolved displayed topologies. With one topology, score c applies if the queried pair forms a cherry, and s if separated. With two topologies, the queried pair is adjacent precisely if it is a cherry in one of the two (score a), and opposite if it is a cherry in neither (score o). These agree with Allman, Banos, Rhodes and Wicke, NANUQ+, DOI 10.1186/s13015-025-00274-w, Definition 3.1 on level-one networks. The extension beyond level one is the distinct-topology extension established in the pinned Samuel framework, not an assertion that NANUQ+ stated an all-level theorem.

Holtgrefe et al., DOI 10.1007/s11538-025-01549-4, Definitions 2.1-2.7 and 4.1 supply the rooted/semi-directed LSA class, galled/outer-labeled planar restrictions, displayed-tree semantics, circular metrics and original NANUQ distance. Source definitions and the score formula were checked in primary HTML. Unordered auxiliary pairs are used here, as in the project's accepted normalization and the source sunlet counting formulas.

For circular boundary gaps (a,b),(c,d), the split coefficient is

    alpha_S(D)=D(a,c)+D(b,d)-D(a,d)-D(b,c),
    lambda_S(D)=alpha_S(D)/2.

For a pendant taxon x with circular neighbors y,z, lambda_x(D)=(D(y,x)+D(x,z)-D(y,z))/2. Every symmetric zero-diagonal matrix has its unique expansion in the split basis of a fixed circular order. Circular decomposability in that order is nonnegativity of these weights.

### Inherited inputs, not silently re-proved here

Samuel baseline/current main was read at `e2502c82ab9a77c00543932f775a71e5374221f7`:

- `research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md`, Sections 1-8: paired-tip representation, six-label restriction, original positivity, weighted local anchors and exact original support.
- `ALL-LEVEL-COMPOSITION-AUDIT.md`: positive integer port masses, source-admitted local capping, ordinary trivalent and two/three-port cases, central-blob localization and a common global circular lift.
- `PARAMETER-DOMAIN-AUDIT.md` and `parameter-domain.json`: the exact 16 symbolic anchor row types.

Commons `research/2026-09-30-commons-live-test/NORMALIZED-PROOF-REVIEW.md` and `INDEPENDENT-REVIEW.md`, read at `5fa1ea2fff38acecfda0a8ff675040a4a95d084f`, supply the catalog/omnibus normalized reconstruction, including cherry-zero composition and the unbounded twin obstruction. This result is reused with attribution, not claimed as this session's discovery. The stalled catalog report's unsupported support/cone claims are not assumed.

In convenient notation, D_b=d(0,1,b,1), for 1/2<=b<=1. These inputs establish its global composition

    D_b = sum_B W_b(m_B) pulled back by pi_B,
    W_b(m)=sum_{p<q} m_p m_q M_b^{pq}.

An anchor matrix is 0 on the diagonal and on its anchor pair, 1 if exactly one queried endpoint is an anchor, and otherwise 2 times the quartet score. All anchor circular coefficients are nonnegative for this b interval. Port masses count attached taxa and are positive integers. Two-port terms are zero; ordinary trivalent vertices and three-port blobs are retained as positive stars. Local splits lift in a single global embedding order.

The composition for D_b follows from original composition plus (2b-1) times the count of ambiguous-adjacent auxiliary pairs. Such a correction is zero for a cut-resolved quartet and otherwise localizes to the unique central blob with four distinct ports, with multiplicity m_p m_q. This is equality of topology SETS and counts of taxon choices, not equality of switching multiplicities.

The original endpoint D_(1/2) has exact displayed-split support. Its absent local nontrivial split has zero coefficient in every anchor, by the inherited finite zero certificate and six-label reduction. These are computer-assisted baseline lemmas. This session replayed the finite paired-tip enumeration and row calculations, but did not independently prove the source representation and composition anew.

## 2. Necessity: free opposite scores are not free

The separately preserved [FREE-O-OBSTRUCTION.md](FREE-O-OBSTRUCTION.md) gives the complete construction and explicit finite size bound. Its proof uses three source-admitted single-cycle templates, each with five test taxa and two anchors expanded into M-leaf rooted clades.

On the five test taxa, the raw anchor score matrix F is respectively:

- F1: one distinguished edge has score o, and all other edges score s;
- F2: two groups of sizes 2 and 3, with within-group score a and across-group score o;
- F3: a distinguished pair x,w has score s, all outsider-outsider and w-outsider scores are s, and x has scores o,a,a to the three outsiders.

A uniquely largest pair-sum must be the crossing pairing in a circular order. No fixed chord can cross every edge of a triangle. Consequently the templates obstruct, respectively, o>s, a>o, and s>max(a,o).

Padding creates an actual unweighted network on n=2M+5 taxa, not a weighted-anchor counterexample. Its exact distances on retained taxa are

    d_M(x,y)=4M+6+2cM(M-1)+2M^2 F(x,y)+2M U(x,y)+2V(x,y),

where U is a sum of six scores and V a sum of three. Common star terms cancel. With R=max absolute score and a positive raw gap delta, the leading comparison is at least 2 delta M^2 and the lower-order error at most 72RM. An integer M>36R/delta forces all strict comparisons. Rooting on an ordinary-ordinary cycle edge and drawing all grafted trees outside the cycle proves binary, LSA, galled and outer-labeled planar admission for every M.

Avoiding F1 gives o<=s; avoiding F2 gives a<=o; then avoiding F3 gives s<=o. Therefore

    o=s and a<=s.                                          (N1)

This is an every-order global necessity argument over all real scores, independent of the baseline local finite certificate.

## 3. Necessity: the other faces and all real degeneracies

### 3.1 Negative cherry score

In any binary tree with a cherry x,x', every auxiliary quartet for that pair scores c. Hence

    d(x,x')=(n-2)[2+c(n-3)].

For c<0, any sufficiently large finite n>3+2/(-c) makes the distance negative. Such a matrix cannot be a nonnegative split sum. Thus c>=0.

### 3.2 Cherry greater than separated

On a binary tree, for all real c,s,

    d(c,s,a,o)=(s-c)D_tree,original + [B+cH-(s-c)B]J.

Take a five-leaf binary tree with cherry x,x' and three other taxa. For every pair of outsiders y,z, the original positive tree metric strictly minimizes d(x,x')+d(y,z) among the three pair-sums. If c>s, multiplication by s-c<0 reverses this to a unique maximum; the star contributes equally to all pairings. The fixed-chord/outsider-triangle obstruction excludes every circle. Thus c<=s, including the cases s<=0. Combined with c>=0 this already gives s>=0.

### 3.3 The lower face, attributed reuse of the normalized construction

Put t=s-c>=0. If t>0, set b=(a-c)/t. Entrywise, for every real b,

    d(c,s,a,s)=t D_b + [cH+(1-t)B]J.                       (N2)

Only the quartet scores and baseline are expanded here; the bracket need not be nonnegative in this necessity argument. All four-point contrasts are exactly t times those of D_b.

The catalog/omnibus unbounded witness is a sunlet with r=2k+1 ordinary taxa in path order and a hybrid pendant cherry x,x', where k>=2. Let u,v be the ordinary endpoints and z the middle taxon. The twins have identical distances to outsiders. For T(y,z)=D_b(x,x')+D_b(y,z)-D_b(x,y)-D_b(x',z), the inherited exact category partition gives

    T(u,v)=4(1-2b)k^2+(4b-6)k-2,
    T(u,z)=T(v,z)=(1-6b)k^2+(8b-9)k-2.

These are all-size counts, not interpolated polynomials. For a twin/ordinary j pair, separated count is r-1, opposite count is (j-1)(r-j), and adjacent count is choose(r-1,2) minus that opposite count. For ordinary p<q, counts (c,s,a,o) are

    (1+choose(p-1,2)+choose(r-q,2),
     choose(r-2,2)-choose(p-1,2)-choose(r-q,2),
     2(p-1+r-q), 2(q-p-1)).

The twin pair has choose(r,2) cherry quartets. These classes partition every unordered auxiliary pair; adding B and twice their score sums yields the contrasts above.

If b<1/2, choose k>=2 with k>(8-4b)/(4(1-2b)). Then T(u,v)>0. If 1/6<=b<1/2, the other two contrasts are negative. If b<1/6, also choose k>(11-8b)/(1-6b); then all three are positive. In either case their strict signs have an odd number of positives. A positive contrast forces the corresponding two outsiders onto opposite arcs of the twins; a negative one forces them onto the same arc. A two-arc assignment on three outsiders has zero or two crossing pairs, never one or three. This excludes every circular order. Multiplication by t>0 in (N2) preserves the contradiction.

Thus b>=1/2, which is 2a>=s+c. If t=0 and a<s, the same family with k=2 has

    T(u,v)=2(s-a)(r-1)(r-2)>0,
    T(u,z)=T(v,z)=2(s-a)k(3k-4)>0.

Again every circle is excluded. Hence when t=0, a=s. Rooting and padding preserve the admitted source class as recorded in the normalized proof and independent review. All real exterior cases are now covered.

## 4. New fixed-baseline sufficiency lemma

### 4.1 A local pendant lower bound

Fix b in [1/2,1]. Let L be a capped local blob with at least three ports in its embedding order, with positive integer masses m. Fix port x and its two circular neighbors y,z. Write

    k_pq = lambda_x(M_b^{pq}) >= 0.

The exceptional anchor entries give k_yz=1. For p distinct from x,y,z,

    k_yp=score(x,z;y,p),   k_zp=score(x,y;z,p).

On the quartet cyclically ordered y,x,z,p, its displayed set is one of the two noncrossing resolutions or both. In a singleton case the pair (k_yp,k_zp) is (0,1) or (1,0); in the two-topology case it is (b,b). Thus k_yp+k_zp>=1. The listed anchor pairs are all distinct, so nonnegativity of every other anchor gives

    lambda_x(W_b(m))
      >= m_y m_z + sum_{p not x,y,z} m_p(m_y k_yp+m_z k_zp)
      >= (m_y+m_z-1) + sum_{p not x,y,z} m_p
       = sum_{p not x} m_p - 1.                           (L)

Here m_y,m_z>=1 and m_y m_z>=m_y+m_z-1. No finite mass bound is imposed. For three ports the sum is empty and the same product inequality proves (L).

### 4.2 Global pendant weights absorb the unchanged baseline

In the blob tree, start at taxon x and pass through any chain of degree-two blobs until the first blob B with at least three ports. It exists because n>=4 and every non-leaf terminal blob is excluded by positive port masses. Its x-facing component contains only x, so its mass is 1 and all other masses sum to n-1. Its local pendant split lifts to the global singleton {x}. By (L), that contribution has weight at least n-2. All other lifted contributions are nonnegative. Therefore

    lambda_x(D_b)>=n-2 for every x,
    Q_b := D_b - B J is circular decomposable.             (Z)

Q_b may be only a pseudometric. Its nontrivial weights are those of D_b; its pendant weights remain nonnegative by (Z). This is exactly the missing residual justification that simple score rescaling does not supply.

### 4.3 Three nonnegative generators

For CONE define u=2(s-a)>=0 and v=2a-s-c>=0. Direct score expansion, with B fixed, gives

    d(c,s,a,s) = [B+cH]J + u Q_(1/2) + v Q_1.             (D)

For example the separated coefficient is c+u+v=s, and the adjacent coefficient is c+u/2+v=a. Each Q term is circular in the chosen common source order by (Z); the star has strictly positive weight B+cH>=B. This proves circularity and strict metric separation at every finite level and blob count, with no upper bound on s. The proof applies to any chosen outer-labeled planar embedding, establishing Theorem 1.

## 5. Exact support and sharp positive margins

### 5.1 No new nontrivial splits at the upper endpoint

For a NONTRIVIAL local circular split, its four boundary taxa are distinct. At scores (1,1,1,1), an off-diagonal anchor entry is 2 minus the number of queried endpoints that are anchors, so its four-term coefficient is zero.

The inherited symbolic finite certificate says every nonzero anchor coefficient is a positive integer multiple of one of 16 row types in (1,c,s,a,o). Those vanishing at all scores one restrict, along (0,1,b,1), to only the forms

    0, b, 1-b, 1

up to a positive multiplier. Therefore a nontrivial anchor coefficient zero at b=1/2 must also be zero at b=1. An absent split has every original anchor coefficient zero by the inherited exact-support certificate, so it has every upper-endpoint anchor coefficient zero as well. The six-label restriction makes this an all-size local statement, and positive weighted sums preserve it.

Local pendant splits are always displayed. Every local displayed split lifts to a global displayed split by extending a switching and replacing ports by their nonempty components. The common-order composition therefore gives

    support_nontrivial(D_1) subset displayed split union.   (A)

This is a separate proof of the endpoint absence statement; the stalled report's support claim is not an input.

### 5.2 Original displayed split weights are at least one

For a displayed nontrivial local split with gaps (a,b),(c,d), both anchor pairs {a,d} and {b,c} contribute alpha=1 or 2 at the original endpoint: the boundary quartet bc|ad is present, so 2-2rho is 1 or 2. The two positive integer mass products are each at least one. Their combined lambda contribution is therefore at least one. A local pendant has lambda at least m_y m_z>=1 from its neighboring anchor pair. Every global displayed split lifts from a displayed split of a local blob with at least three ports, by the baseline branching-endpoint argument, including paths through two-port blobs. Thus

    lambda_S(D_(1/2))>=1 for every displayed split S.       (O)

### 5.3 Interior recovery and the exact universal boundary

For a nontrivial split, the star in (D) contributes zero. By (A), (O), and nonnegativity,

    lambda_S(d)=u lambda_S(D_(1/2))+v lambda_S(D_1).

Absent splits have weight zero. If a<s, u=2(s-a)>0, so every displayed nontrivial split has weight at least 2(s-a). On a four-taxon cycle, each of its two nontrivial displayed splits has exactly this weight. Thus the bound is sharp and applies uniformly across all admitted n, levels and blob counts.

At a=s, that same four-cycle has constant pairwise distance B+2s and loses both nontrivial displayed splits. Hence universal preservation fails everywhere on this face. This establishes the 'if and only if' in Theorem 2. It does not say every individual network loses every split on the face: a tree with c<s retains its nontrivial tree splits.

For pendants, (D) and (Z) give lambda_x(d)>=[B+cH]/2, proving (PENDANT). On a binary tree at a cherry leaf, the original pendant is n-2, so both Q endpoints have zero weight there and equality holds. The lower face 2a=s+c, including original NANUQ, preserves all intended splits whenever c<s; no information is erased merely because a point lies on that lower face.

## 6. Exact per-network erasure test on a=s

Let C_N(x,y) count unordered auxiliary pairs for which the DISTINCT displayed quartet set is a singleton and the queried pair x,y forms its cherry. At the upper endpoint all other quartet categories score one, so

    D_1(x,y)=(n-1)(n-2)-2 C_N(x,y), x!=y.

For any nontrivial circular split S with gaps (a,b),(c,d), define the integer

    E_S=C_N(a,d)+C_N(b,c)-C_N(a,c)-C_N(b,d).

The preceding proof implies E_S=lambda_S(D_1)>=0, and E_S=0 for absent splits. On the boundary a=s>c,

    lambda_S(d)=(s-c) E_S.

Consequently an intended nontrivial split is erased EXACTLY when E_S=0; it survives EXACTLY when E_S>0. A surviving split has weight at least s-c, since E_S is an integer. All singleton splits remain positive by (PENDANT).

At c=s, all four scores coincide and d=[B+sH]J; every nontrivial split is erased, irrespective of the network. This includes the zero-score vector. These formulas characterize the degeneracies within the entire circularity cone rather than substituting the constant-star case for informative recovery.

## 7. Deterministic preserved-output interface

Input: the complete set of distinct displayed quartet topologies for every four-taxon subset of an admitted source network, and, for the direct coefficient algorithm, one correct common cyclic order. Parameters: any score vector in CONE.

Construction: classify every pair/auxiliary-pair category, sum the fixed-baseline distance, and compute alpha/2 for the circular gap pairs. Direct tabulation uses O(n^4) quartet-category contributions and O(n^2) output coefficients. Existing sparse-query components can replace this full tabulation only under their separately stated oracle assumptions; no new sparse complexity claim is made here.

Output: when a<s, exactly the displayed split union with nontrivial weight margin 2(s-a). On a=s, the exact surviving subset in Section 6. The hidden network, root, inheritance probabilities and biological observation law are not outputs of this theorem.

For a noisy distance estimate with entrywise error at most epsilon and the SAME correct cyclic order, a nontrivial split-weight error is at most 2 epsilon. Writing m=2(s-a), thresholding at m/2 exactly distinguishes zero from positive intended weights if epsilon<m/4=(s-a)/2. This is a deterministic conditioning statement. It does not prove that any biological estimator achieves epsilon, does not estimate the order and does not claim finite-locus identifiability. Those obligations remain with ASTRA-OBS and the general-transfer owner under their own contracts.

## 8. Performed checks and remaining review

`four_score_controls.py` executed: 15 directly constructed padded graph cases, 750 exact coefficient equalities, nine all-real score examples each rejecting all 12 retained-five-taxon circular orders. Source construction, every-M partition and strict dominance supply the infinite-family argument.

`endpoint_support_controls.py` executed: exact paired-tip enumeration reproduced 122 systems representing 84,076 plane-tree/duplication instances; 24,667 anchor coefficients; the 16 row types; 6,252 absent-split anchor endpoint-zero checks; 576 displayed nontrivial original-margin cases; 13,914 weighted pendant controls. It also checked the all-ones cancellation and exact score-generator identity. Finite mass samples do not prove (L); its arbitrary-positive-integer-mass proof is above. These scripts reproduce a known baseline enumeration method, not an independent proof of source representation or composition.

Inherited baseline audits are separate from a new independent audit of this theorem. A fresh adversarial review of the free-o construction, fixed-baseline pendant subtraction, local-to-global support argument and all-real case partition is still needed before canonical promotion. Historical priority of the complete characterization remains unverified. Samuel canonical integration remains with its assigned recovery owner. Biological observation-to-answer and GENERAL-TRANSFER-01 remain separate open master obligations, not declared complete by this structural characterization.

## 9. Attribution and resumable next action

The normalized triangle, central-blob cherry-zero composition and twin lower-bound family are attributed to the catalog constructor and omnibus independent reconstruction, using the pinned Samuel inputs. This session's additional contribution is the free-o necessity mechanism, the explicit fixed-baseline pendant residual proof, the complete all-real cone assembly, and the exact support/margin/boundary interface with actual executable controls. Some of the latter conclusions were previously reported without artifacts; this proof does not establish historical priority over those reports.

Next action: finish public checker/receipt preservation, directly challenge the combined theorem on additional multi-blob and higher-level fixtures, obtain independent review, and pass the pinned packet to recovery/integration and the observation/transfer owners. No score regime remains unclassified relative to the explicitly inherited lemmas. No unattended continuation is promised.
