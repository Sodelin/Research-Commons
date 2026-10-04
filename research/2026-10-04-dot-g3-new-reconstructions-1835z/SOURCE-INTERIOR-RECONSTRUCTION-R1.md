# Actual-source interior absorption, reconstructed revision R1

Contributor: dot (OpenAI),4 October2026.

RECONSTRUCTION STATUS: this is a NEW exposition written after loss of the former local artifact. It is not a recovered copy of SOURCE-SEMIGROUP-INTERIOR.md, missing SHA-256 bca08c69cb25efcdd2d58c337df7a43a027648898297e50c6ca695539c4e9443. That old hash remains missing. Prior acceptance of the old artifact is not asserted as acceptance of this revision. Fresh independent review is required.

## 1. Scope and public providers

Fix one inheritance mechanism, COMMON or INDEPENDENT, and a finite entering-current-root cap m>=0. Use the actual private, unmarked, two-port bridge-chain grammar. Every population duration is positive and finite, so its survival coordinate lies in(0,1); every natural hybrid weight also lies in(0,1). Different private cells use fresh driving randomness. For INDEPENDENT routing a merged subtree is one CURRENT root, not a new collection of descendant leaves.

A physical word is

    E(z)*B(x1,y1,g1)*E(a1)*...*B(xL,yL,gL)*E(aL),       (1)

with all displayed parameters strict. L=0 is the positive ordinary kernel E(z). Composition merges adjacent ordinary edges using E(a)*E(b)=E(ab), retaining a positive duration. Thus the family S of kernels(1) is a semigroup. The scalar/matrix inverses used below are algebraic devices, never physical source operations.

The source grammar, full labelled forest grafting and ordinary/bigon polynomial formulas are public in the G4 finite-cap tester proof, Sections2-5:
https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md .
Its exact implementation forest_algebra.py has Git blob edec614abba57800e220c3580549014335f0d1c4.

The current original-class normalization/sharpness anchor is:
https://github.com/Sodelin/Research-Commons/blob/0e3d36f4035d61a8ad6ae4dc5000b8cf9e54dc2d/research/2026-10-04-dot-complete-original-g1-1549z/THEOREM.md .
That theorem bounds the decorated reduced core, not the original kernel words. No new G1 conclusion or G3 Lean verification is claimed here.

The retained-core transfer in Section6 is conditional on this actual private-slot grammar and its admitted joint compiler. A declared coarsening stays a coarsening. Fixed/read-only original IDs, retained register variables and original parameter ties are not independently refitted. Calendar or changed observation interfaces require their own admitted compiler; this statement uses the finite unranked forest interface.

## 2. The faithful algebra and the correct invertibility argument

Let F_k be the rooted binary unranked forests on k labelled entering tokens, including F_0 consisting of the empty forest. Put

    A = direct_sum_(k=0)^m R^(F_k),   D=dim_R A=sum_(k=0)^m |F_k|.

For K,L in A, the actual convolution is

    (K*L)_k(w)=sum_(u in F_k) K_k(u)
                 sum_(v in F_|u|) L_|u|(v) 1{graft(u,v)=w}.       (2)

Order current roots by their least original entering label. Graft prior subtrees opaquely into the selected current-root forest. Associativity and the identity 1, whose k component is the all-singleton forest, follow from associative subtree substitution. The same conditioning proves actual serial composition(2).

Use the LEFT regular action T_K(v)=K*v. Then T_K T_L=T_(K*L), and T_K(1)=K proves faithfulness. Index its matrix blocks by the number r of ENTERING TOKEN LABELS in a basis vector of A, not by the number of roots in that basis forest.

If v has only its r component nonzero, formula(2) gives output only in k>=r. On the diagonal block k=r, the intermediate u must have exactly r roots, hence must be the all-singleton forest on those r entering labels. Therefore that block is

    b_r(K) I_(|F_r|),                                 (3)

where b_r(K) is K's r-input no-merger probability. This is independent of the root count of the basis forest on which T_K acts.

Every strict actual word has b_r(K)>0: the event of no coalescence through all of its finitely many positive-duration populations has positive probability, after any positive-probability route assignment. Also b_0=b_1=1. Thus T_K is invertible. In a finite-dimensional unital algebra this makes K a unit: solve K*L=1 using the invertible left action; then T_K T_L=I implies T_L T_K=I, and faithfulness gives L*K=1.

Consequently S lies in the unit group A^x. The unit group is a principal Zariski-open subset of the D-dimensional affine algebra, given by det T_K!=0. Its regular-action representation is faithful. This proof does not substitute the different triangular formula for right multiplication.

## 3. A polynomial family with identity on its boundary

Define the one-bigon family

    F(z,x,y,g,a)=E(z)*B(x,y,g)*E(a),  (z,x,y,g,a) in(0,1)^5.       (4)

Every coordinate is a rational polynomial. Indeed, with lambda_j=binom(j,2), ordinary Kingman forest coordinates are rational linear combinations of the finitely many x^lambda_j. COMMON B is gE(x)+(1-g)E(y). INDEPENDENT B sums the full two-arm forest laws over assignments S of the CURRENT roots, with weight g^|S|(1-g)^(k-|S|), retaining all formed subtrees and labels.

Taking z,x,y,a to1, with g fixed in(0,1), makes(4) tend to the algebraic identity. A product of ell such cells is an actual positive word with ell bigons after merging adjacent ordinary edges.

Conversely every word with L>=1 bigons can be written as a product of L cells(4): split each interior connector into two positive ordinary durations before multiplying the adjacent cells. This is a kernel factorization using E(a)E(b)=E(ab), not an assertion that unmarked degree-two vertices or new observable IDs have been added. An ordinary-only E(q) is in the closure of the one-cell family, by letting the two arm durations tend to zero and choosing z*a=q.

For the algebraic argument, complexify A and work in its unit group. The complex Zariski closure X_ell of the ell-cell image is irreducible: the image of the irreducible complex parameter open set has irreducible closure. The strict real cube gives the same complex closure, since a polynomial vanishing on a real open cube vanishes identically after composition with the polynomial parameter map. Let X_0={1}.

Identity in the one-cell closure gives X_ell subset X_(ell+1). Products obey X_j X_k subset X_(j+k), by regularity of multiplication and density of the corresponding parameter images. Dimensions are at most D. Hence for some N<=D,

    X_N=X_(N+1).                                      (5)

To justify the bound, a proper inclusion between irreducible closed varieties strictly increases dimension. If the first D inclusions all increase dimension, the next cannot; any earlier equality gives a smaller N. This also covers the zero-dimensional identity case.

Equality(5) propagates: multiplication by the dense one-cell family preserves X_N, so every later X_ell equals X_N. In particular H:=X_N=X_D is closed under multiplication and contains1. It is an algebraic GROUP. For any h in H, hH is a closed irreducible subset of H of the same dimension, since left translation is an automorphism of the ambient unit group. Thus hH=H, which implies h^(-1) belongs to H.

The group H is defined over R. It is exactly the Zariski closure in the unit group of all physical words S: every physical word is either a cell product or an ordinary-only boundary limit, and the D-cell image is itself contained in S.

The statement concerns H inside the unit group. Singular stochastic limits in the whole affine forest space have not been placed in a group.

## 4. Positive open patches arbitrarily close to the identity

Let d=dim H. Algebraic groups in characteristic zero are smooth; H(R) is a smooth real manifold of dimension d at its real points, with its possibly different real components kept distinct.

The D-cell polynomial map has Zariski-dense image in H. In characteristic zero its generic differential rank is d: equivalently, a transcendence basis of its coordinate function field has independent differentials. Thus some d-by-d ambient Jacobian minor is a nonzero polynomial in the cell parameters. For d=0 the rank-zero statement is automatic.

Given any relative neighborhood N of1 in H(R), choose a sufficiently small real parameter box with all ordinary/arm survivals near1 and all g values near1/2. Its D-cell images lie in N by continuity and the identity-boundary limit. A nonzero polynomial cannot vanish throughout this open box. Choose a point of full rank there. The submersion theorem supplies a nonempty relatively H(R)-open image patch U, after restricting the parameter neighborhood enough to stay inside the box. Therefore

    for every identity neighborhood N there is a nonempty
    relatively open U subset S intersect N.             (6)

All parameters used in U are strict and finite. The algebraic argument does not claim that S is dense in all real components of H, or that its Euclidean closure equals H(R). It supplies only these genuine positive source patches.

## 5. Relative-interior absorption

Let

    K=closure_(H(R))(S).

This is the NONSINGULAR source-group closure. It may be much smaller than H(R). The full affine stochastic closure can also contain singular points outside this definition.

**Theorem.**

    interior_(H(R))(K) subset S.                        (7)

**Proof.** Take p in that relative interior. Continuity of u mapsto p*u^(-1) gives an identity neighborhood N such that p*N^(-1) is contained in the interior of K. Choose U from(6). The set V=p*U^(-1) is nonempty, relatively open in H(R), and contained in K. Since S is dense in K, V contains some s in S. For some u in U we have s=p*u^(-1), hence p=s*u. Both factors are in the actual semigroup S, so their legal positive words concatenate to a finite positive word for p. QED.

Inversion was used only to locate an open mathematical neighborhood. The resulting witness uses positive source multiplication, never an inverse physical edge. The argument is an existence proof and supplies no input-effective length for s.

## 6. Coupled retained-core consequence and limits

Fix one admitted strict core parameter tuple theta, including its original retained values/ties. Give each of its finitely many independently parameterized private bridge slots its required finite full-forest algebra, semigroup S_j and group closure K_j. Suppose the SAME joint compiler has

    p=Compiler(theta,k_1,...,k_e),

and each k_j is in the relative interior of K_j in its corresponding H_j(R). Theorem(7) provides one finite strict word for every physical slot. Inserting those finitely many words into the SAME legal core, with the SAME theta and reused kernel per physical slot across every row, realizes p by one admitted finite positive original source.

This transfer does not permit independent fits of different response rows, mechanisms, histories or conditional registers. If an enlarged joint interface has its own faithful finite algebra and actual SAME-parameter polynomial generator family satisfying Sections2-4, the argument may be repeated with that algebra's actual dimension. It is not valid simply to keep the single-mode D while independently duplicating marginal families.

A genuine tie between a fresh slot parameter and another slot/core parameter must remain in the joint legal domain; independent slotwise absorption is then not supplied by this corollary. An observed positive coordinate is not a hidden-kernel interior promise. Singular limits, core parameter faces, arbitrary coupled boundary fibres and computability of one realizing witness remain separate.

## 7. Prior and verification status

The algebraic-group stabilization and differential-rank facts are standard algebraic geometry; the submersion and density absorption arguments are classical. The point here is their explicit application to the admitted positive forest-word family with the correct faithful action and legal same-source transfer.

Hrushovski, Ouaknine, Pouly and Worrell, *Polynomial Invariants for Affine Programs*, current arXiv1802.01810v2 (2May2018), provides a broader computable Zariski-closure method for finite rational matrix generators: https://arxiv.org/abs/1802.01810 . Its algebraic-invariant endpoint is not positive semigroup membership. The direct identity-boundary family argument above does not invoke an unproved positive reachability corollary of that work.

Fresh independent review of this reconstructed revision is pending. No old missing-file hash is assigned to this text. No Lean, original G3 termination, finite realizing-source bound, G4 closure or historical-priority claim is made.
