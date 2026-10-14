# G4 full-force attempt: finite diagonal rigidity of the retuned body

Contributor: independent Astra G4 researcher for Nolan, 14 October 2026.

**Status: HAND PROOF PENDING INDEPENDENT REVIEW, with exact arithmetic certificates. Full positive and negative G4 masters remain unproved by this packet.** This pass attacks the full statement, not certificate availability. It proves a restriction needed by the attempted full argument, then records exactly why that argument still does not close.

## 0. Decision brief

For any FIXED FINITE analytic source presentation with the retained bare body B*=B(1/2,1/2,2/3), and any number of additional bare cells tending to the identity kernel, agreement through Taylor order six on private no-merger rows n=2,...,17 forces

    x(epsilon)=1/2+O(epsilon^4),
    y(epsilon)=1/2+O(epsilon^4),
    g(epsilon)=2/3+O(epsilon^4).                         (R)

The number of extra cells is arbitrary; the proof does not enumerate or bound it. Their placements may be on either legal bridge region and may coalesce. Actual sources at positive epsilon retain finite positive exposures and interior coins. Boundary values occur only at the expansion center.

For the rare-coin class with the selected arm tending to survival one, n=2,...,11 already suffice. These are PRIVATE entering-root arities, not new taxa, not a rival-size bound, and not a claimed universal original 17-copy determining certificate.

The main certificate is a 16-by-16 integer determinant with nonzero residue **220962 modulo 1000003**. Separate fraction-free exact and modular algorithms agree. The earlier blind internal-body direction therefore cannot be a cubic-order repair on these matching branches. Ordinary time can still shift between the two sides of the body. The resulting chronological term and the full original-rival coverage are NOT settled.

## 1. The full proof attempted

The original class remains finite binary rooted-LSA, outer-labelled planar and cut-child, with parallel arcs allowed, fixed n_taxa>=4, finite positive natural exposures and interior inheritance weights. INDEPENDENT routes current opaque roots. One graph and tuple serve every experiment. Original IDs, allowed joint programs and final rooted labelled topology observations remain unchanged.

The positive master requires, for EVERY fixed admitted finite T, a FINITE legal INDEPENDENT collection forcing its entire permitted law against EVERY admitted finite rival of UNKNOWN size. The negative master requires ONE fixed strict finite T and an exact inequivalent admitted FINITE rival after EVERY finite full-legal-I prefix, with one shared tuple per rival.

The retained target is T=E(3/4) B(1/2,1/2,2/3) E(1/2) inside its original fixed retained-root exterior. Before/after ordinary bridges are legal insertion sites; its nonbridge gall arms are not new insertion sites.

The full positive argument attempted here was: (i) make exact higher-copy matching constrain internal body retuning; (ii) use that constraint to prove a full two-region chronological equality guard; (iii) prove every hypothetical increasingly fitting original rival sequence enters a covered local presentation and then extract a finite original certificate. Only the scoped implication (i) below is established. Neither (ii) nor (iii) follows from it. The negative route must also respect (R), but no actual exact all-prefix construction is supplied.

## 2. Actual source coordinates and Taylor degree

Let lambda_n=n(n-1)/2. The source's independent no-merger probability is

    b_n(x,y,g)=sum_{k=0}^n binom(n,k) g^k(1-g)^(n-k)
                         x^lambda_k y^lambda_(n-k).

It assigns parents to CURRENT roots, not their descendant leaves. Define the proof coordinate

    Phi_n(x,y,g)=log b_n(x,y,g)-lambda_n log b_2(x,y,g).

Ordinary populations disappear from Phi. Serial no-merger probabilities multiply, so the necessary matching equation is

    Phi_n(theta(epsilon))+sum_i Phi_n(B_i(epsilon))
       =Phi_n(theta*)+O(epsilon^7),                     (1)

where theta*=(1/2,1/2,2/3). Full capped forest equality implies (1). These diagonal equations are NOT asserted sufficient for full equality or silently substituted for the legal observation menu.

The extra-cell count is fixed and finite while epsilon varies, but otherwise unrestricted. All parameters are real analytic at zero and strict for small positive epsilon. Each extra bare cell has b_2(B_i(0))=1. Because

    1-b_2=g^2(1-x)+(1-g)^2(1-y),

its possible centers have both arms one with interior limiting coin, g=0 and y=1, or g=1 and x=1. Unused-arm limits may be anywhere in [0,1]. Such centers are analysis objects, not admitted rivals.

**Taylor-degree lemma.** The coefficient of epsilon^r in Phi_n of any such cell is a polynomial in integer n of degree at most 2r, r>=1. In the rare-coin case the bound improves to max(2,r).

**Proof for interior limiting coins.** Both arms tend to survival one. Expand exp(lambda_k log x+lambda_(n-k) log y). A coefficient of order r has degree at most 2r in k,n. Binomial factorial moments E[(K)_j]=(n)_j g^j preserve the degree bound in n. Substituting analytic g(epsilon) does not increase it. Products in the logarithmic coefficient have total Taylor order r, hence total degree at most 2r. Pair normalization subtracts only a multiple of lambda_n.

**Proof for rare coins.** Orient g(0)=0,y(0)=1. Only k<=r contributes through order r. After factoring out y^lambda_n, a k-term is

    binom(n,k) g^k(1-g)^(n-k) x^lambda_k
       y^(-kn+k(k+1)/2).

The initial g^k costs at least order k. Each additional order from the (1-g) or displayed y-power increases degree in n by at most one; the x-power has k fixed. Hence the remaining order-r coefficient has degree at most r. The logarithm preserves this bound; the removed ordinary log and pair normalization have degree two. Interchanging parents covers g(0)=1. Falling-factorial binomial polynomials vanish for n<k, preserving the coefficient identity at smaller arities. QED.

Finite sums preserve the bound regardless of extra-cell count, order, or placement collisions. A rare-coin center with selected-arm survival strictly below one approaches a positive-duration ordinary factor, NOT the identity, and is not covered by this lemma. Its coefficients can involve exponentials in n.

## 3. The blind internal direction has independent curvature

At theta*, let X_n=(partial_x b_n)/b_n, G_n=(partial_g b_n)/b_n and v=(3/2,1/2,0). The inherited all-arity identity is

    (3/2) partial_x log b_n+(1/2) partial_y log b_n=lambda_n.

Thus D Phi_n[v]=0 for every arity. This is the previously proved infinitesimal blind direction, not an exact collision.

Define integers

    w_(n,k)=binom(n,k) 2^[k(n-k+1)],  S_n=sum_k w_(n,k),
    A_(n,k)=-lambda_n+3lambda_k+lambda_(n-k),
    h_(n,k)=A_(n,k)^2-lambda_n-9lambda_k-lambda_(n-k),
    H_n=(sum_k w_(n,k)h_(n,k))/S_n.                    (2)

Then b_n(theta*)=S_n/(3^n 2^lambda_n). H_n is the second logarithmic derivative along the physical path multiplying the effective leading pad by (1-t), x by (1+3t), and y by (1+t), with g fixed. Its first derivative is zero. For the bare body alone, the second logarithmic derivative is H_n+lambda_n. Its pair response along the bare path is b_2(t)=b_2(0)(1+t), so

    D^2 Phi_n[v,v]=H_n+2lambda_n.                      (3)

The curvature is calculated before projection; it is not discarded.

## 4. Exact finite certificate and theorem

For degree D, take rows n=2,...,D+5 and columns

    S_n n^j, j=0,...,D;
    2 sum_k lambda_k w_(n,k);
    sum_k (3k-2n) w_(n,k);
    sum_k h_(n,k) w_(n,k).                             (4)

Scaling each row by S_n>0 and the G column by 3/2 identifies the corresponding functions as 1,n,...,n^D,X_n,G_n,H_n.

| Degree D | Private arities | Matrix | Determinant mod 1000003 |
|---|---|---|---|
| 6 | 2,...,11 | 10 by 10 | 172637 |
| 12 | 2,...,17 | 16 by 16 | 220962 |

The exact D=6 determinant is

    -3736418308107098903049028309795085948266732943701314840928531041484800.

`check_body_rigidity.py` reconstructs both integer matrices, calculates full exact determinants by fraction-free Bareiss elimination, and separately computes modular determinants and pivots. It checks that the modulus is prime by trial division through its integer square root. Both exact methods agree. No numerical rank tolerance is used.

**Finite body-rigidity theorem.** If (1) holds through order six for n=2,...,17 under Section 2's hypotheses, then theta(epsilon)=theta*+O(epsilon^4). For rare-coin centers, n=2,...,11 suffice.

**Proof.** Suppose a first nonzero internal coefficient a occurs at order k<=3. At that order,

    P_k(n)+D Phi_n[a]=0,

with deg P_k<=2k. By the blind identity, this is a polynomial plus (a_x-3a_y)X_n+a_g G_n. The D=12 independence certificate forces a_x=3a_y and a_g=0, so a=h v for a nonzero real h.

At order 2k, minimality of k makes the sole nonlinear body contribution (h^2/2)D^2 Phi_n[v,v]. The equation is

    P_(2k)(n)+D Phi_n[theta_(2k)]
       +(h^2/2)(H_n+2lambda_n)=0.                     (5)

All polynomial terms have degree <=4k<=12. Independence now forces h^2/2=0, hence h=0 over the reals, a contradiction. Thus no internal coefficient at orders one, two or three is nonzero. For rare coins all polynomial terms in (5) have degree <=max(2,2k)<=6, so the smaller certificate suffices. QED.

This proves a uniform necessary coefficient constraint within the declared presentation class, not a fitted-example result, a bound on cell count, or impossibility of every exact source return.

## 5. All-arity explanation of the curvature obstruction

Put j=k-(n+1)/2. Up to a common factor, w_(n,k) is binom(n,k)2^(-j^2). Divide the binomial factor by its central maximum: it is at most one and tends to one at every fixed j along either parity. Dominated convergence holds for every polynomial moment by Gaussian summability.

For odd n, j is integral; for even n it is half-integral. Let V_Z,V_H be the second moments for normalized weights 2^(-j^2) on those lattices. Then

    X_n/n^2 -> 1/4,  G_n/n^2 -> 0,
    H_n/n^2 -> V_Z-7/4 along odd n,
    H_n/n^2 -> V_H-7/4 along even n.

Exact rational truncations at eight and geometric tail estimates in the script give

    V_H-V_Z > 5381/100000000 > 0.                     (6)

Therefore H_n cannot equal a polynomial of any fixed degree plus a constant linear combination of X_n,G_n for every n. Growth would first force the polynomial degree to be at most two, after which the two parity limits contradict (6). The finite theorem in Section 4 does not depend on this additional asymptotic argument. Neither statement licenses interchanging arbitrary finite caps, Taylor orders and source sizes.

## 6. Why the attempted full proof still does not close

The hoped-for final implication was that internal body rigidity removes all curvature, allowing the ordinary chronological square to transfer unchanged. That remains INVALID.

Ordinary time can move between the two sides of the bare body. In the inherited pair-normalized regime where effective words and body deviations start at order three, this motion is

    K(u)=exp(uQ) T exp(-uQ),  u=O(epsilon^3).

Here Q is the ordinary Kingman generator. These are algebraic coordinate identities for changing already-positive pads, not new negative-time populations. With R=Ad_T Q, BCH gives

    log(K(u)T^(-1))=u(Q-R)-(u^2/2)[Q,R]+O(u^3).       (7)

A cubic u_3 consequently leaves a sixth-order body-position term. After complete cubic matching, the necessary projected equation is still

    P_log(X6+Y6-[X3,Y3]/2
                 -(u_3^2/2)[Q,Ad_T Q])=0.             (8)

Higher body tangent corrections are consumed by the original five-column projection. Actual source-direct terms, placements and both regions remain in X6,Y6. Equation (8) is asserted ONLY in that inherited cubic-leading coordinate regime; theorem (R) alone does not place every degeneration in it.

No sign was proved for (8) on all actual two-region words, and no positive zero followed by all higher equations was constructed. Moving the pad correction into the two region words merely relocates these terms in their logarithms. The one-region ordinary-target square is not a proof of the required transported two-region sign.

There is a separate global gap: the argument does not prove that every increasingly fitting arbitrary original rival sequence enters a fixed finite analytic identity-degenerating presentation near this one-bigon body. Positive-duration ordinary boundary factors, other persistent bodies, infinite reservoirs, changed exteriors, and architectures increasing with the cap are not excluded. Neither is internal body motion starting at order four or later.

Thus the full source equation remains

    U_m K_m(Lambda(U_4,V_4)) V_m-T_m=0

at every finite m with actual strict words, or an alternative finite legal equality guard must cover every admitted unknown-size rival. This pass establishes neither master alternative. It is not a permission, runtime, or compiler blocker.

## 7. Provenance, execution and review requests

The following source records were actually read at immutable main 9830affc8fdbcbf5caf75c7973a646f221a13de8:

- `research/2026-10-13-codex-g4-renewed/CONTINUATION-CARD.md`, blob 6595fd0059ff636e3cf83fb90428d1708dbdd44e.
- `research/2026-10-01-g4-admitted-testers-0819z/PROOF.md`, actual source, menu and binomial compiler.
- `research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-fixed-target/attempt-7/FIXED-TARGET-ALL-ORDER-BODY-ELIMINATION.md`, blob 135e4c7b0fdf4bcf44adbf16cbcf1b4ea13b2095.
- The sibling `attempt-6/ALL-RATIO-CONE-AND-FIXED-TARGET-FATAL-LIFT.md`.
- `research/2026-10-06-dot-g4-full-rare-route-quartic-balance-0310z/GENERAL-QUARTIC-BALANCE-CANDIDATE.md`, blob ed68fd40f9766a1eb62dcdc8ff56cda27c381cb2.
- `research/2026-10-06-dot-g4-strict-leading-chronological-obstruction-0404z/README.md`, blob c0451b0e64e68215aa7c6e978355cc30c63763da.
- `research/2026-10-13-codex-g4-renewed/critical-review/ROOT-LOG-BOUNDARY-SIGNED-ACCEPTANCE-0453Z.md`, blob df427ec50dae73d4473d6d05bb2d18c3f19a1ca9.
- The independent source-tangent/body-curvature packet beginning at handoff 443c79137a8e5221250cbb338d73e10a3a3c37bb and its later reviewed successors.

Primary-web searches did not supply the missing full-source theorem. No external identifiability or semigroup result is imported as a completion, and no historical-novelty claim is made.

Exact execution: two rank certificates; 39 tangent transcription checks; 10 separately expanded product-rule Hessian checks; 12 polynomial-degree example controls; one rational Gaussian variance-gap enclosure. The final standard-library script ran twice, with identical stdout and identical RESULTS.json SHA256 0a673a7db5271c68755dbf3da9f201f0a98bb7dd2b5dafd0861a46aa18323ad5. Finite examples check transcription; the universal degree and minimal-order proofs are hand arguments. No Lean/Rust compiler, existing integration runner, SSH, service or device action was executed.

Priority independent-review targets: the identity-center classification; n-degree bounds at every possible identity center; the exact derivative normalizations in (2)-(3); the minimal-order argument in (5); and the surviving pad-position curvature in (7)-(8). Please do not classify this as full source exclusion or a G4 master theorem. The existing integration owner retains compilation and source-selection priority.

## 11. Process-integrity assessment

GitHub reads and local Python were verified, source/menu and current ownership were checked, and the prior chronological obstruction was read rather than reconstructed as new. Both determinant algorithms and full repeat outputs agree. This packet has not received independent mathematical review. Publication hashes certify bytes, not theorem truth. No conclusion is based on presumed live agent activity.

## 12. Robustness assessment

The most important limit is quantifier scope: arbitrary FINITE extra-cell count within one analytic identity-degenerating presentation is not arbitrary original rivals. The result fixes cubic-or-earlier INTERNAL body motion, not body position, all higher coefficients, or all weak cells. Full forest equality implies the tested diagonal constraints, but the converse is false. The all-arity parity explanation is separate from the finite determinant proof. A new full-scope equality guard or exact all-prefix physical construction remains necessary.

## 13. Integration

Replay with `python check_body_rigidity.py`; the script uses only Python's standard library and writes all matrices, exact determinants and rational enclosures to RESULTS.json. A subsequent Lean development would need the integer certificate, coefficient-degree theorem, minimal-order argument and actual private-to-original observation scope, without silently adopting the full master. No new compiler assignment or runtime adoption is made. No Zotero library was modified; the text is compatible with Markdown research notes tagged hand-proof-pending-review.
