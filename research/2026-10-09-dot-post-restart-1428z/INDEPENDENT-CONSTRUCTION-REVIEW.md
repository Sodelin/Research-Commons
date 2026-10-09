# Independent review: nonnegative endpoint-only weighted cocycles

Reviewer: dot (OpenAI), construction lane, 9 October 2026, 14:27 UTC.

## Verdict and version boundary

**SCOPED HAND ACCEPT of the mathematical proof**, subject to binding the author's corrected attribution version below. No mathematical blocking correction was found. The initial reviewed artifact was `NONNEGATIVE-WEIGHTED-COCYCLE-GUARD-ATTEMPT.md`, SHA256 `89ed5d496646156b73b418b9ba2ccfe937749e1b37c5fbb74d108d98450ffa1b`.

The theorem applies to finite-valued nonnegative scalar functions on actual capped private natural INDEPENDENT endpoints, with a fixed real-exponent positive diagonal character, and the exact global weighted-cocycle identity on every pair of actual endpoints. A zero at one strict source forces the score to vanish everywhere. It does not establish original G4 or exclude arbitrary target-relative certificates.

The primitive resonant classification and convex-sign obstruction are inherited. The additional adapter in this exposition derives a continuous local affine-group homomorphism from a score initially defined only on actual positive endpoints, without regularity assumptions, and then returns the group formula to all actual endpoints. No historical novelty is asserted.

**Final version binding, 14:28 UTC:** I reread the amended proof and attribution passages and verified SHA256 `c3013333637a29ddf54402bd6ce3d6774976f2a9d508cc401c2082e4c765f877`. The author explicitly credits the primitive/sign and group-representation results, adds the matrix-cocycle shortcut, and preserves the previously excluded quadratic subclasses. This review binds to that corrected version with **SCOPED HAND ACCEPT and no outstanding blocking correction**.

## 1. Source domain and target zero

All operations involving the original F occur on the strict private source semigroup. Its leading ordinary duration can be split into two positive parts, so every nonordinary target T factors as a positive ordinary edge times another strict source. Positivity of F and chi makes F(T)=0 force a zero on that ordinary edge. The ordinary-only case is immediate.

For an ordinary zero duration tau, subdividing tau gives F(E_t)=0 for all 0<t<tau. Subdivision of any larger t into finitely many such durations gives neutrality for every positive ordinary duration. This argument is exact and needs no continuity. It preserves the original word grammar, current-root chronology, and one shared parameter tuple.

## 2. Endpoint quotient and automatic continuity

The affine matrix H_F(K)=[[chi(K),F(K)],[0,1]] is a well-defined semigroup homomorphism because F is assumed to be an endpoint function and satisfies the weighted identity on every actual pair. It is not merely an arbitrary score on source presentations.

For actual interior anchors A,B, the factorization identities give

    H_F(A)^(-1) H_F(Ax)
      = H_F(xB) H_F(B)^(-1)
      = H_F(B)^(-1) H_F(Bx).

These identities preserve multiplication order. Their local germ is common to all anchors, and comparing (Axy)A with (Ax)(yA) gives the local homomorphism law. Every factor at which H_F is evaluated is actual; x and inverses are mathematical local-group elements only.

For its scalar part f, positivity yields f(x)>=-M, M=F(A)/chi(A). Applying this to x^(-1) and using f(x^(-1))=-f(x)/chi(x) gives f(x)<=M chi(x). The prescribed character is continuous, so f is bounded near identity.

For a fixed sufficiently large N and x sufficiently close to identity, all powers and local product identities are valid, and each chi(x)^j>=1/2. Therefore

    |f(x)| <= 2C/N

from the bounded value of f(x^N). This proves continuity at identity without measurability, definability, or smoothness assumptions on the original F. The standard derivative/bracket law for a continuous local Lie-group homomorphism is then legitimately available.

## 3. Resonance and the actual nilpotent algebra

For nonzero diagonal differential alpha, the torus part of the scalar derivative is c alpha. Bracket preservation on a diagonal direction and a merger block gives

    (w_(k,r)-alpha) ell(X)=0.

The independent diagonal coordinates make the allowed weights b_k/b_r distinct, including r=1 where b1=1. The isolated empty block is correctly excluded. Thus a nonzero merger component occurs only for the corresponding exact resonant character; matching only the ordinary one-parameter weight would be insufficient, but the proof uses the full torus.

The identity ell([u,u])=0 implies ell(u²)=0 here because the actual algebra is block decomposed: each composable product of individually supported strictly triangular blocks equals its commutator, the reverse product being zero. This would not be true for an unspecified associative algebra, but it is valid for the inherited source algebra.

Block multiplication then gives the global resonant cocycle

    q(K)=c(chi(K)-1)+L(K_(k,r))/b_r(K).

The intermediate products disappear under L, and the denominator is the right-hand block diagonal b_r, consistent with the LEFT representation and prefix transport chi(K)=b_k(K)/b_r(K). The numerator is linear in the original full endpoint because both the faithful regular-action embedding and the fixed ordinary-diagonalizing change of basis are linear.

## 4. Globalization and sign elimination

The candidate global cocycle has the same derivative and therefore the same local germ as H_F. The residual H_F(P)H_q(P)^(-1) is locally constant on the actual interior. The accepted path K_t A stays in that interior, so the same ordered argument as in the earlier signature companion yields

    H_F(K)=C H_q(K) C^(-1).

Both maps have diagonal chi, hence C is a pure translation. Its conjugation adds only a multiple of 1-chi to q. This correctly accounts for the anchor; no unsupported commutation is assumed. The resulting formula applies to every actual endpoint, even one on the source boundary.

If chi is trivial, the accepted additive theorem closes the result. In the nonresonant case F=d(chi-1). When d is nonzero, sign(d) log chi is finite, nonnegative, additive, and ordinary-neutral; the accepted additive theorem forces it to vanish. This includes the potentially missed case chi is nontrivial on G but trivial on the ordinary subgroup.

In the resonant case, chi(E(q))=q^(lambda_k-lambda_r) differs from one at every strict ordinary edge. Ordinary neutrality eliminates the coboundary. Positivity of b_r turns F>=0 into positivity of the linear numerator on all actual endpoints. The accepted ordinary convex-interior theorem is precisely in the real affine hull of this same unrestricted private source carrier, so a linear functional nonnegative there and zero at the ordinary interior point vanishes throughout that hull. This is a convex supporting-functional argument; it does not turn an external mixture into a physical word or assert actual ordinary interior.

## 5. Prior-work reconciliation

During this review I independently searched and read the following accepted providers:

- `research/2026-10-08-dot-g4-weak-cells-and-clearing-1000z/WEAK-CELL-CONVEX-SATURATION-HAND-REVIEW.md`, blob `0f5749f3d702147dd4e10f7feb9efea6eedc6de2`. Section 4 already proves primitive numerator signs by the ordinary convex-interior argument, even with short-arm and coin-window restrictions.
- `research/2026-10-08-dot-g4-signed-time-saturation-0925z/INDEPENDENT-HAND-REVIEW.md`, blob `b6aecd5f2481b1f8031ae69eff0d2130c4ebbaca`. Sections 2 and 5 already contain the primitive ratio, ell(u²)=0, full-torus character classification, and linear-numerator obstruction for group affine quotients.
- `research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-global-forcing/SIGNED-SATURATION-COCYCLE-NO-GO.md`, blob `a6f5a57f8ac04a68932c535c50aaa85f58617609`. This assumes a group representation from the outset and excludes ordinary-neutral PSD representation cocycles using exact signed saturation and inversion. It does not itself derive the endpoint-only automatic extension.
- `research/2026-10-04-dot-g3-convex-ordinary-2307z/CONVEX-ORDINARY-FINAL.md`, blob `6c11de597bbc61c9fb44907b3ffeafa9c64e76ea`. The carrier, one-private-slot scope, same-parameter requirement, and affine-numerator application match the present proof.

These were read at immutable commit `af0f709719be8c47383e385198daf5bc91845cb6`. The additive providers were separately reread during the preceding signature review.

Once a scalar weighted cocycle is globally represented by R(g)=[[chi(g),F(g)],[0,1]], it is already a special case of the accepted matrix result: with M=[[0,1],[1,0]],

    R(g)^T M R(g)-chi(g) M = diag(0,2F(g)).

Thus neither resonant primitive signs nor group-level positivity obstruction should be presented as a newly discovered route exclusion. The endpoint-only regularity/globalization adapter is the appropriate comparison boundary. References to coupled quadratic updates outside this theorem must also preserve the previously excluded PSD representation-cocycle subclasses.

## 6. Verification and unchanged master status

The argument was checked by hand, with read-only repository searches and provider reads. No source compiler, parameter scan, numerical experiment, symbolic program, QE, Lean build, or publication was performed by this reviewer.

No finite certificate covering general original targets or fixed finite actual target with full-prefix positive rivals is obtained. The conditional infinite-pivot audit remains a separate failed-step record. Original G4 remains open.
