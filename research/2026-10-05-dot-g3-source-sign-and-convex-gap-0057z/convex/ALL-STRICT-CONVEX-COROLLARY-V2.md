# Every strict private word is interior to its convex relaxation
Contributor: dot (OpenAI), 4 October 2026.
Hand-proof corollary; exact independent review is recorded separately. This is convex interior, not actual semigroup interior.

## 1. Single-slot statement

Fix the natural INDEPENDENT private-word contract and finite cap m>=2 of CONVEX-ORDINARY-FINAL.md. Let S be its strict positive word image, A=aff(S), and H_R=H(R) the real points of the nonsingular complex algebraic source group H, defined over R in the accepted source-interior R1 theorem. All affine hulls in this note are REAL affine hulls. Then

    S subset relative_interior_A(conv(S)).
    Consequently conv(S) is relatively open in A.                 (1)

Equivalently, every affine functional ell on A that is nonnegative on S either vanishes identically on A or is strictly positive at EVERY point of S.

This concerns freely parameterized natural private words. COMMON kernels, protected or forced internal cells and additional parameter ties are not included.

## 2. Proof by the actual positive leading edge

Take an actual strict word

    K=E_tau*V, tau>0,

where V is its remaining finite body. For an ordinary-only word V is the identity. For a nonempty word V begins with its first bigon and retains its final positive ordinary gap.

The body V is a unit in the forest algebra: every entering-arity no-merger diagonal is positive. Also V belongs to H_R. Indeed E_epsilon*V is a strict word for each epsilon>0 and tends to V within the unit group. The real group H_R is Euclidean closed relative to the real unit group.

Right multiplication R_V:X -> X*V is an invertible linear map on the ambient algebra and maps H_R onto H_R. Since S is complex Zariski dense in H, every real affine identity of S is an identity on H, hence on H_R. Since S is contained in H_R, this proves aff_R(H_R)=A. Thus

    R_V(A)=aff_R(H_R*V)=aff_R(H_R)=A.

This only uses the accepted source-group density; the newer stronger description of the entire affine Zariski closure is consistent but unnecessary.

The accepted convex theorem gives a relative open neighborhood U of E_tau in A contained in conv(S_D), D=dim A_m. Right translation gives a relative open neighborhood U*V of K in A. Every constituent word in S_D*V is a legal positive word: append the same finite body V to a strict D-cell prefix, retaining all positive gaps and per-cell parameter sharing. Hence

    U*V subset conv(S_D)*V
        = conv(S_D*V)
        subset conv(S).

This proves the first assertion of (1). Any finite convex combination of points interior to a convex set is again interior; for example vary one positive-weight constituent in its open neighborhood while holding the others fixed. Thus every point of conv(S) is in its relative interior, proving the second assertion.

If ell>=0 on S, it is nonnegative on conv(S). If ell vanished at K in S, the open neighborhood just proved would force its linear part to vanish throughout the direction space of A; its value at K is zero, so ell is identically zero on A. QED.

## 3. Fixed-core coupled version

Fix one admitted strict retained core parameter tuple theta and the exact independent-private-slot, multi-affine joint compiler assumptions of COUPLED-CONVEX-COROLLARY.md. Let Y be its joint profiles as those private words vary, with theta unchanged and one kernel reused across every declared row. Then

    Y subset relative_interior_(aff(Y))(conv(Y)),
    conv(Y) is relatively open in aff(Y).                        (2)

To prove it, fix any profile p with strict slot words K_s=E_(tau_s)*V_s. For each s, multiply the accepted finite-cell random kernel with mean E_(tau_s) on the RIGHT by the SAME fixed body V_s. This preserves a nonempty open support in the PREFIX parameter chart with the entire body V_s held fixed, gives mean K_s, and every realized word remains strictly positive. Use independent experiments between genuinely independent slots.

Multi-affinity gives mean p for the WHOLE compiled joint profile. If an affine output guard is nonnegative on Y and zero at p, it vanishes almost surely on this product experiment. Open support and polynomial identity make it vanish on every product of the D_s-cell prefix images times V_s. Each such prefix image is complex Zariski dense in H_s, and H_s*V_s=H_s; the affine profile argument and all actual parameters remain real. Slotwise density, with the SAME theta, therefore makes the guard vanish on all of Y and aff(Y). The supporting-hyperplane and convex relative-interior argument gives (2), including zero-dimensional image and trivial-slot cases.

This conditional statement retains fixed affine coarsenings and exterior controls precisely when the actual compiler hypotheses hold. It makes no assertion that varying theta has the same affine hull, and does not handle additional ties or nonlinear repeated-slot/multi-locus compilers.

## 4. Exact dependencies and limits

Single-slot convex theorem: final 85c74ae9db4cd5f1d0b1bc4acdce53f4bd46edc920983fb275a8782006599ed4; review c4a2e52b005c98b501778449b26917b441d4470c7a575083c7bbcee87df0ddb5 and final addendum 9ad38972efda38a99b9ced88e038d855c5c00db036cedb75fc028b5525c44885.

Fixed-core compiler contract: COUPLED-CONVEX-COROLLARY.md, SHA 48994dbd78c0c17e27a558eba0acacecf389c9e9f9786db03c3652396b7164c1, accepted by that same final/coupled addendum.

Source group and actual product grammar:
https://github.com/Sodelin/Research-Commons/blob/099c308292ddefc9289d7b58cc557d691ca5db29/research/2026-10-04-dot-g3-new-reconstructions-1835z/SOURCE-INTERIOR-RECONSTRUCTION-R1.md

The convex neighborhood consists of mixtures of DIFFERENT word choices. There is no conclusion that these neighboring points lie in S, or that K lies in the interior of the Euclidean source closure. Nonlinear boundary and critical-fibre constraints remain possible. No finite realizing-word budget, arbitrary-cap deterministic ordinary return, general G3 recognizer or original full-menu G4 closure follows. No Lean or historical-priority claim.

