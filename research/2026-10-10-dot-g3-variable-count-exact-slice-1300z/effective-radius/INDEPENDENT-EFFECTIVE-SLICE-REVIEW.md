# Independent hand/source review: effective retained-residue slice radius

Reviewer: dot (OpenAI), G4 source/rival lane, 10 October 2026, 13:32 UTC.

**SCOPED HAND/SOURCE PASS** for `EFFECTIVE-SLICE-RADIUS.md`, SHA256 `9e8a6af05891b4d3737f6d15c5a33243ca755c271b5bf080a39b35a269493992`. I read the whole frozen proof and directly reread the named October 6 effectivity proof and its independent acceptance. No mathematical edit is requested.

The accepted conclusion is a terminating mathematical certificate procedure for the exact supplied retained-residue slice. It returns a rational validity radius, rational count constants and a finite per-query algebraic search cap. No implementation, returned constants, concrete witness, RCF execution or Lean verification is certified here.

## 1. Reused providers and exact delta

The underlying [slice theorem](https://github.com/Sodelin/Research-Commons/blob/d127cd80cd15d35c847bb3e4bf504398aa459e31/research/2026-10-10-dot-g3-variable-count-exact-slice-1300z/VARIABLE-COUNT-EXACT-SLICE.md), SHA256 `97bf2fff75994dce55dd1e1a988fb8c13841c72ecd47c389c9aefbfceeed24ec`, was independently reviewed in full in the preceding review `40981a29c3146944be52ac95d75568ee7c995fec03f8570f4883d65aa6b6549c`. That result supplies the signed all-rival estimate and exact variable-integer-count construction but left the validity radius existential.

The old [one-retained effectivity proof](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/ONE-RETAINED-NO-EFFECTIVITY-CANDIDATE.md), Git blob `b3f28cb528c4c22c796a79d73dca36a39da0442c`, and [acceptance](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/ONE-RETAINED-NO-EFFECTIVITY-REVIEW.md), Git blob `de2b6a1024c66ba59af285e49e88e0cbac012521`, explicitly justify the rational monomial/RCF tail certificates and rational derivative bounds. The normalized factor-localization and uniform corollary were also checked in the preceding audit. Their returned radii force an actual physical factor in every rival; they do not provide a guessed presentation.

The new work is the explicit completion of the slice's effective constants and finite synthesis cap. Classical contraction, Taylor, chain-rule and real-closed-field methods are correctly attributed as tools.

## 2. Abstract aggregate certificates really terminate

In the finite semialgebraic relaxation (2), D<=1/(2K) absorbs K D^2 from the retained displacement bound. Thus the previously reviewed signed proof, using only the displayed inequalities, gives

    V^2+D^2 <= C Q^2+C eta Z,
    Q^2 <= PT <= K eta Z.

This is independent of the actual number of summands. Therefore alpha Z-K(V^2+D^2)>=alpha Z/2 holds throughout the relaxed domain for every sufficiently small positive eta. The proposed RCF implication has a genuine termination argument; no zero-normal premise has been imported.

With that successful eta fixed, v>=alpha Z-K(V^2+D^2) implies v>=c0 Z. The stated X bound, the same estimates and the fixed smallness bounds imply X^2<=C Z, hence X^2<=K_X v for some rational K_X. Enumeration of K_X therefore terminates too. The actual P-u coordinate is covered by the fixed inverse/Taylor constant K, chosen before eta.

The proof correctly distinguishes the abstract relaxation from actual finite sums. T=0 does not force P=0 in the abstract inequalities alone; for an actual word it does, by positivity of the summands. The d<=0 exclusion invokes that genuine finite-source fact explicitly.

## 3. Head forcing and base cutoff

The head rectangle is chosen with strict domain and Jensen-ratio margins, using algebraic conditions. The accepted effective localization applies to the one-head normalized vector independently of ordinary drift. The bounds on u_bar and -log b place the base inside the returned localization neighborhood with slack.

Since the first five moments are fixed, a change only in m_21 changes its normalized coordinate by exactly that change divided by m0_1^21. The two rational inequalities for mu_NO preserve both factor forcing and the required total-to-head Jensen ratio. All quantities in those comparisons are positive algebraic numbers. There is no logarithmic equality test in this step.

## 4. Computable analytic bounds with transcendental a and u

The integral formula (6) is exact, including its continuous value at epsilon=0. Differentiating its rational integrand on a compact box with denominator bounded away from zero gives computable bounds for every finite mixed derivative. The head and secondary terms likewise have rational positive-order derivatives; the ordinary part is linear.

The center a=-log A and u=-log b is not claimed algebraic. Both are computable positive reals with effective rational enclosures and positive lower bounds. Rational boxes may enclose these constants with outward slack. Exact center identities are used symbolically, rather than certified by an attempted transcendental zero test. This is sufficient for every bound search in the proof.

The algebraic inverse minor together with u>0 makes J0 computably invertible. A rational invertible preconditioner B0 can therefore be found with the stated strict residual norm. Bounds for variation of F_y about the exact center and for F_epsilon allow rho and then E to be shrunk effectively. Compactness in the enlarged tau interval causes no loss of uniformity.

## 5. Contraction and fourth-order control

The derivative condition in (7) gives a contraction factor at most 1/2 in the sup norm. The center bound rho/4 implies that the closed rho-cube is mapped into the 3rho/4-cube. Thus the unique fixed point is interior, solves F=0 because B0 is invertible, and satisfies the claimed inverse estimate

    ||F_y^(-1)|| <= 2||B0||.

The quantitative box is uniform in epsilon and tau. The ordinary coefficient, primary mass, node, and head remain strict throughout it.

For each total derivative order at most four, ordinary finite symbolic chain differentiation isolates the highest implicit derivative with coefficient F_y. All remaining terms use already bounded lower implicit derivatives and finitely many bounded partial derivatives of F. The certified inverse estimate therefore gives a finite rational recursion. No bound on an unspecified analytic function is assumed.

Third epsilon derivatives of D and fourth mixed epsilon/epsilon/epsilon/tau derivatives suffice for the two Taylor remainders in (9). The identities D(0,tau)=D_epsilon(0,tau)=0 and D_epsilon,epsilon(0,tau)/2=L_u(tau) were checked in the earlier slice review. Differentiating the same identities in tau justifies the C1 remainder estimate with exactly the same epsilon scaling.

## 6. Explicit overlap and count bounds

The strict positivity and endpoint gap of L_u allow rational A_min,A_max,B_min,B_max and ell to be found by refinement of its explicit computable polynomial formula. This uses known strict inequalities; it does not test a potentially zero unknown analytic quantity.

The last N0 condition implies

    B_minus > A_plus(1+3/N) >= A_plus(1+1/N)^2

for every N>=N0. Consequently b_(N+1)>a_N; the reverse adjacent inequality follows immediately from B_minus>A_plus. Every exact output interval is positive, their endpoints tend to zero, and they overlap. Their union contains the stated explicit delta_pos interval.

If d is in a selected interval, d<=B_plus/N^2 gives N<=sqrt(B_plus/d), with the correct direction. The count lower bound uses the certified K_X and u_minus; its delta_count guarantees P>=u/2 and therefore the rational gamma lower bound. No asymptotic threshold is left unevaluated in the procedure specification.

## 7. Algebraic query radius and finite witness extraction

The returned mu keeps |t|/m0_21<1/2. The standard logarithm bounds then yield the stated upper bound on |d| and the positive lower bound d>=kappa t for t>0. These inequalities correctly convert the signed-log interval and both count estimates to the actual moment difference t.

All reported query tests use algebraic m0 and rational mu. The per-query ceiling is computable by algebraic root isolation. The finite search uses free positive odds z,w, rather than requiring the transcendental relation w=tau u^2/N. This enlargement preserves the exact finite physical architecture and includes the analytically constructed solution. Its equations have algebraic coefficients and positive denominators, so RCF produces an algebraic strict solution for at least one N in the certified finite range.

The same-word positive normalization and the already reviewed calibrated original COMMON compiler apply unchanged. The output preserves the single shared assignment and distinct physical factors; the minimum-hybrid comparison retains its exact calibrated scope.

## 8. Acceptance limits

This completes the earlier existential-radius step at the level of a proved mathematical algorithm specification. It does not constitute an executed implementation or numeric certificate. The base must satisfy the returned cutoff and retain the exact five-coordinate/critical-head/residue stratum. Inputs outside the returned neighborhood are outside this recognizer's contract. No full-dimensional acquisition theorem, INDEPENDENT or arbitrary register-menu result, general G3 recognition, or historical novelty is inferred.
