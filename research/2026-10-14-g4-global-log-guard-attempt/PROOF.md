# G4 full-proof attempt: no finite additive log-diagonal guard

Contributor: independent Astra G4 researcher for Nolan, 14 October 2026.
Read snapshot: 1a9e07ff7ca184f85b5def37cf6a827fa541d054.
Status: HAND PROOF, pending independent mathematical review. The full-master proof attempt is unsuccessful. No Lean/Rust, integration, SSH or device execution is claimed.

## 0. Endpoint and outcome

The earlier extra-reticulation exclusion is an accepted natural BOTH supplier. It uses a finite COMMON certificate to fix ancestral clocks/profiles before excluding arbitrary-count additional cells. The proposed complete positive route here was to replace that input by a source-additive positivity guard computed from finitely many INDEPENDENT no-merger rows, and then invoke the exact finite-I equivalence and BOTH theorem.

The universal-sign premise of that route is false at EVERY finite cap: every nonzero weighted sum of pair-normalized log no-merger probabilities takes BOTH signs on arbitrarily weak strict physical cells. The proof below is all-orders, not an extrapolation from finite controls. One-cell insertions can keep the target bridge's complete pair kernel exactly unchanged and move the proposed guard in either direction, while decreasing a legal COMMON crossed-cherry probability in both cases.

This rejects this class of additive log-diagonal guards. It does not refute nonlinear diagonal identities, chronology-sensitive forest/topology guards, or source-specific signs after imposing further exact target-fibre equations. It gives no exact all-prefix rival family and no master closure.

The preserved positive obligation is: for each fixed admitted T, finite original legal I rows J_T must force its inherited finite COMMON certificate C_T against EVERY admitted finite unknown-size rival N, using one graph and shared tuple. The qualifying negative alternative fixes ONE strict T and requires exact inequivalent finite physical rivals after EVERY finite full-legal-I prefix.

## 1. Actual source coordinates and additivity

Put lambda_n=n(n-1)/2. The inherited current-root INDEPENDENT bigon formula is

    b_n(x,y,g)=sum_{k=0}^n binomial(n,k) g^k(1-g)^(n-k)
                         x^lambda_k y^lambda_(n-k),
    Phi_n=log b_n-lambda_n log b_2.

Here x,y,g are strictly in (0,1), and n counts currently surviving opaque rooted genealogies. No merged genealogy is resampled at the leaf level. These private diagonals are analytic coordinates, not newly granted legal observations.

On a serial no-merger event every factor receives the same n roots, so b_n multiplies and Phi_n adds. Ordinary populations have Phi_n=0. This diagonal identity does not say that full forest kernels commute or that chronology may be omitted from the master equation.

Use the inherited insertion grammar only on an eligible unmarked bridge. Retain the root, original taxa and labels, exterior, joint-program scope, and shared parameters. Extra read-only clocks or parameter ties are not relaxed.

## 2. A strictly physical rare-route family

For 0<rho<1, z>0 and 0<e<min(1,1/z), take

    B_e=B(rho,1-z e,e).

Both population exposures are finite and positive; the inheritance is interior. At e=0 the kernel is the identity, used only as an analytic expansion center. The independent pair cost -log b_2 tends to zero. At any fixed complete forest cap the kernel tends to identity as well, since rare routing has probability O(e) and the used arm shrinks. No uniform-in-cap estimate is asserted.

### 2.1 Degree bound

Factor the source diagonal as

    b_n=(1-z e)^lambda_n (1-e)^n S_n,
    S_n=sum_k binomial(n,k) [e/(1-e)]^k rho^lambda_k
                 (1-z e)^[-nk+k(k+1)/2].

At coefficient order r only k<=r contributes. The binomial factor has degree k in n. At remaining order j the final factor has degree at most j in n, because its exponent is affine in n for fixed k. The factor (1-e)^(-k) adds no n-degree. Thus the order-r coefficients of S_n and log S_n have degree at most r in n. The separate n log(1-e) has degree one; the ordinary lambda_n log(1-z e) cancels under pair normalization.

Therefore [e^r]Phi_n is a polynomial in n of degree at most r, vanishing at n=0,1,2. Orders one and two vanish identically. For r>=3 this polynomial is in the span of binomial(n,3),...,binomial(n,r). This is an algebraic identity for all integer n, not a fitted degree bound.

### 2.2 Highest coefficient

Let

    A_rho(u)=sum_{k>=0} rho^[k(k-1)/2] u^k/k!,
    P_r(rho,z)=[u^r] log A_rho(u exp(z u)).

The coefficient of n^r in [e^r]Phi_n is P_r(rho,z). To extract it, keep only terms whose n-degree equals their e-degree: binomial(n,k)e^k contributes u^k/k!, and the last factor contributes exp(zuk). Lower n-degrees and the normalized ordinary term do not enter. At each fixed r only k<=r is used, so this is a finite formal calculation, with no exchange of infinite analytic limits.

Equivalently, the coefficient of binomial(n,r) in [e^r]Phi_n is r! P_r(rho,z).

## 3. Both coefficient signs at EVERY order

Fix any integer r>=3. For fixed rho, P_r is a polynomial in z with leading term z^(r-1)/(r-1)!, so it is positive for sufficiently large finite z.

For the negative sign use rho=0 only as a coefficient reference. Then A_0(u)=1+u and

    P_r(0,z)=sum_{k=1}^r (-1)^(k-1) (kz)^(r-k)/(k(r-k)!).

Set z_r=(r-1)2^(r-4)>0 and t_k=(kz_r)^(r-k)/(k(r-k)!)>0. Directly, t_2=2t_1. For 2<=k<=r-2,

    t_(k+1)/t_k
      =[(r-k)/(z_r k)](1+1/k)^(r-k-2)
      <=[(r-2)/(2(r-1))](3/4)^(r-4)
      <=1/3.

For r>=4 the last bound starts at 1/3 and decreases, since its successive ratio is 3(r-1)^2/[4r(r-2)]<1. For k=r-1 the ratio is 1/(r z_r)<=1/3, including r=3. Thus the alternating tail starting at t_3 is at most t_3<=2t_1/3. Hence

    P_r(0,z_r)=t_1-t_2+t_3-t_4+... <= -t_1/3 <0.

For fixed r the coefficient P_r is a finite polynomial in rho and z. Continuity supplies a sufficiently small STRICT rho>0 with P_r(rho,z_r)<0. The actual selected rare arm therefore has finite positive exposure. No rho=0 physical source is used. This proves both signs for every r>=3.

## 4. Complete finite-guard theorem

**Theorem.** For every m>=3, every nonzero real vector a=(a_3,...,a_m), and every eta>0, there exist actual strict cells B_- and B_+ in section 2 with independent pair cost below eta such that

    sum_{n=3}^m a_n Phi_n(B_-) < 0 < sum_{n=3}^m a_n Phi_n(B_+).

**Proof.** The vectors binomial(n,r), n=3,...,m, indexed by r=3,...,m, form a triangular basis. Let r be the least index with

    c_r=sum_{n=3}^m a_n binomial(n,r) !=0.

All lower Taylor orders of the weighted Phi expression vanish by section 2.1 and the minimality of r. Its leading coefficient at order r is r! c_r P_r(rho,z). Choose the sign of P_r to agree with or oppose c_r using section 3. For sufficiently small strictly positive e the actual source expression has the respective strict sign. Shrink e further to ensure all parameters are strict and -log b_2<eta. QED.

Omitted arities are covered by zero-padding a up to its largest index. Equivalently, any finite weighted sum of log b_n that vanishes on every ordinary edge fails a universal nonnegative added-cell sign unless it is identically zero. Weights may depend on the fixed target. This conclusion concerns signs of actual finite sources, not only a formal leading cone.

## 5. Exact insertion at one fixed target

Suppose the fixed admitted target has an eligible freely replaceable ordinary bridge with pair survival d in (0,1). Choose either sign cell with b_2>d. Replace that bridge by

    E(s) B(rho,1-z e,e) E(s),    s=sqrt(d/b_2) in (0,1).

Both pads are positive, and the complete private two-root kernel is exactly E(d). At every n,

    log[d_n(replacement)/d^lambda_n]=Phi_n(B).

Thus every nonzero finite log-diagonal guard moves in either direction under an actual one-reticulation, exact pair-matched insertion into the SAME fixed target. Its exterior and parameter tuple remain unchanged across experiments. Strict rational rho,z,e can be chosen because the sign inequalities are open; if d is algebraic, the padding survivals are algebraic as well.

The cell's COMMON pair survival is c_2=gx+(1-g)y, with

    b_2-c_2=g(1-g)(2-x-y)>0.

After padding the COMMON survival is d c_2/b_2<d for either guard-sign choice. On a pendant bridge, the positive COMMON crossed-cherry event with two pendant-taxon copies and one external original taxon is multiplied by c_2/b_2. This is a legal completed-topology marginal under the inherited unchanged-exterior adapter. It is not a private-state measurement.

These examples are not exact matches to an entire prescribed I prefix: other rows generally change. They therefore do not prove the negative master, even though the pair equality and the guard-sign inequalities are exact.

## 6. Full-proof verdict and attribution

The attempted positive proof would use a universal additive log cost to rule out every added cell, then recover C_T and invoke BOTH. Its universal-sign premise is now contradicted for EVERY finite no-merger panel, including arbitrarily weak insertions. More diagonal rows do not repair this class of argument.

The accepted BOTH proof remains intact: it imposes additional exact COMMON palette/clock/paired-ratio constraints before its sign argument. This note does not show that a sign fails on a separately constrained full target fibre. Nonlinear diagonal predicates and chronological full-forest/topology identities remain possible. Neither an exact all-cap return nor a global equality guard is supplied here.

The October 8 all-ratio theorem already rules out a universal separator of the complete cubic/quartic leading correction span; that is reused and not claimed as new. This note concerns arbitrary finite LOG-DIAGONAL covectors at arbitrary order, not arbitrary full-forest covectors. Historical novelty is unassessed. Repository searches yielding no match are not proof of absence.

The deformed exponential A_rho and its connected-graph logarithm are classical. A primary reference inspected in HTML is Alexey Kuznetsov, *On series expansions of zeros of the deformed exponential function*, arXiv:2412.02462v1 (2024), https://arxiv.org/abs/2412.02462. No zero-location theorem from that paper is needed here. The separate AMS full-text route failed and is not claimed as inspected.

## 7. Exact source and review pins

All repository sources below were read at 1a9e07ff7ca184f85b5def37cf6a827fa541d054:

- `research/2026-10-01-g4-admitted-testers-0819z/PROOF.md`, sections 1,3,4: current-root source formula, source admission and bridge insertion.
- `research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/FINITE-INDEPENDENT-BRIDGE-EXACT-EQUIVALENCE.md`, blob a34fe26c169887c9eafbc482a5d4e046601df911.
- `research/2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-NATURAL-BOTH-FINITE-FORCING-ACCEPTANCE.md`, blob ed2f8070d8aa7bbf2e45e5369c65c7b78dfcc21a.
- Its `whole-source/continuation-2110z/COMPLETE-ORIGINAL-NATURAL-BOTH-LOCAL-EXCLUSION.md`, blob 6d78a55abb66606407a7b87346e0d90fef4be41b.
- `research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-fixed-target/attempt-6/ALL-RATIO-CONE-AND-FIXED-TARGET-FATAL-LIFT.md`.
- `research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/INDEPENDENT-COMMON-TRANSFER-DISCONTINUITY.md`, blob ea154cfb7daaa8897e6632935853ec43356bf2d3.

## 11. Process-integrity assessment

The isolated standard-library script has 448 passing exact integer/rational assertions. It checks the boundary sign and decreasing alternating tail through order 40; the independently expanded physical polynomial coefficients through order 10; opposite strict-parameter leading signs through order 20; and eight actual rational sign witnesses with exact target-pair padding. Two runs returned exit 0 with identical receipt bytes. These finite ranges are controls, not the justification for the universal theorem. Initial floating-point exploration is not certification evidence.

This hand proof has not been independently reviewed or Lean-verified. Reviewer priorities are the polynomial degree, highest-degree extraction, all-order alternating estimate, least-Newton-index argument, and physical bridge embedding. A correct arithmetic receipt would not repair an error in these logical implications. The integration pause and existing compiler ownership were preserved.

## 12. Robustness and remaining master duty

The quantifiers cover every finite cap and every nonzero fixed log-diagonal covector, but not every nonlinear/full-topology predicate. No chronology is removed from a full-source equation. The rho=0 reference is moved to strict rho>0 before an actual source is selected.

The positive master still needs finite legal I equalities forcing C_T on EVERY original finite rival. The source-centred negative route still needs actual strict solutions of

    U_m K_m(Lambda(U_4,V_4)) V_m=K_m(T)

on COMPLETE forest kernels for every finite cap, the same target, and later original legal inequivalence. Neither assertion is established here. This is a rejected full-proof mechanism, not G4 closure.
