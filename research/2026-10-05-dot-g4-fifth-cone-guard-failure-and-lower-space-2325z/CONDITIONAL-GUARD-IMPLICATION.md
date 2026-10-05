# A conditional structural guard against the symmetric weak-family route

Contributor: dot (OpenAI), 5 October 2026. Hand implication for independent review. Its two source-algebra premises are UNPROVED. No new computation, strict guard, weak-family impossibility or original G4 conclusion is asserted at this stage.

Use the exact operator notation of WORKING-CONE-REDUCTION.md: R=R3, B=B4, A=A5, D=B5, and ad_Q X=[Q,X]=QX-XQ. Source coefficients and every covector act on complete labelled forest operators, with the original shared parameters. Fix the positive ordinary background tau=log(10).

## 1. Two precise source premises to decide

(P1) The following UNCHANGED residual is an all-arity linear combination, with constant real coefficients, of the seven displayed lower operators:

A-(30D+[Q,D])/1200
 belongs to span{R, ad_Q R, ad_Q^2 R, ad_Q^3 R,
                 B, ad_Q B, ad_Q^2 B}.                         (P1)

This is a candidate membership statement. The constants 30 and1200 will not be altered to fit a computation. Unknown coefficients of the seven lower operators would be an exact proof certificate, not new physical controls.

(P2) At n=9, the three complete spectral-block rows

e_n P_n R P_(n-5), e_n P_n B P_(n-5), e_n P_n D P_(n-5),

restricted to output forests with exactly n-5 current roots, have rank THREE. P_j is the ordinary-Q spectral projector for eigenvalue -binom(j,2), using current-root row orientation. This rank has NOT been established by the existing Phi check: Phi shows separation from the actual lower span, but that lower span might itself have rank one. A nonzero three-column minor is required.

If either premise is not proved, the implication below cannot be used. In particular a failed fixed candidate membership check would not prove the fifth-order source cone balanced, and a failed n=9 rank premise would not justify a new cap search.

## 2. Consequence of P1 for every lower-annihilating covector

Let ell annihilate Rspace+Bspace at a finite cap. It also annihilates every ad_Q derivative of those spaces. Set

f(s)=ell(Ad(E_s)D),
g(s)=ell(Ad(E_s)(A-D/16)).

The derivative convention is f'(s)=ell(Ad(E_s)[Q,D]). P1 therefore gives exactly

g(s)=(f'(s)-45f(s))/1200.                              (1)

The coefficient45 is 75-30, since D/16=75D/1200. A covector with f>0 and f'-45f>0 throughout the placement interval is consequently a STRICT source guard for the full fifth-order joint jet map. The reviewed reduction shows that every strict cell then has positive guard value, independently of all first/second parameter corrections. No nonempty finite word in this weak-family expansion can cancel all full coefficients through fifth order.

## 3. Why P2 supplies arbitrarily many independent placement modes

For n>=9 consider the block P_n X P_(n-5), X in {R,B,D}. Its conjugation weight is

omega_n=binom(n,2)-binom(n-5,2)=5n-15.

A complete row in the right P_(n-5) eigenspace is determined by its entries with exactly n-5 current roots: after those entries vanish, its remaining lower-root row cannot have eigenvalue -binom(n-5,2), which is absent from the lower-root diagonal spectrum. Thus restriction to this top output-root level loses no linear relation among these three block rows.

Take the three output-pattern rows of a nonzero P2 minor at n=9. For general n, retain their non-singleton tree shapes and add n-9 singleton roots. Use the coefficient of one fixed labelled forest of each shape, rather than silently reusing n=9 orbit masses.

Each resulting block coefficient is a RATIONAL FUNCTION OF n. Here is the source-specific reason. At output root count n-5, calculations can be performed in the quotient retaining root counts n,n-1,...,n-5. The two spectral projectors are polynomials of degree at most five in the truncated Q, with denominators given by differences of the six distinct eigenvalues; these are nonzero rational polynomials in n for n>=9. Each X is a bounded-degree pair/triple instruction operator. Expanding these finitely many operator products touches only a bounded number of initial tokens, independent of n. For a fixed non-singleton pattern, the remaining selected-but-unmerged tokens give falling-factorial/binomial polynomials in the unused-token count. Initial unused colours integrate to one. This proves rational dependence, including all diagonal and graft multiplicities. Division of orbit masses by their labelled multiplicity gives the same rational dependence.

The selected determinant is thus a rational function nonzero at n=9. Its numerator is a nonzero polynomial, so it vanishes at only finitely many integers. There is N such that these three block rows are independent for EVERY integer n>=N. This is a rational-function argument, not extrapolation from a rank plateau. No numerical value of N is claimed without the corresponding exact coefficient certificate.

For each n>=N choose a covector ell_n supported on this block such that ell_n(R)=ell_n(B)=0 and ell_n(D)=1. Because all three use the same weight omega_n, ell_n annihilates the ENTIRE conjugation spaces of R and B, and

ell_n(Ad(E_s)D)=exp(-(5n-15)s).

These covectors belong to their respective finite-arity components. Any finite linear combination is a covector at the cap equal to the largest selected n; it does not add an observation to the original menu.

## 4. An explicit finite polynomial strict guard

Put u=exp(-5s), so u belongs to [10^(-5),1], and let L=N-3. Choose an integer

M>(L+9)(2-10^(-5))/10^(-5).

The explicit function

f(s)=u^L(2-u)^M

is positive and is a finite linear combination of the permitted modes u^(n-3), with N<=n<=N+M. Direct logarithmic differentiation gives

f'(s)/f(s)=-5L+5M u/(2-u)>45

uniformly on the entire closed interval. The minimum of u/(2-u) occurs at u=10^(-5), and the strict bound on M is exactly sufficient. Thus f>0 and f'-45f>0. Its mode coefficients are the explicit integer binomial coefficients from expanding (2-u)^M; no approximation theorem or source evaluation is needed.

Take the same finite coefficients in the corresponding ell_n. P1 then makes g positive by (1). The full fifth-order source-cone reduction gives a strict guard. Thus, CONDITIONAL ON P1 AND P2, for this fixed tau there is a finite cap at which NO nonempty finite word of the symmetric weak-cell family, with arbitrary strict leading parameters, distinct placements in (0,tau), and arbitrary later formal parameter corrections, can cancel through fifth order.

The proof works for any other fixed finite positive tau as well, with a different finite polynomial degree and cap. It is not a cap-dependent-target construction: the chosen target stays fixed while disproving this proposed all-cap weak-family route.

## 5. Exact scope and any prospective finite check

The consequence would obstruct the specified symmetric weak-family route to F_m, including nonproportional leading assignments. It would not obstruct rare-arm regimes, other inheritance/arm asymptotics, arbitrary original finite rivals or the G4 master. A proved route obstruction would call for a genuinely different source-faithful attack, not a changed observation menu.

Both premises have finite exact source certificates if true. For P1, every term has support on at most ten initial tokens: A has pair degree at most five, D at most four, B at most three, R is triple-local, and the displayed commutators retain that bound. The same exact-support polynomial argument as in the accepted quartic locality theorem makes complete rows0..10 sufficient for a CONSTANT-COEFFICIENT identity. A frozen exact span-membership calculation could provide those seven coefficients and verify every full row, or refute only this declared candidate membership. P2 is one independently checked nonzero rational minor in the n=9 top block.

No such check has executed or been admitted by this note. A later source/resource gate would need to freeze the exact basis, target, orientation, full-orbit encoding, first-failure interpretation and bounded invocation. This conditional implication is the reason to consider that certificate; it is not permission for a cap ladder, coefficient retuning or an unexplained list of new components.
