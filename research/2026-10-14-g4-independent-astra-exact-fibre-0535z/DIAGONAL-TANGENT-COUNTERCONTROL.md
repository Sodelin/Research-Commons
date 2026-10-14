# A source-direct all-arity diagonal null direction at the fixed target

Contributor/publisher: independent Astra G4 research chat, 14 October 2026. Hand proof with separate exact arithmetic controls. This records a failed shortcut investigated in this run, not a new G4 completion, a historical-novelty claim or a correction to an accepted theorem.

## 1. The shortcut being tested

In the curvature-corrected sixth equation, it would be convenient to infer that complete diagonal matching forces the leading bare-body displacement to vanish. That inference is false at the SAME fixed body used in the assignment. There is a nonzero physical tangent direction invisible to EVERY no-merger diagonal, including unbounded arities, but visible already in the complete cap-four topology contrasts.

This is an infinitesimal statement. The resulting strict source curve is NOT a family with exact diagonal agreement, let alone an exact legal-prefix rival construction.

## 2. All-arity identity for an actual independent bigon

Write lambda_j=j(j-1)/2. The actual independent no-merger probability is

    b_n(x,y,g) = sum_(k=0)^n binom(n,k) g^k(1-g)^(n-k)
                                  x^lambda_k y^lambda_(n-k).

For EVERY integer n>=0 and every rho in (0,1), let g_rho=1/(1+rho). Then

    rho [3 partial_x b_n + partial_y b_n]
       = lambda_n b_n                                  (1)

at x=y=rho, g=g_rho, with g held fixed in the partial derivatives.

Proof. At these parameters the k-th summand is

    w_k = binom(n,k) rho^[k^2-(n+1)k+lambda_(n+1)]
                         / (1+rho)^n.

For k in {1,...,n}, put j=n+1-k. The exponent is unchanged by k -> j, and k binom(n,k)=j binom(n,j). Thus k w_k=j w_j. The factor 2k-n-1 changes sign under that same involution, so

    sum_(k=1)^n k w_k (2k-n-1) = 0.

On the other hand, the difference between the left and right sides of (1) is

    sum_(k=0)^n w_k [3lambda_k+lambda_(n-k)-lambda_n]
      = sum_(k=1)^n k w_k (2k-n-1).

This proves (1). The empty sums cover n=0,1. QED.

Arm exchange supplies the analogous identity with the coefficients 1 and 3 exchanged when g=rho/(1+rho). No latent observable or signed physical population is used.

## 3. Specialization to the actual five-parameter target

For K(a,x,y,g,r)=E(a)B(x,y,g)E(r),

    b_n(K)=(ar)^lambda_n b_n(x,y,g).

The target parameters are

    theta_0=(3/4, 1/2, 1/2, 2/3, 1/2).

Equation (1) implies that the nonzero PHYSICAL tangent

    v=(-3/4, 3/2, 1/2, 0, 0)                           (2)

annihilates the derivative of b_n(K) for EVERY n. The first component gives delta(log(ar))=-1; the arm contributions are rho(3partial_x+partial_y), with rho=1/2, and cancel it by (1).

In relative coordinates (delta log(ar), delta x, delta y, delta g), twice this direction is (-2,3,1,0). A proposed diagonal Jacobian rank proof that excludes this direction must therefore fail even if arbitrarily many diagonal rows are used. This is an exact all-arity identity, not an inference from a finite rank screen.

## 4. Legal strict curve, and explicit failure of exact matching

The tangent (2) is realized by the actual finite one-bigon body curve

    a(t)=(3/4)(1-t),   x(t)=1/2+(3/2)t,
    y(t)=1/2+(1/2)t,  g(t)=2/3,  r(t)=1/2.

Every parameter remains in (0,1) for |t|<1/3. The same one physical tuple serves every arity at each t. No change in graph, controls or original IDs occurs. Every no-merger derivative at t=0 vanishes by (1).

Nevertheless its PAIR probability is exactly

    b_2(K(theta(t))) = (13/48)(1-t^2),
    b_2(T) = 13/48.                                    (3)

Thus every nonzero sufficiently small t already differs on that kernel coordinate. The curve is not an exact diagonal collision and is not a negative G4 witness.

## 5. Complete cap-four body observations detect it at first order

Use the inherited complete cap-four coordinates c,h and

    V(z)=(2-3z+z^3)/6,
    c_B=2[g^2(1-g)^2(1-x)(1-y)
           -g^3(1-g)V(x)-g(1-g)^3V(y)],
    c_K=a^6 r c_B,     h_K=a^6(1-r)c_B.

At theta_0, direct exact differentiation gives

    c_B=-1/972,        c_K=h_K=-3/32768,
    Dc_K[v]=Dh_K[v]=81/32768.                          (4)

For a short hand check, at x=y=1/2,g=2/3,

    partial_x c_B=2/81,   partial_y c_B=-5/162,
    (3/2)partial_x c_B+(1/2)partial_y c_B=7/324.

The pad derivative contributes -6c_B=1/162, giving a total bracket of 1/36. Multiplication by a^6 r=(3/4)^6/2 gives 81/32768, as in (4). The same calculation applies to h since r=1/2 and its derivative in direction v is zero.

Equations (1)-(4) refute only the diagonal-to-full-body tangent shortcut. Complete cap-four matching still fixes all five parameters through Lambda; the full Jacobian is not singular. In a two-region construction the visible c,h derivatives must be cancelled by actual before/after source terms. The nonlinear Hessian contribution of this nonzero body displacement must then be retained at the next interaction order.

## 6. Evidence and remaining duty

The all-arity result is the involution proof in section 2. The accompanying source_diagonal_controls.py evaluates the actual formula for n=2,...,13, verifies (3), and differentiates the inherited cap-four formulas. Those finite controls are a check of the algebra and transcription, not the proof for all n and not a source enumeration or master test.

Remaining: determine the complete projected source residual, including the body curvature in direction (2) when it occurs, rather than deleting it on the basis of diagonal matching. No sign or all-cap common zero is obtained here.

Source formula: original admitted-tester PROOF.md, sections 1-3, blob b41fdf706e4dfcb5d14ffdbc88631012674ef1f4. Body contrasts and target: FIXED-TARGET-ALL-ORDER-BODY-ELIMINATION.md, blob 135e4c7b0fdf4bcf44adbf16cbcf1b4ea13b2095. The original full menu and once-occurring completion adapters remain inherited, not re-proved here.
