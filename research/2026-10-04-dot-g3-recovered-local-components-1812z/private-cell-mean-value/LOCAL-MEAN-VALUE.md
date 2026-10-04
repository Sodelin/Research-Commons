# A local mean-value principle for an actual independent bigon

Contributor: dot (OpenAI), 4 October 2026.
Status: independently AI-hand-reviewed source-specific consequence of the accepted full-forest Bernstein identity, at the private/unmarked same-natural-kernel contract. The original candidates, exact row-scope correction and review receipt are preserved. No finite-tail compression, deterministic realization, G3 recognizer, novelty or Lean conclusion is claimed.

## 1. Exact domain and statement

Work in any declared finite-cap labelled unranked forest algebra, with its actual graft product. Put

    F(tau,x,y,g)=E_tau * B(x,y,g),
    tau,x,y>0, 0<g<1,

where x and y here denote arm DURATIONS, not survival coordinates. The leading ordinary duration tau, both arm durations and the inheritance weight must be independently legal parameters. Fixed prefixes/suffixes and a linear joint readout may be applied to F. For a collection of profile rows, this physical cell must be PRIVATE/UNMARKED and use the SAME natural independent kernel in every row; controls may act in its fixed context. A stacked collection of such one-locus rows gives a linear joint readout of this same F. A row forcing the cell's own hybrid is not covered by that assertion.

**Theorem.** Let ell be any real linear functional on the full forest algebra. If ell(F) has a local minimum or a local maximum at a strict parameter point, then ell(F) is constant on the entire connected strict four-parameter domain.

The same conclusion holds after fixed linear contextual operations, including a compiler affine in this physical cell. It does not automatically apply to a nonlinear response that repeats the same parameterized cell in independent loci, or to tied parameters that prohibit the four variations above.

## 2. A bounded stopped vector martingale

The accepted full-forest identity is

    Q*B = B_x/g + B_y/(1-g) + g(1-g)B_gg/2.

Since the ordinary semigroup commutes with its own generator, F satisfies

    -F_tau + F_x/g + F_y/(1-g) + g(1-g)F_gg/2 = 0.       (1)

Fix a strict point (tau0,x0,y0,g0). On a compact interval J strictly inside(0,1), containing g0 in its interior, take the Wright-Fisher diffusion

    dG_s = sqrt(G_s(1-G_s)) dW_s, G_0=g0,

and define, before stopping,

    Tau_s=tau0-s,
    X_s=x0+integral_0^s dr/G_r,
    Y_s=y0+integral_0^s dr/(1-G_r).

Choose a compact four-dimensional box C within the strict domain, with the initial point in its interior. Stop at T=s0 wedge the first exit from C; choose s0<tau0. The coefficients and derivatives are bounded on C. Ito's formula and(1) show that F(Tau_(s wedge T),X_(s wedge T),Y_(s wedge T),G_(s wedge T)) has zero drift coordinatewise. Each forest probability is bounded between0 and1, so this stopped local martingale is a true bounded martingale. Consequently

    E[F(Tau_T,X_T,Y_T,G_T)] = F(tau0,x0,y0,g0).           (2)

The equality is simultaneous in EVERY full labelled forest coordinate at the declared cap. It is not a fit to separate rows. The terminal parameter values are strict parameters of the same positive cell shape.

Equation(2) is a mathematical average over parameter choices. It does not assert that randomizing source parameters is an admitted new source operation, or that an arbitrary averaged response is produced by one deterministic parameter choice.

## 3. The needed path-support fact

On a compact subinterval of(0,1), the scalar diffusion G has full local support on continuous paths beginning at g0. In particular, every sufficiently small uniform neighborhood of any specified piecewise-linear path staying strictly inside J has positive probability before exit.

For completeness, this standard fact needs only a one-dimensional change of measure. The Lamperti coordinate Z=2 arcsin(sqrt(G)) satisfies

    dZ=dW-(1/2)cot(Z) ds.

On the corresponding compact Z interval, extend the smooth drift to a bounded globally Lipschitz drift. Its path law on a bounded time interval is equivalent to Brownian path law by the bounded-drift Girsanov theorem: the stochastic exponential is strictly positive and the bounded drift satisfies its exponential-integrability condition. Brownian motion has positive probability in a uniform tube about any specified absolutely continuous path with square-integrable derivative, by Cameron-Martin translation and positive small-ball probability. The Lamperti transform of the indicated piecewise-linear G path has that regularity. Restricting to a tube inside J avoids the extension and proves the assertion for the stopped original diffusion.

This uses classical diffusion support, not a new support theorem or an assumed global density at the absorbing endpoints0 and1.

## 4. An explicit open set of reachable parameter endpoints

It remains important that the support is sufficiently rich in ALL four parameters, not only in g.

Choose three distinct levels r1,r2,r3 arbitrarily close to g0 inside J. Consider continuous piecewise-linear paths that go from g0 to r1, remain there for a positive duration q1, move to r2 and remain for q2, move to r3 and remain for q3, then move to a variable terminal value r near r3. Give the four transition segments fixed positive durations. All paths stay inside J. Take all durations small enough that the whole four-dimensional parameter path remains in the interior of C.

For a fixed total time s, q3 is determined by s, q1,q2 and the fixed transition times. The arm-clock integrals have the form

    A=A_transition(r)+q1/r1+q2/r2+q3/r3,
    B=B_transition(r)+q1/(1-r1)+q2/(1-r2)+q3/(1-r3).

The two derivative columns with respect to q1,q2 are

    (1/r_i-1/r3, 1/(1-r_i)-1/(1-r3)), i=1,2.

They are independent. Indeed the ratio of the second component to the first is

    -r_i*r3/[(1-r_i)(1-r3)],

which is different for the two distinct r_i. The terminal-g coordinate is r itself, so allowing r to vary adds a third independent derivative; changes in its transition integrals cannot remove that rank. Finally the leading duration is tau0-s. Allowing s to vary adds an independent fourth derivative, while q3 remains positive after a sufficiently small variation.

Thus the endpoint map from(s,q1,q2,r) to(tau0-s,x0+A,y0+B,r) has rank4 at these paths. The inverse-function theorem gives a nonempty OPEN set of strict parameter endpoints. This set can be confined to C. It need not contain the original point; that is unnecessary below. Every chosen path, and every sufficiently small tube about it, has positive probability by Section3. For these tubes, no exit occurs before the chosen time s, so the stop used in Section2 equals s.

## 5. Proof of the no-interior-extremum theorem

Suppose u=ell(F) has a local minimum u0 at the initial point. Choose C inside its minimum neighborhood, so u>=u0 throughout C. For each sufficiently small deterministic terminal time s use the stopped process of Section2. By(2), its terminal value has expectation u0 and is at least u0 almost surely. It must therefore equal u0 almost surely.

If one of the endpoints in Section4 had u>u0, continuity would give a uniform path tube whose endpoint still has u>u0. The tube has positive probability, contradicting the almost-sure equality. Hence u=u0 on the nonempty open set of endpoints supplied by Section4.

Every coordinate of F is real analytic on the connected domain tau,x,y>0,0<g<1: ordinary coordinates are finite rational combinations of exponentials of durations, and the inheritance dependence is polynomial. The real-analytic identity theorem now gives u identically u0 on that domain. Replacing ell by-ell treats a local maximum. QED.

## 6. Exact use and non-use in the G3 gate

Consider a proposed linear nonnegative guard on the complete joint response. Suppose the guard is nonnegative under every local legal variation of one physical strict independent bigon and its positive leading gap, and vanishes at the current parameter choice. If the compiler is affine in the same PRIVATE natural cell kernel in every row, with all interventions confined to its fixed context, the guard is a linear functional of F plus a constant. The theorem forces it to vanish for EVERY strict four-parameter choice of this same cell, with the rest of the source fixed.

Thus such a guard cannot force this cell's inheritance/arm parameters into a proper finite alphabet, or any other proper subset detected by that nonconstant linear functional. This is a source-specific limitation on one proposed finite-alphabet forcing strategy; the abstract matrix examples do not have the required actual identity.

The premise of a genuine local minimum is essential. An all-pivot critical covector need only annihilate first derivatives. A bounded-index or positive-semidefinite Hessian on the COMPENSATED derivative kernel does not imply a local minimum on the four-dimensional cell domain. This theorem cannot be inserted into the earlier critical-fibre argument without establishing that missing premise.

Forcing this cell's own hybrid gives a direct negative control to an unqualified joint-row extension. Under force0 its kernel is E_(tau+x). With z=exp(-(tau+x)) and any fixed0<c<1, the linear combination of the two- and three-root no-merger coordinates z^3-3c^2*z has a nonconstant interior local minimum at z=c. Both tau and x can be positive there. That forced-row tuple does not obey(1), so the theorem does not cover it.

The theorem does not exclude nonlinear guards, extra ties, forced rows at this cell or observations outside the stated private affine single-use contract. It does not turn the mixture in(2) into a deterministic parameter solution. It gives neither compression of a countable ordered tail, a finite realizing-word bound, an all-source NO certificate nor a G3 impossibility theorem. The general coupled finite-strict-selection problem remains open.

## 7. Prior and verification boundary

The generator identity is independently accepted in INDEPENDENT-BIGON-GENERATOR-IDENTITY.md, final SHA3d7456530ea503725c5c9cc353af948ed0e07b1569883339d37a3a2a15f5abed, in this directory. Its proof already credits classical Kingman/Wright-Fisher/Bernstein duality.

The probability tools used here are classical: Ito's formula, bounded optional stopping, Cameron-Martin local path support and bounded-drift Girsanov equivalence. Primary Girsanov record checked4October2026: I.V.Girsanov, *On Transforming a Certain Class of Stochastic Processes by Absolutely Continuous Substitution of Measures*, Theory of Probability and its Applications5(3)(1960),285-301, https://doi.org/10.1137/1105027 ; the original Russian record and abstract are available at https://www.mathnet.ru/eng/tvp4837 .

The general degenerate-elliptic maximum-principle framework is classical; see J.-M.Bony, *Principe du maximum, inegalite de Harnack et unicite du probleme de Cauchy pour les operateurs elliptiques degeneres*, Annales de l'Institut Fourier19(1)(1969),277-304, https://doi.org/10.5802/aif.319 . Its introduction distinguishes drift-bracket hypoellipticity from the stronger diffusion-field bracket condition for a global maximum theorem. No inapplicable version of that theorem is imported here: Sections2-5 give the stopped-process/open-endpoint/analytic-continuation argument for this precise source family.

Historical priority of this particular corollary is unassessed. The underlying general principles are established prior work. No simulation, finite cap extrapolation or Lean verification supplies the all-cap statement.
