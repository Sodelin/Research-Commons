# Exact boundary of the contraction-energy obstruction

Contributor: Codex laplace_recovery lane, 14 October 2026.
**Hand-derived follow-through; independent review requested.**
The previous fixed-Hilbert-metric obstruction and the exact source quartet
formula are inherited. This note distinguishes individual PSD contractions,
smooth common energies, and genuinely available nonsmooth contractions.
It proves no finite INDEPENDENT forcing or exact-return theorem.

Let V be one finite complete labelled-forest space on nonempty inputs
(the isolated empty-input block may be omitted). Q is ordinary Kingman
evolution, P=lim_(t to infinity) exp(tQ) its completion projection, and Z
its absorbing one-root genealogy subspace. Every actual source kernel B
fixes Z pointwise. Use column vectors and retain every genealogy state.

## 1. Jointly faithful individually contractive PSD families are excluded

Suppose {M_j} is any family of positive semidefinite forms such that each
seminorm is contractive under B and under exp(tQ) for every t>=0.
The previous quotient-Hilbert argument applies separately to every j:

                     range(PB-P) subset ker M_j.

If the family is jointly faithful, meaning intersection_j ker M_j={0},
it follows that PB=P. Thus the strict fair equal-arm cell's nonzero
completed quartet contrast excludes ANY jointly faithful such family.

For a finite family the same conclusion follows by summing the forms:
M=sum_j M_j is positive-definite and contractive. In finite dimension,
an arbitrary jointly faithful family has a finite jointly faithful
subfamily, by successive dimension reduction of the common kernel.
The conclusion therefore is not evaded by adding infinitely many forms.

A finite family may also be permuted by each source operation while
obeying the corresponding individual inequalities: summing again gives
a common positive-definite contraction. This is different from merely
requiring the MAXIMUM of their energies to decrease. Section 3 gives
an explicit faithful counterexample to extending the obstruction to
that weaker requirement.

## 2. A differentiable common energy is also excluded

Let E:V->R be continuously differentiable, and suppose its restriction to
Z is strictly convex. Assume, for EVERY signed vector x in V,

    E(exp(tQ)x)<=E(x) for every t>=0,    E(Bx)<=E(x).          (1)

Then PB=P.

Proof. Continuity and the ordinary limit imply E(Px)<=E(x). Fix z in Z
and any y in V. Substitute x=z+u y into this inequality. Equality holds
at u=0. Since both signs of u are allowed, differentiation gives

    dE_z(P-I)y=0.

The same argument for B, using Bz=z, gives dE_z(B-I)y=0. Consequently

    dE_z(PB-P)y=0 for every z in Z and y in V.

If w=(PB-P)y were nonzero, it would lie in Z, and E(z+u w) would have
zero derivative for every real u. It would be constant on that line,
contradicting strict convexity on Z. Hence w=0. QED.

Global convexity away from Z is not needed for this implication. The
essential premises are differentiability at the absorbing vectors,
strict convexity along Z, and inequalities allowing both signed
perturbation directions there. A smooth strictly convex norm-squared
energy satisfies these regularity premises and is therefore impossible
for the nonordinary cell at issue.

The result must NOT be applied to an energy known to decrease only on
physical probability vectors. The absorbing probability face is on the
boundary of that simplex, so perturbations in a transient-state direction
cannot be taken with both signs. Section 3 exhibits exactly this escape.

## 3. A faithful finite maximum of PSD energies DOES work

The following is a source-valid counterexample to a broader no-go claim.
It also shows that strict convexity alone is insufficient.

For each forest state f let r_f>=1 be its current-root count. An actual
finite source kernel K is nonnegative, column-stochastic, and satisfies

    K_(f,h)>0 implies f=h OR r_f<r_h.                       (2)

Indeed any changed rooted forest has undergone at least one merger.
Routing alone does not change the uncoloured forest. This holds for
ordinary edges and for complete physical words, with any finite number
of cells and arbitrary admitted parameters.

For x in V put

    A(x)=sum_f r_f |x_f|,
    D_K(x)=sum_h |x_h| sum_f K_(f,h)(r_h-r_f)>=0.

The actual monotone-root coupling gives the exact inequalities

    A(Kx)<=A(x)-D_K(x),
    ||Kx-x||_1<=2 D_K(x),
    ||Kx||_1<=||x||_1.                                    (3)

The first follows by the triangle inequality and summing the weighted
columns. For the second,
`||K e_h-e_h||_1=2(1-K_(h,h))`, and every off-diagonal transition loses
at least one root. The third is ordinary stochastic contraction.

Since both Euclidean norms are at most ||x||_1,

    ||Kx||_2^2-||x||_2^2
      <=(||Kx||_2+||x||_2)||Kx-x||_2
      <=4 A(x) D_K(x).                                    (4)

For ANY fixed 0<eta<=1/4 define

                  E_eta(x)=A(x)^2+eta ||x||_2^2.            (5)

Because 0<=D_K(x)<=A(x), equations (3)--(4) give

    E_eta(Kx)-E_eta(x)
      <=-2 A D+D^2+4 eta A D
      <=-(1-4 eta) A D <=0.                               (6)

This is a common source contraction on the FULL signed vector space,
with constants independent of cell count and cap. The energy is strongly
convex: A^2 is convex and eta ||x||_2^2 has positive-definite Hessian.
It vanishes only at zero and discards no forest coordinate. It is
nondifferentiable in transverse directions at nonzero absorbing vectors,
so Section 2 does not apply.

Moreover it is the maximum of FINITELY MANY positive-definite quadratic
forms. For each sign vector sigma in {+1,-1}^dim(V), set

    v_sigma,f=sigma_f r_f,
    M_sigma=v_sigma v_sigma^T+eta I.

Then

    E_eta(x)=max_sigma x^T M_sigma x.                      (7)

Every M_sigma is positive-definite, but only their maximum is known to
contract. They cannot all contract separately, by Section 1. This is
an exact distinction between a faithful family of individual quadratic
Lyapunov forms and a faithful nonsmooth common envelope.

On the physical probability simplex, A(p)=sum_f r_f p_f is linear.
Thus the restriction of (5) is the smooth strongly convex polynomial

                    (sum_f r_f p_f)^2+eta sum_f p_f^2,      (8)

and (6) remains valid. Smoothness ONLY on the physical simplex therefore
does not supply the missing signed-direction premise of Section 2.

## 4. This evasion retains quartet information but is not a G4 guard

After completion every state has r=1. For an exchangeable quartet law
whose total balanced probability is a, (5) becomes

             1+eta [a^2/3+(1-a)^2/12].                    (9)

Ordinary completion has a=1/3. The fair equal-arm strict cell followed
by completion has a=1/3+delta, where
`delta=(1-exp(-t))^3/12>0` by the inherited exact formula. Its energy
exceeds the ordinary completed value by

                    eta [delta/9+5 delta^2/12]>0.          (10)

Thus the common contraction energy has not quotiented away this genealogy
difference. There is no contradiction: both evolutions dissipate energy
from the same fresh-root state, but to different final values. The
ordinary and cell paths need not have equal dissipation.

The loss in (6) charges mergers of EVERY kind, including ordinary
coalescence. It does not isolate extra reticulations or vanish along an
ordinary target path. Subtracting the target's ordinary dissipation has
no sign supplied by this proof. Nor does equality of one energy value
identify the full forest law. Consequently this construction is not the
sought nonnegative target defect controlling arbitrary weak insertions.
It marks the strongest justified boundary of the rejected method:

- Common individually contractive PSD forms cannot be jointly faithful.
- A globally differentiable common energy strictly convex on the absorbing
  genealogy subspace cannot preserve the needed topology variation.
- Faithful nonsmooth strictly convex envelopes, and smooth energies on
  the physical simplex alone, genuinely evade those obstructions.
- Their availability does not provide the original source-specific
  target equality case or finite INDEPENDENT certificate.

The exact observable positive route still needs a nonlinear inequality
whose equality case is tied to the target's complete physical law, with
all chronology and weak-cell counts controlled. Generic contraction is
not that inequality.

## Evidence and status

The linear-algebra obstruction is a continuation of
[the fixed-metric reset note](INDEPENDENT-ORTHOGONAL-RESET-DISSIPATION-OBSTRUCTION.md),
independently reviewed in
[ORTHOGONAL-RESET-DISSIPATION-SOL-REVIEW.md](../../whole-source/continuation-2110z/ORTHOGONAL-RESET-DISSIPATION-SOL-REVIEW.md).
The quartet value retains the original source theorem's attribution.
Equations (3)--(10) are direct finite-state hand calculations using the
actual merger-only support property; no test run or additional physical
observer was used. Historical novelty of these elementary norm
constructions has not been assessed. Original G4 remains open on the
finite INDEPENDENT branch.
