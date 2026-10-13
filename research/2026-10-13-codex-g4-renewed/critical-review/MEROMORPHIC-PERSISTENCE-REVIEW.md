# Independent review: meromorphic finite persistence

Reviewer: Codex critical-review lane, 13 October 2026. This is an independent
hand audit within the collaborating research team, not external refereeing
or formal verification.

## Frozen submission and verdict

Reviewed [MEROMORPHIC-FINITE-PERSISTENCE.md](../chronology/continuation-1837z/MEROMORPHIC-FINITE-PERSISTENCE.md),
SHA256 `2a02c32ee1961f2391d1e380baa73349fb6d225dae8bd2442ec676db2138bf2f`.
The companion Carlson bridge has the separate
[critical review](CARLSON-BRIDGE-REVIEW.md).

**Hand acceptance of the stated analytic theorem.** Equality at every
nonnegative integer between a finite target product and a countable strict
cell product, under the two stated summable budgets, forces the latter
family to be finite. No assumption of finite total squared bias divided by
duration enters the proof. This verdict does not on its own assert an
original-source observation theorem.

## Checks of the decisive steps

The change of variable `x=cos(theta/2)^2` gives exactly
`U(z)=integral_0^1 x^(z-1/2) a(x) dx`, including the factor 2 in `a`.
Evenness of the periodic heat density about pi removes the square-root
branch at zero. The endpoint at one has only an integrable square-root
factor, and contributes an entire function of z after a cutoff away from
zero. Finite Taylor subtraction therefore gives only simple possible
poles at the negative half integers, with the displayed Taylor coefficients
as residues. Also `U(0)=1` follows from the zero Fourier coefficient.

The off-lattice small-cell estimate was checked independently, including
negative real parts of z. On the central interval, the contour shift avoids
all zeros of the cosine. Its analytic logarithm is uniformly bounded on
the fixed smaller rectangle for z in a compact set. The estimate
`cos((theta-ih)/2)^(2z)-1=O(theta^2+h^2)` follows from its quadratic zero at
`theta-ih=0` and compactness. The wrapped Gaussian central second moment is
at most the unwrapped second moment: wrapping cannot increase absolute
distance to zero. Central vertical edges remain at a fixed positive real
distance from every Gaussian center, so their exponentially small estimate
is uniform for all sufficiently small absolute h, independently of h^2/t.

For the complementary integral, one fixed complex neighborhood of
`[0,1/2]` can be chosen with both local angle branches close to the real
arc from pi/2 to pi (or its reflected arc). Near zero both branches remain
near pi and their composition agrees by evenness. The specified lower
bound on real distance to every Gaussian center and upper bound on
imaginary distance yield `exp(-c/t)` on that neighborhood. The analytic
factor `(1-x)^(-1/2)` stays bounded. Cauchy estimates then bound the required
finite derivatives on a smaller neighborhood. Taylor's integral remainder
on the real segment is sufficient; no unwarranted Taylor convergence up
to x=1/2 is needed. The continued Mellin denominators are bounded away from
zero on the chosen compact set off the pole lattice. This proves the
uniform `O_C(t+h^2)` estimate used for the infinite product.

Consequently summability gives locally uniform absolute convergence of
the product tails on the connected punctured plane. Removing any one
finite factor leaves a locally convergent holomorphic product. A zero of
that factor off the pole lattice is therefore a zero of the full product;
there is no pole of another factor there to cancel it.

The theta4 product has exactly the stated real zeros `h=s t`, with s a
nonzero odd integer. At each such point exactly one factor vanishes,
simply in h, and the remaining tail product is nonzero. Differentiating the
zero curve gives a nonzero time derivative, and the heat equation converts
it to a nonzero second theta derivative at pi. The expansion then gives
`a_1=4 H''(pi)`. Thus every strict cell has a genuine simple pole at either
`-1/2` or `-3/2`, including every exceptional theta zero. No unexamined
possibility of cancellation of both first poles remains.

The reviewed Carlson theorem first extends the integer equality to the
right half-plane. The identity theorem and normal convergence extend it
to the whole connected complement of the pole lattice. If infinitely
many cells occur, their duration and absolute bias both tend to zero.
One of the two first-pole locations occurs infinitely often. On a fixed
small circle about that point the corresponding single-cell functions
tend uniformly to 1. Rouché applied to `(z-p) U_i(z)` gives one zero in
the disk. The nonzero residue excludes p itself. Shrinking the circle
shows these zeros approach p, and uniform convergence on compact sets
away from p forces infinitely many of them to be distinct. Every such
zero propagates to the infinite product and hence to the finite target
product. A finite product is meromorphic at p with finite pole order and
is not identically zero because its value at zero is 1. Multiplication by
a fixed power of `z-p` gives the stated contradiction to isolated zeros.

## Source and novelty boundaries

The analytic theorem needs only the summable duration and squared-bias
budgets and the exact integer product identities. The separate source
composition must supply these from one common-clock carrier, not from
independently fitted rows. The checked inherited residual identity does
so for calibrated equal-arm private BOTH carriers. Complex arities and
complex zeros are proof devices and are not additional legal observations.

The classical theta product, heat equation, Mellin continuation, Carlson
uniqueness, Rouché and identity theorem are reused tools. The application
and estimates are the claimed contribution; this review does not certify
historical novelty. No computational experiment, Lean proof, or Rust
verification was used to establish this acceptance.
