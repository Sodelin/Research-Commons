# Chronology review of the meromorphic finite-persistence proof

Reviewer: Codex chronology subagent, 2026-10-13. **Scoped hand acceptance**
of the lead researcher's
[MEROMORPHIC-FINITE-PERSISTENCE.md](MEROMORPHIC-FINITE-PERSISTENCE.md),
SHA256 `2a02c32ee1961f2391d1e380baa73349fb6d225dae8bd2442ec676db2138bf2f`. The reviewer
contributed the companion Carlson estimate and discussed the analytic
strategy with the author; this is an independent audit within that team,
not an external referee report.

The theorem as stated is correct: an exact all-integer equality between a
finite product of the specified cell functions and a countable product with
summable clocks and squared log odds forces the countable family to be
finite. No energy bound, chronological first cell, or positivity of the
Mellin density is needed. No computational or formal verification was
performed.

## Meromorphic continuation and the uniform cusp estimate

The substitution `x=cos^2(theta/2)` has Jacobian
`dtheta=-dx/sqrt(x(1-x))`, and evenness doubles the integral. Thus the
normalization of the displayed Mellin density is correct. Near zero,
`theta=pi-2 arcsin(sqrt x)`. Since the heat density is even about `pi`, its
composition is analytic in `x`; the square-root branching cancels. Near
`x=1` the heat density is likewise analytic after the angle substitution,
and only the stated integrable factor remains. Finite Taylor subtraction
therefore gives precisely the simple possible poles at negative
half-integers, with the stated residues.

The small-cell argument remains valid on compact sets with negative real
parts. In the central interval the cosine stays away from zero, so its
complex logarithm and all powers indexed by a fixed compact set are
uniformly bounded. The expansion differs from one by
`O_C(theta^2+h^2)`; a possible mixed `theta h` term is absorbed by that
bound. The central Gaussian second moment is at most `2t`, and the omitted
mass and cut-edge terms are exponentially small.

For the complementary interval, one can indeed choose a fixed complex
neighborhood of `[0,1/2]` with the stated angle bounds. At zero both local
angle branches remain near `pi`; elsewhere continuity on the compact real
interval suffices. The two branches give the same heat-density value.
The real distance of every angle from a Gaussian center is at least `r/2`,
whereas the absolute imaginary displacement after adding either `ih` is
at most `r/4`. Consequently the square in the Gaussian exponent has a
uniform positive real gap, at least `3r^2/16`. Summing the image terms
preserves an estimate of the form `C t^(-1/2) exp(-c/t)`.

Cauchy estimates on nested fixed neighborhoods then control every finite
number of density derivatives required for Taylor subtraction. This does
not require `h/t` or `h^2/t` to be bounded. Taylor's integral remainder
controls the full real segment even when the Taylor series itself has a
smaller convergence radius. On a compact set away from the pole lattice,
the finitely many displayed rational denominators are bounded away from
zero, and the remaining integral is uniformly integrable. This proves
the claimed `O_C(t+h^2)` estimate after continuation.

## The exceptional theta zero

I checked the normalization against the classical theta4 product in
[DLMF 20.5.4](https://dlmf.nist.gov/20.5.E4). For real `h`, exactly one
factor vanishes at each `h=(2j+1)t`; all remaining factors are nonzero and
their tail product converges to a nonzero value. Each zero is therefore
simple in `h`.

At such a zero, differentiating the identity along the fixed odd-integer
curve `h=st` gives `partial_t H=-s partial_h H`, which is nonzero. The
Fourier heat equation is valid termwise and says
`partial_t H=partial_theta^2 H`. Hence the second angle derivative is
nonzero. The substitutions give `a_0=2H(pi)` and, when this vanishes,
`a_1=4H''(pi)`. Thus the first genuine pole is always `-1/2` or `-3/2`.
There is no unresolved exceptional parameter locus beyond those two cases.

## Products, zeros, and the contradiction

The source budgets and the uniform off-pole estimate make the product
converge locally uniformly on the connected plane with the negative
half-integers removed. Removing any one factor still leaves a normally
convergent product, so a zero of that factor at a point off the pole lattice
is a zero of the complete product. Possible zero factors do not compromise
convergence. Its value at zero is exactly one.

For an infinite subsequence sharing a genuine pole `p` among the first two
possible locations, small circles centered at `p` have no other poles.
Uniform convergence of each single-cell function to one on such a circle
makes Rouché applicable to `(z-p)U_i` and `z-p`. The resulting zero is not
`p`, because the residue there is nonzero. Using arbitrarily smaller
circles shows the zeros approach `p`, and they must contain infinitely
many distinct points. Each propagates to the complete product.

The reviewed Carlson bridge licenses the integer-to-function identity;
the identity theorem extends it over the punctured plane. A finite target
product is meromorphic at `p` with finite pole order. Multiplication by
a sufficiently high fixed power of `z-p` makes it holomorphic there.
The propagated zeros then contradict its being nonzero. This proves the
stated finite-persistence conclusion.

## Applicability and master boundary

The inherited diagonal/resource identity supplies the exact summable
hypotheses, including cancellation of the weak-clock term. Complex arities
and zeros are tools in the compactness proof; they are not additional legal
observations or separately chosen source parameters.

The reviewed mixed-target global implication can therefore use this
finite-persistence theorem to obtain existential finite legal-cap forcing
for every finite strict calibrated equal-arm private BOTH target in its
stated rival class. An explicit cap bound, an INDEPENDENT-only local
theorem, and the original whole-core observation/transfer obligation are
separate. This review does not claim those conclusions or general G4
closure.
