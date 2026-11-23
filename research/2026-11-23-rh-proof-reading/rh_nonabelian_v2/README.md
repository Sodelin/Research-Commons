# An exact compact-window criterion for the cubic Artin factor

**Status:** conditional classical reduction with exact finite rational fixtures. Not Lean-compiled; no prime-distribution hypothesis established, no new RH proof, and no assertion of priority. The source inspection below is separate from the proof and the fixtures.

Let `K` split `x³−2`, and let `ρ` be the standard two-dimensional irreducible representation of its Galois group `S₃`. Write `L(s)=L(s,ρ)`, `D(s)=−L′(s)/L(s)`, and let `c(p^k)=log(p) tr(ρ(Frobₚ)^k)` at primes other than 2 and 3. Set `c(n)=0` otherwise. At 2 and 3 the inertia-invariant subspace vanishes; this is why no bad-prime term has to be added. For Re(s)>1, `D(s)=Σ c(n)n^(−s)` absolutely.

## The one missing estimate

Fix **one** real r>1, for example r=2. Use the nonnegative continuous weight

- Wᵣ(u)=r(1−1/u) for 1≤u≤r;
- Wᵣ(u)=r²/u−1 for r≤u≤r²;
- Wᵣ(u)=0 elsewhere (u>0).

Put Bᵣ(X)=Σₙ c(n) Wᵣ(n/X). If, for every ε>0, there is an eventual upper bound Bᵣ(X)≤Cε X^(1/2+ε), then the standard Artin factor is zero-free on Re(s)>1/2 and its nontrivial zeros lie on the critical line. An eventual lower bound Bᵣ(X)≥−Cε X^(1/2+ε) works equally well. “Eventual” means for **all** real X above the threshold, or equivalently all sufficiently large **integer** X by the next paragraph. Infinitely many isolated X, sparse sampled windows, or a fixed-height zero check are insufficient for this proof. This is a multiplicative window of fixed relative width; it does not prove any shrinking-width or sparse-window criterion.

For the integer variant, take m=⌊X⌋. The globally Lipschitz weight Wᵣ changes by only Oᵣ(1/m) at each n that can contribute at either X or m: such n satisfy m≤n≤r²(m+1), and |n/X−n/m|≤n/m². There are Oᵣ(m) such n and |c(n)|≤2log(n), so |Bᵣ(X)−Bᵣ(m)|≪ᵣlog(m), absorbed by the same power bound. This lets the arithmetic obligation be stated on integers without conceding sparsity.

### Why the cutoff really is local

Let A(X)=Σₙ c(n)(X/n−1)₊. Exactly,
`Bᵣ(X)=A(r²X)−(1+r)A(rX)+rA(X)`.
For n≤X both the slope and constant cancel. For X<n≤rX the surviving coefficient is r(1−X/n), and for rX<n≤r²X it is r²X/n−1. This combination cancels the linear centering term from the earlier global criterion automatically.

Using the full positive half-line, the initial Mellin transform is
`∫₀∞ Bᵣ(X) X^(−s−1) dX = D(s) Mᵣ(s)`,
where
`Mᵣ(s)=∫₁^(r²) Wᵣ(u)u^(s−1)du = (r^s−1)(r^s−r)/(s(s−1))`.
Indeed substitution u=n/X and absolute convergence justify the interchange for Re(s)>1. The factor can also be obtained by multiplying the Mellin transform of A by the three dilation factors. Mᵣ is entire; its values at 0 and 1 after removal are respectively (r−1)log r and r(r−1)log r. Every other zero is on Re(s)=0 or Re(s)=1. In particular it does not cancel poles within 0<Re(s)<1.

### No hidden analytic bound on the continued logarithmic derivative

The identified weight-one form is f(z)=η(6z)η(18z), [LMFDB 108.1.c.a](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/108/1/c/a/). For y>0 each eta factor is positive, and eta inversion gives f(iy)=(√108 y)⁻¹ f(i/(108y)). Thus the Mellin integral of f(iy) converges locally uniformly for all complex s and is strictly positive for real s. In the region of absolute convergence it equals (2π)^(−s)Γ(s)L(s), and therefore gives analytic continuation, the functional symmetry s↔1−s for the completed function, and L(s)>0 for real s>0. Any zero in the open strip is a pole of D with nonzero residue equal to minus its multiplicity. To cover possible points on Re(s)=1 without importing boundary nonvanishing, use a **pair** of fixed windows (r=2 and r=3, with the same side of bound not required). Their nonreal zeros on Re(s)=1 do not intersect: the equality 2πk/log 2=2πl/log 3 implies 3^k=2^l and hence k=l=0. Alternatively for the single-window claim, use classical Dedekind-zeta nonvanishing on Re(s)=1 (e.g. de la Vallée Poussin's argument from its nonnegative prime-ideal logarithmic coefficients), then Artin factorization ζ_K=ζ L(χ₋₃)L²; at s=1 the Artin factor is already positive. No vertical-line growth estimate is required for this argument.

Fix θ=1/2+ε<1. Choose X₀ such that g(X)=Cε X^θ−Bᵣ(X) is nonnegative on X≥X₀. Its initial transform for Re(s)>1 equals
`Cε X₀^(θ−s)/(s−θ) − D(s)Mᵣ(s) + E(s)`,
where E is entire because the discarded portion of Bᵣ is supported in the compact interval [1/r²,X₀]. For the lower bound use g(X)=Cε X^θ+Bᵣ(X). The transform is holomorphic on the real axis to the right of θ because D has no positive-real poles. If a zero inside θ<Re(s)<1 existed, the same meromorphic function would have a pole there, so the abscissa of absolute convergence of the g-transform could not lie to its left. For a nonnegative g with finite abscissa a, its transform must have a real singularity at a. To see this, if it continued through a, choose a real s₀>a close enough that its Taylor disk extends to a real s<a. The Taylor expansion at s₀ of the transform evaluated at s₀−z has nonnegative coefficients for real z≥0 (differentiate under the integral at s₀, after taking X₀≥1); Tonelli's theorem then gives convergence of the original integral to the left of a, a contradiction. Thus the hypothesized pole cannot exist. Let ε tend to zero and apply the functional equation to the other half of the strip.

### What the published Dirichlet theorem already buys

At unramified primes the trace is 3·1_{p splits completely in K}−1_{p≡1 mod 3}; this follows from the three conjugacy classes of S₃ and the sign map. Prime powers k≥2 contribute at most Oᵣ(√X log²X) by trivial counting and uniformly bounded traces and weights. Dirichlet GRH provides the fixed-progression prime number theorem for p≡1 mod 3. Partial summation against the bounded-variation weight gives
`Σ_{p≡1 mod3} log p Wᵣ(p/X)= X Mᵣ(1)/2 + O_{r,ε}(X^(1/2+ε))`.
Thus the conditional upper-bound hypothesis amounts to
`Σ_{p split in K} log p Wᵣ(p/X) ≤ X Mᵣ(1)/6 + O_{r,ε}(X^(1/2+ε))`.
The missing ingredient is one-sided control for the nonabelian splitting class. A two-sided ordinary Chebotarev estimate is stronger than what this reduction needs, but deriving even this ceiling is not done here. No claim is made that existing methods cannot prove it.

## What can and cannot be imported from the Lean proof

The published source uses [MainConclusion](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean) to obtain its Dirichlet-only endpoint through [every_character_of_literature_of_vWin](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean) and [vwin_of_row](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean). The actual [VWin definition](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean) quantifies over a `PChar`; `VWinAt` chooses an interval [Y,Y²] and `VAt` bounds cohomological lengths in fields satisfying `IsChiField`, a condition explicitly requiring embedding in a cyclotomic field over ℚ. Our S₃ field K cannot meet that field predicate: every subfield of a cyclotomic Galois extension of ℚ is itself abelian and Galois. Split primes are not determined by a choice of rational cyclotomic residue data. The weighted prime window here is **not** Lean's cohomology window, and the source provides no direct instantiation by changing the character type. No claim is made that another component of the Lean strategy cannot generalize.

Recommended narrow formalization: start with an independent statement of the compact Mellin/Landau lemma with abstract log-derivative and explicit continuation inputs; formalize the finite-sum weighting, then identify which existing analysis libraries support the Mellin continuation and nonnegative-transform boundary lemma. Independently formalize the coefficient factorization for this K. Do not formalize the proposed ceiling as an axiom and report it as a result.

## Verification

Run `python3 -B rh_nonabelian_v2/check_kernel.py | diff -u rh_nonabelian_v2/REPLAY.txt -` from the repository root. Fixtures only, using exact fractions. They check support, positivity, two piecewise formulas against three-kernel dilation, and rational Mellin moment identities on the fixed sample. They are not a proof of the complex multiplier or a test of the missing asymptotic bound.
