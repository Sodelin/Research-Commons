# One genuinely nonabelian test: the splitting field of x³−2

**Status:** proved classical reduction, obstruction to a simple Dirichlet substitution, and sufficient analytic milestone. Exact arithmetic fixtures were run; no new GRH case, zero calculation, or Lean build.

## The factor that remains

Let E = Q(∛2), F = Q(√−3), and K = EF. Eisenstein at 2 and nonsquare discriminant −108 give G = Gal(K/Q) = S₃. F is fixed by A₃ and E by a point stabilizer. Write 1, ε, ρ for trivial, sign, and two-dimensional standard representations. Their characters on identity, transposition, and 3-cycle are (1,1,1), (1,−1,1), and (2,0,−1), respectively. The three-point permutation representation is 1⊕ρ, the two-point representation G/A₃ is 1⊕ε, and the regular representation is 1⊕ε⊕ρ⊕ρ. Artin formalism gives:

    ζ_E(s) = ζ(s) L(s,ρ)
    ζ_F(s) = ζ(s) L(s,χ₋₃)
    ζ_K(s) = ζ(s) L(s,χ₋₃) L(s,ρ)^2.

For either nontrivial character ψ of A₃, the character of Ind ψ is ψ+ψ⁻¹ on A₃ and 0 on its complement. It equals ρ. Induction and class field reciprocity identify L(s,ρ) with the L-function of a nontrivial order-three Hecke character of **F**, not a Dirichlet character of **Q**. Its holomorphy and functional equation are classical. The factors have no poles inside the critical strip, so their zeros cannot cancel. Given Dirichlet GRH, RH for ζ_K or ζ_E is equivalent to RH for this one degree-two factor.

| Frobenius at p≥5 | χ₋₃(p) | Inverse Artin Euler factor, T=p⁻ˢ | Inverse ζ_E factor | Inverse ζ_K factor |
|---|---:|---|---|---|
| Identity | +1 | (1−T)² | (1−T)³ | (1−T)⁶ |
| Transposition | −1 | (1−T)(1+T) | (1−T)(1−T²) | (1−T²)³ |
| 3-cycle | +1 | 1+T+T² | 1−T³ | (1−T³)² |

At 2 and 3 the cubic field is totally ramified (Eisenstein for x³−2 and (x−1)³−2 respectively). Inertia in K/Q therefore contains A₃, and ρ has no A₃-invariants: its inverse factor is 1 at either prime. At 2, F is inert, so K has (e,f,g)=(3,2,1); at 3 both E and F ramify, so K has (6,1,1). This checks the bad factors too. The two local Eisenstein uniformizers generate maximal local orders; the polynomial discriminant has no other prime factors, so disc(E)=−108. Applying the conductor–discriminant formula to 1⊕ρ gives cond(ρ)=108.

## Why regrouping Dirichlet factors does not reach it

**Proposition.** No finite product or ratio of Dirichlet L-functions equals L(s,ρ) after changing finitely many Euler factors. Take a common modulus M of all putative factors. Their product has the same inverse Euler polynomial or rational function (1−T)^k at every good p≡1 mod M. But K∩Q(ζ_M) is abelian over Q, hence fixed by the commutator A₃. The identity and a 3-cycle of G can each be paired with the identity on Q(ζ_M) to give actual automorphisms of the compositum. Unconditional Chebotarev gives infinitely many primes in each resulting conjugacy class. Both sets are 1 mod M, but their Artin factors differ. Equality would force equality of local factors by uniqueness of absolutely convergent Dirichlet-series coefficients. This rules out a particular proof shortcut, not every possible implication from Dirichlet GRH.

Concrete example: 7 and 31 are both 1 mod 3. The cubic has no root modulo 7, but has roots 4, 7, and 20 modulo 31. Their sign character agrees; their standard character does not.

## One precise analytic milestone

Write θ_split(X) for the sum of log p over unramified p≤X with the cubic split completely, and θ₁(X) for the analogous sum over p≡1 mod 3. For p≥5 the trace coefficient of ρ is

    a_p = 3 · 1_{splits completely} − 1_{p≡1 mod 3}.

The one new bound **θ_split(X) = X/6 + O_ε(X^(1/2+ε))** for every ε>0 and all sufficiently large X would suffice. Dirichlet GRH already gives θ₁(X)=X/2+O(√X log²X) at fixed modulus 3. Thus S(X)=Σ_{p≤X} a_p log p=O_ε(X^(1/2+ε)). For Re(s)>1, partial summation gives Σ_p a_p log p·p^(−s)=s∫₁^∞ S(X) X^(−s−1)dX. The bound extends this integral holomorphically to Re(s)>1/2. The higher-prime-power part of −L′/L converges absolutely and locally uniformly there since |tr ρ(g^k)|≤2 and k≥2. Therefore −L′/L has no poles there, excluding zeros of L; functional-equation symmetry excludes the left side. This is a conditional reduction, not a proof of the estimate or a transfer of the Dirichlet one-sided window theorem.

## Source scope and prior work

- The [original Lean endpoint](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/original/src/Main.lean) exports RH and Dirichlet statements. In the [refactored endpoint](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean), UpperTheory.EveryCharacter explicitly quantifies over DirichletCharacter ℂ N; [MainConclusion.lean](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean) reaches it via every_character_of_literature_of_vWin and vwin_of_row. Hecke and automorphic ingredients inside the proof do not expand the verified target domain. [MIT verification report](https://math.mit.edu/~drew/grh/) separately confirms this scope. These are source inspections, not a new kernel build.
- Lagarias and Odlyzko, [On computing Artin L-functions in the critical strip](https://doi.org/10.1090/S0025-5718-1979-0528062-9) (1979), treat the pure-cubic case via imaginary-quadratic ring class characters and finite computations. The [LMFDB Artin record](https://www.lmfdb.org/ArtinRepresentation/2.108.3t2.b.a) gives conductor 108; the [L-function record](https://www.lmfdb.org/L/2/108/3.2/c0/0/0) lists its weight-one form, local factors and finite zero data. A targeted search did not find an independent all-height result for this factor. No claim of novelty for the reductions.
- Next milestone: isolate a genuinely analytic estimate for the split primes or cubic Hecke character, then check whether the existing arithmetic-to-ceiling machinery can supply it over F. In parallel, formalize the ordinary factorization identities as bridge lemmas rather than claiming their missing analytic premise.

## Exact replay

Run python3 -B rh_nonabelian/check_s3.py. It checks the character and Euler identities for all six permutations, the displayed ramified-factor products, and consistency of cubic root enumeration with a separate power-residue check for all 166 unramified primes below 1000. It does not compute zeros or verify the analytic milestone.

For a closer analogue of the original proof, see [the one-sided smoothed milestone](ONE-SIDED-MILESTONE.md): the positive eta product proves real-axis zero-freeness, so an all-large one-sided ceiling suffices by Landau. The ceiling remains to be proved.
