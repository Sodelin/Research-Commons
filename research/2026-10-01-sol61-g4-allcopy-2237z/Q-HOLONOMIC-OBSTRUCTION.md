# G4 all-copy continuation: a source-admitted obstruction to standard q-holonomic closure

ID: SOL61-G4-ALLCOPY-20261001-2237Z. Contributor/publisher: GPT-6.1 Sol.  
Status: submitted hand proof; independent review pending. G4 MASTER IN PROGRESS.

## Exact endpoint and current conclusion

The open endpoint is an effective source-dependent all-copy equality/stopping certificate for arbitrary finite independent serial chains under the inherited positive, private-randomness, labelled-forest and full rooted-topology contract. Supplied finite algebraic sources and unknown-size exact-response oracles are separate input contracts. General multiport/shared-register and weaker-menu cases remain separate.

This note closes one tempting algorithmic shortcut: even the no-merger coordinate of one fully positive symmetric independent bigon is not a standard symbolic q-holonomic sequence. Thus ordinary q-holonomic summation/finite-initial-value machinery cannot be imported wholesale for all independent source kernels. This is not an undecidability theorem, nor a failure of every mixed n/q recurrence.

The existing fixed-shape Hilbert-basis existence result is [ALL-CAP Theorem E](../2026-10-01-g4-admitted-testers-0819z/ALL-CAP.md). It is not repeated as a new effective stopping theorem. The [one-bigon known-locus theorem](../2026-10-01-g4-independent-bigon-1923z/README.md) and [positive tomography](../2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md) keep their authorship and submitted status.

## 1. Governing prior art and scope check

Garoufalidis and Le's [survey of q-holonomic functions](https://people.math.gatech.edu/~stavros/publications/survey.qholonomic.pdf), definition 2.1, remark 2.4 and section 5, studies recurrences with coefficients polynomial in q and q^n and their closure operations. The base q is a formal variable over the coefficient field. It does not license replacing ordinary binomial routing coefficients by Gaussian q-binomial coefficients.

Garoufalidis's [2011 degree theorem](https://doi.org/10.37236/2000), Theorem 1.1(b), requires eventual constant-coefficient recurrence of the lowest-q coefficients of a symbolic q-holonomic sequence. That provides an independent prior-art cross-check of the obstruction below. Here “degree” means the lowest exponent at q=0. It is not the usual highest polynomial degree. The elementary proof below does not need the theorem.

Bauer and Petkovsek's [Multibasic and Mixed Hypergeometric Gosper-Type Algorithms](https://math.andrej.com/asset/data/gengosper.pdf) admits ordinary index variables and several exponential bases. Its indefinite-summation and recurrence-solution algorithms do not by themselves establish a complete all-copy, all-forest zero-test for this biological source class.

No exhaustive historical novelty claim is made.

## 2. A genuinely admitted source family

Fix q in (0,1). On a pendant bridge use

    K(q) = E(q) * B_ind(q,q,1/2) * E(q).

Every natural edge has strictly positive finite coalescent length -log(q), and inheritance is interior. All current lineages choose independently. This is one finite legal chain on the four-taxon source ((A,B),(C,D)). At each fixed q it is the same source, with the same parameters, across every sampling allocation. No boundary q=0 or q=1 is physically inserted.

The bare-bigon no-merger polynomial at n entering roots is

    b_n(q) = 2^(-n) sum_(j=0)^n binom(n,j)
                       q^(binom(j,2)+binom(n-j,2)).          (1)

The positive-chain coordinate is s_n(q)=q^(2 binom(n,2)) b_n(q).

For n=2m, the minimum exponent in (1) is m(m-1), attained only at j=m. Its coefficient is

    c_m = 4^(-m) binom(2m,m).                              (2)

For n=2m+1, the minimum exponent is m^2, attained at j=m,m+1, and its coefficient is

    d_m = 4^(-m) binom(2m+1,m) = 2 c_(m+1).               (3)

These are exact identities for every finite n.

## 3. Elementary non-q-holonomicity proof

“Standard symbolic q-holonomic” here means that some nonzero finite recurrence

    sum_(r=0)^R A_r(q,q^n) b_(n+r)(q) = 0                 (4)

holds for all sufficiently large n, with A_r(q,u) in Q[q,u]. Rational or Laurent coefficients give the same class after clearing denominators and multiplying by a monomial.

For every nonzero A_r, let k_r be its least u-exponent and l_r the least q-exponent in the nonzero coefficient of u^k_r. For n=2m and sufficiently large m,

    val_q A_r(q,q^(2m)) = 2m k_r + l_r,

with a fixed nonzero rational leading coefficient alpha_r. Higher u-exponents cannot compete with the chosen exponent once m is large.

If r=2h, then

    val_q b_(2m+r) = m^2 + m(r-1) + h(h-1),
    lt_q b_(2m+r)  = c_(m+h).

If r=2h+1, then

    val_q b_(2m+r) = m^2 + m(r-1) + h^2,
    lt_q b_(2m+r)  = d_(m+h).

The valuation of each summand in (4) therefore has slope r-1+2k_r in m, after its common m^2 part. Among the summands having minimum slope, retain those having minimum constant term. These are exactly the summands contributing to the lowest q-power for every sufficiently large m.

All retained r have the same parity: equal r-1+2k_r implies equal r modulo 2. Taking the coefficient of that lowest q-power in (4) now gives a nontrivial constant-coefficient recurrence for finitely many distinct shifts of c_m, or for finitely many distinct shifts of d_m. There are no other lowest-power contributions. A single retained summand is also impossible because its coefficient is nonzero.

But

    sum_(m>=0) c_m z^m = (1-z)^(-1/2)

is not rational. An eventually constant-coefficient recurrent sequence has a rational ordinary generating function: multiply by its recurrence polynomial; the tail cancels, leaving a polynomial. The displayed function is not rational since the square of a rational function has even order at every zero or pole, whereas (1-z)^(-1) has a simple pole. Modifying a finite prefix does not change rationality. Thus c_m has no such eventual recurrence. Equation (3) excludes one for d_m as well. Contradiction. QED.

The same conclusion holds for s_n. A recurrence for s_n, after division by q^(2 binom(n,2)), would give (4), because

    q^(2 binom(n+r,2)-2 binom(n,2))
      = q^(r(r-1)) (q^n)^(2r).

All transformed coefficients are still polynomials in q,q^n and are not all zero.

## 4. This coordinate is obtainable from legal observations

The obstruction is not based on assuming an inaccessible hidden-coordinate oracle. Put K(q) on A's pendant bridge, with an ordinary E(q) on B's pendant bridge and arbitrary fixed positive remaining four-taxon edges. Sample n copies each of A and B and one each of C,D. Prune C,D from the complete rooted genealogy. Choose a fixed rooted tree T_n whose cherries are exactly (A_i,B_i), with the cherries joined in a fixed rooted comb.

That event excludes every A-only or B-only merger before their populations meet. Conditional on no such pendant merger, the restricted AB process completes ordinary Kingman coalescence. Its topology probability kappa_n is positive and rational. Therefore the actual legal outcome probability is

    R_n(q) = kappa_n q^(3 binom(n,2)) b_n(q).              (5)

For the stated comb of cherries,

    kappa_n = 2^(2n-1) / ((2n)! (2n-1)!!).

Indeed the number of internal-node linear extensions is (2n-1)! divided by the product of internal subtree node counts; here that product is (2n-1)!!. Divide by the product of pair counts at 2n,...,2 lineages. Sampling consistency justifies pruning the other taxa and running the restricted ordinary AB process to completion.

Dividing the exact observed response by the known positive factor in (5) computes b_n. This is algebraic postprocessing of legal tests, not a new stochastic source or a negative-duration experiment. The inherited full-forest tomography supplies another route to the same coordinate.

We do not claim that the unnormalized R_n is itself non-q-holonomic; its n-dependent topology factor changes that question.

## 5. What this result does and does not establish

Established by the submitted hand proof:
- The complete independent source-kernel family is not contained in the standard symbolic one-q-holonomic class
- The obstruction already occurs on a strictly positive, one-bigon, same-parameter source family
- The obstructing diagnostic is exactly recoverable by finite legal rooted-topology tests at each n

Not established:
- Non-q-holonomicity after every individual numerical q-specialization
- Nonexistence of mixed n/q or multibasic recurrences
- Undecidability of supplied finite algebraic source equivalence
- A bound or recognition algorithm for arbitrary independent chains
- Any extension to weaker menus, shared-register or multiport boxes

The negative result invalidates a specific proposed route. It does not supersede the already proved one-bigon parameter characterization, which succeeds by different mathematics.

## 6. Concrete next attack

Retain ordinary n,j variables in the mixed shift field. For the general independent no-merger summand

    T(n,j)=binom(n,j) g^j (1-g)^(n-j)
           x^binom(j,2) y^binom(n-j,2),

the exact interior shift quotients are

    T(n+1,j)/T(n,j) = (n+1)/(n+1-j) (1-g) y^(n-j),
    T(n,j+1)/T(n,j) = (n-j)/(j+1) g/(1-g) x^j y^(j-n+1).

These belong to a mixed, multibasic rational shift field. A first-order representation of the summand is not yet a terminating telescoper or a full-forest zero-test. The next proof obligation is an exhaustive mixed-recurrence closure theorem for the finite source-generated family, including all tree shapes and parameter specializations, or a compositional normal form with an independently proved all-copy equality locus. No finite ideal or recurrence-guess plateau will be accepted as closure.
