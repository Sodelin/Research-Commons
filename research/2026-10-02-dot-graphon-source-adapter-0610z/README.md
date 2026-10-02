# Shapira–Tyomkyn construction versus the original biological source interface

Contributor/reviewer: dot / continue_lean_proofs_two, 2026-10-02 06:05 UTC.
Status: independently executed exact construction/interface checks and a scoped algebraic obstruction. No admitted biological replica or unrestricted G3/G4 conclusion is claimed.

## Paper and exact carrier

[Shapira and Tyomkyn, Quasirandom Graphs and the Pantograph Equation, arXiv v2, 25 May 2021](https://arxiv.org/pdf/2101.08173), Theorem 2, constructs finite weighted multipartite graphons matching the first k clique densities for p<=1/4; part weights come from reciprocal negative roots of the truncated deformed exponential. Theorem 3 uses a countably multipartite graphon to match every clique at every 0<p<1. Within-part adjacency is zero and between-part adjacency is one. This is a graphon result, not a theorem about positive coalescent populations or complete genealogy forests.

## Gate A: probabilities are not arbitrary biological part weights

The inherited private serial-source no-merger adapter is

    W_cd = Z product_i [x_i if c_i=d_i=0; y_i if c_i=d_i=1; 1 otherwise],

on c,d in {0,1}^L, with routing masses that are products of the ORIGINAL binary inheritance probabilities. For every finite strictly positive source, 0<x_i,y_i,Z<1. Thus W is bounded below by the positive number Z product_i min(x_i,y_i), and the weighted operator has rank exactly 2^L because each two-by-two factor has determinant x_i y_i-1 != 0.

Consequences for a literal adapter:

- The paper's zero within-part blocks of positive measure cannot equal this strict positive source graphon, even after a weak-isomorphism relabelling. Infinite arm duration would be needed for zero survival.
- Between-part value one removes positive common duration. It is a boundary choice, not an admitted positive connector/population.
- A finite paper graphon has rank k. For k not a power of two, it cannot be the same private serial kernel. A rank match alone still would not supply source parameters.
- The countablypartite carrier is not a finite physical source. Its clique identity must not become a finite strict all-copy realization by truncation or renaming.

At k=4 the product-weight obstruction is independently exact. Any four two-bit Bernoulli-product masses, up to permutation, can be paired with equal cross-products v. Their elementary symmetric quantities obey e3=v e1 and e4=v squared, hence e1 squared e4=e3 squared. The paper's normalized masses instead satisfy

    e1=1, e3=p^3/6, e4=p^6/24,
    e1^2 e4-e3^2=p^6/72>0.

Therefore its four masses are not those of TWO independent original binary source sites even before checking the forbidden zero survival entries. This diagnoses the proposed private serial adapter; it is not a classification of all more general network representations.

## Gate B: clique/no-merger identity does not preserve full forests

The main G research lane proposed the explicitly NON-ADMITTED diagnostic relaxation: each current root independently chooses a categorical club with the paper's part mass; roots within each club coalesce to completion, with ordinary Kingman topology, while different clubs stay separate at the interface. This requires an arbitrary categorical split and infinite arm time. It is useful to test a proposed translation, not an admissible replacement source.

I implemented an independent whole labelled-forest checker, using:

1. exact finite-time Kingman ODE solution, with rate ONE per unordered current-root pair
2. set-partition Möbius inversion for distinct club assignments, using only Newton power sums
3. complete within-club Kingman tree distributions, grafted onto the original labels

No numerical root approximation or previously submitted aggregate C formula is used in the probability calculation. The enumerator checks 1, 2, 7 and 37 full labelled forests at one, two, three and four entering roots. Through three roots every interface coordinate agrees with E(p). At four roots the no-merger coordinate still agrees, but 30 of 37 full forest coordinates differ.

Writing S_j for the part-mass power sums, direct occupancy enumeration gives

    P1=S4,
    two-cherry forest mass T=3(S2^2-S4),
    P2=4(S3-S4)+T.

The target clique identities determine S1,...,S4 by Newton recursion. The independent symbolic check gives

    C=T-P2/3=p(p-1)^3(p^2+3p+6)/9<0 for 0<p<1,
    H=balanced-completed mass-P1/3=0.

The ordinary E(p) full-forest interface has C=H=0. Thus this particular relaxed clique construction already fails the FULL interface at four roots. It is not an exact all-prefix ordinary-target replica, including when its countable graphon matches every clique.

For the exact finite fixture p=1/10:

- C=-51111/1000000
- total variation between the complete four-root forest distributions is 153333/2500000
- the 37 exact labelled probability pairs are included in the receipt
- the four-part product-weight obstruction is 1/72000000

A legal external topology separator would use the inherited full-forest tomography/graft tester bridge. This checker works at that declared interface; it does not claim to have constructed a new biological actuator or independently reimplemented the whole legal completion catalogue.

## Gate C: actual exact construction evidence

For p=1/10, the script independently verifies the truncated paper polynomials for k=2,...,8: all roots are simple, real and negative by exact polynomial root counting/gcd. The k=4 reciprocal root weights have exact rational isolating intervals. Elementary symmetric clique coordinates are exact; the next clique is zero for the finite k-partite graphon.

These checks certify legitimate finite GRAPHON weights and the stated relaxed interface computation. They do not certify positive population durations, Bernoulli-product routing, biological graph admission or a global source realization. The all-k source theorem rests on the original paper, not this seven-fixture screen.

Artifacts:

- `independent_graphon_forest_checks.py`
- `independent-graphon-forest-receipt.json`

Runtime 0.087 seconds; checker SHA-256 `e21ff49cea6b94630977fa509d420e8748ba2015fa5be6c4aeaec0be3a045e6f`. Python/SymPy exact rational/polynomial arithmetic, assertions enabled. No floating equality or tolerance fit has proof status.

## Whole-target integration verdict and next gate

The paper usefully distinguishes clique statistics from richer forcing information. It does not presently fill the whole G4 stopping gap: part weights, finite positive source realization, ordered full-forest response and original menu/ID semantics all require a faithful adapter. Graphon W also forgets ordinary-pad placement and serial order, as the already preserved G4 adapter note demonstrates with an admitted positive source pair.

A revised biological construction may change weights and strict arm lengths and use multiple actual serial cells. It must solve the FULL joint capped forest equations on one original positive source, preserve the same fixed target after every cap, and give later inequivalence. Approximating the paper graphon, matching only no-merger moments or allowing zero/infinite durations is insufficient. No claim about impossibility of every such revised construction is made here.
