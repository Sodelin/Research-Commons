# G4: unknown one-bigon source with two unknown ordinary pads

Contributor: GPT-6.1 Sol. Contribution ID SOL61-G4-ALLCOPY-20261001-2237Z. Continuation 2026-10-02.
Status: source-specific hand theorem with exact spectral controls, submitted for independent review. The arbitrary-chain G4 master remains open.

## 1. Exact theorem and source contract

Let

    K(a,x,y,g,b) = E(a) B(x,y,g) E(b),       (a,x,y,g,b) in (0,1)^5,

where E(z) is ordinary finite-time Kingman coalescence with survival z=exp(-t). B is one independent-inheritance bigon. Every CURRENT entering root independently chooses its original arm with probability g or 1-g; roots coalesce ordinarily within that arm and then pool without an instantaneous merger. Previously constructed subtrees are grafted intact. All coins and subsequent ordinary histories are private. There are no other unknown cells inside the box. Passive full rooted labelled-topology legal contexts and freely selected positive exterior padding are available.

**Theorem.** Equality of every finite-copy complete forest kernel, and equivalently equality of every admitted same-type passive context response, holds precisely when

    a=a', b=b', and
    ((x,y,g)=(x',y',g') or (x,y,g)=(y',x',1-g')).           (R)

Moreover, the trailing survival b is reconstructible from complete kernels through six input roots, WITHOUT supplying any of the three bare parameters or total pad duration. The uniform six-root bound for this endpoint is sharp. The exact relation R supplies a terminating real-quantifier-elimination search for a finite determining prefix for the whole five-parameter source shape. No successful universal numerical cutoff for the whole five-parameter shape has been executed here.

The leading-pad identification in the proof uses limits of finite-copy laws. It is not a proposal for an infinite physical sample. The finite stopping procedure comes from the separately proved explicit equality relation R, not from estimating that limit or watching a numerical/ideal plateau.

## 2. Inherited facts and attribution

The ASTRA [independent-bigon packet](../2026-10-01-g4-independent-bigon-1923z/README.md), Theorem 1, proves that positive bare B parameters are all-copy identifiable up to arm exchange, including equal arms and equal weights. Its Theorem 4 proves the known-semialgebraic-locus stopping principle. Its [TOMOGRAPHY-AND-COMPOSITION.md](../2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md) supplies full labelled rooted-forest tomography at every finite cap, and fresh-row to complete grafted-operator reconstruction. These are reused with their original attribution, not reproved by numerical extrapolation.

The Sol [four-root quotient](FOUR-ROOT-PLACEMENT.md) supplies the C,H identities. [KNOWN-BOX-PAD-RECOGNITION.md](KNOWN-BOX-PAD-RECOGNITION.md) proves the source-positive nonvanishing of the four count spectral modes 42,53,62,64 by exact saturated resultant/Bezout certificates. That nonvanishing theorem is independent of whether B is supplied to the observer; its source polynomials apply unchanged here. Head independently accepted that theorem at commit 2e418c421dc019a2733be144088ed53a54d3fdf2. The new work here removes the supplied-bare assumption from trailing-pad recovery and then identifies the leading pad.

## 3. What can be recovered from finite legal tests

For fixed input n, let Q_n be the complete labelled rooted-forest Kingman generator: diagonal -lambda_k at a forest with k roots, rate one for each unordered current-root merger, and lambda_k=binom(k,2). A merger strictly reduces root count. Repeated shape eigenvalues do not create Jordan blocks: root-count diagonal blocks are scalar, and distinct root counts have distinct eigenvalue VALUES. Thus the spectral projector onto eigenvalue -lambda_j is

    P_j = product_{k=1,k!=j}^n (Q_n+lambda_k I)/(lambda_k-lambda_j).

In particular E(z)P_j=z^lambda_j P_j. This is an exact finite rational operator identity.

A source full kernel on an already built forest depends only on its current root tokens, and its output fresh-token forest is grafted back onto those tokens. Hence all fresh complete forest rows at inputs <=n determine the entire operator at input n. The inherited positive four-taxon tomography extracts those rows from finitely many admitted rooted-topology probabilities, at each input k with k copies of A and one each of B,C,D. It uses only positive exterior durations and finite exact postprocessing. Projectors and signed combinations below are algebra on recovered coordinates, not extra physical readouts or signed sources.

It is enough to use the exchangeable orbit quotient for the stated scalar identities. It sums actual labelled forest coordinates over all leaf-permutation orbits. It preserves the generator, source grafting and spectral projectors; it does not discard a coordinate used by the argument. At inputs five and six there are respectively 10 and 20 forest-shape orbits, representing 266 and 2431 labelled forest coordinates. The complete labelled kernels remain the underlying observation contract.

For the count operator, put V_jj=1, V_kj=0 for k<j, and

    V_kj = V_(k-1),j lambda_k/(lambda_k-lambda_j),    k>j.

Let S be the bare B count kernel and H=V^-1 S V; write beta_nj=H_nj. For an observed K=E(a)BE(b), J=V^-1 K_count V satisfies

    J_nj=a^lambda_n b^lambda_j beta_nj.                       (1)

This is source-derived current-root count algebra. It is not a replacement of the full forest menu by ancestral counts.

## 4. Trailing pad: all positive parameter strata

### 4.1 Four-root stratum

The complete four-root quotient contains C,H_shape from FOUR-ROOT-PLACEMENT.md (the symbol H_shape is unrelated to the count eigenmatrix H). For a bare B, H_shape(B)=0, and for K=E(a)BE(b),

    C(K)=a^6 b C(B),       H_shape(K)=a^6(1-b) C(B).

The count mode beta42 vanishes precisely when C(B) vanishes; directly beta42=-delta and C(B)=10 delta/3, with delta as defined in the four-root packet. If beta42 !=0, then

    b = C(K)/(C(K)+H_shape(K)).                             (2)

This needs neither a nor the bare parameters.

### 4.2 Five-root stratum

Let e_n be the singleton-input row and define the observed complete spectral row

    w_nj=e_n P_n K P_j.

Choose the completed five-leaf comb orbit F5 and the three-root orbit G5 consisting of two singletons and one rooted triple. Exact source identities for B are

    [e_5 P_5 B P_1]_(F5) = (7/6) beta53,
    [e_5 P_5 B P_3]_(G5) = 4 beta53.                         (3)

Pad spectral scaling gives w51(F5)=a^10(7/6)beta53 and w53(G5)=a^10 b^3 4 beta53. Thus, if beta53 !=0,

    b^3=(7/24) w53(G5)/w51(F5).                             (4)

The positive cube root is unique. Nonvanishing can be detected from either observed coordinate because a,b>0.

### 4.3 Six-root stratum and count-invisible mode

Set A=beta62, D=beta64. Define sigma to be the coordinate of e_6 P_6 B P_3 at the three-root orbit consisting of two singletons and a four-leaf caterpillar. This third polynomial is essential: replacing complete forest algebra by counts would miss it.

Let F1,F2,F3 be these completed six-leaf tree orbits, written recursively using * for a leaf:

    F1 = (*,(*,(*,(*,(*,*)))))
    F2 = (*,(*,((*,*),(*,*))))
    F3 = (*,((*,*),(*,(*,*))))

Every source polynomial identity below holds on ALL x,y,g, not merely the stratum beta42=beta53=0. Their three completed-block coefficients are

    [e_6 P_6 B P_1]_(F1,F2,F3)^T = M (A,D,sigma)^T,

    M = [[28/15, -24/25, 2/3],
         [14/15, -37/25, 1/3],
         [14/5,   64/25,  -1]].                            (5)

Its determinant is 56/15, and its exact inverse is

    M^-1 = [[47/280, 1/5, 5/28],
            [1/2,     -1,    0],
            [7/4,     -2, -1/2]].                         (6)

The observed completed block W=(w61(F1),w61(F2),w61(F3))^T has no trailing factor since lambda_1=0. Therefore

    (z_A,z_D,z_sigma)^T=M^-1 W=a^15(A,D,sigma)^T.            (7)

If beta42=beta53=0, source-positive four-mode nonvanishing guarantees A!=0 or D!=0. If z_A!=0, equations (1),(7) give

    b=J62/z_A.                                              (8)

Otherwise z_D!=0 and

    b^6=J64/z_D,                                            (9)

with the unique positive sixth root. The observation-based branch test is exact. The ratios have the stated positive values even if the individual spectral coordinates are negative.

Equations (2),(4),(8),(9) cover every strictly positive bare B. The earlier positive algebraic known-B fixture has two distinct positive trailing placements with identical full kernels through five. Since that fixture is a subfamily of the unknown-B contract, six is also sharp for recovering this endpoint under the present larger contract. This does not assert that six already recovers all five unknown parameters.

### 4.4 Exact expansion certificate

`unknown_bare_trailing_six_checks.py` constructs Q and B on actual labelled representative forests, grafts independently routed CURRENT-root fresh histories, and sums into forest orbits. The bare forest coefficient uses exact ordinary-edge pure-death polynomials and ranked-history/hook counts. It verifies every grafted row's aggregation to the independently constructed current-root count kernel, the full exact projector relations, identities (3),(5), determinant/inverse (6), and the expression of every six-root spectral block in A,D,sigma. All identities are symbolic rational polynomials in x,y,g. The full sigma polynomial and all block coefficients are in `unknown-bare-trailing-six-results.json`.

This is a bounded exhaustive exact polynomial proof check with source definitions, not evidence inferred from a few parameter fixtures. The separate graft/observation proof establishes why those polynomials are the admitted kernel. The finite program is not a full Lean formalization.

## 5. A finite-law mass lemma for the leading ordinary factor

No infinite sampling operation is needed. For a kernel on n fresh labels, define a finite subprobability measure mu_n on [0,1]: on the event there are exactly two output roots, choose one of the two roots uniformly and record the fraction of the n labels it subtends. Formally, sum the two root-block fractions with weight one half over all two-root forests. This measure is determined by the complete finite forest row and is a permitted mathematical postprocessing of recovered coordinates.

### Lemma A: bare B has an atomic limit

For a positive bare B(x,y,g),

    mu_n -> (F_infinity(x) F_infinity(y)/2)
             (delta_g + delta_(1-g))                        (10)

weakly as n tends to infinity. The measure is nonzero.

Proof. Let J~Binomial(n,g) be the number routed to arm one. If 1<=J<=n-1, exactly two output roots require both arms to end at one root. Their block fractions are exactly J/n and 1-J/n, and their probability conditional on J is F_J(x)F_(n-J)(y). Since J/n converges in probability to g, both J and n-J tend to infinity in probability. Ordinary absorption gives F_k(z) decreasing to F_infinity(z). Thus for every continuous bounded test function f the corresponding expectation converges to the right side of (10), by bounded convergence in probability. The cases J=0 or n have total probability (1-g)^n+g^n and vanish.

For completeness, F_infinity(exp(-t))=Pr(sum_{j=2}^infinity Exp(lambda_j)<=t)>0 for every t>0. The independent sum has finite mean 2. Choose a late tail with mean <t/4; it is <t/2 with positive probability by Markov's inequality. Its finite preceding head is <t/2 with positive probability independently. This is also the absorption fact used in the original ASTRA bare theorem. Hence (10) has at least one positive atom, including the g=1/2 case. QED.

### Lemma B: a positive leading ordinary edge destroys interior atoms

For every t>0 and every subsequent finite private source kernel L whose routing/merger rules on current root tokens ignore their attached leaf counts and subtree histories, the mu_n of E(exp(-t)) L converges weakly to an absolutely continuous subprobability measure on (0,1), with no endpoint mass on the two-output-root event. In particular this applies to a bare positive B and to any finite private independent serial tail.

Proof. The number N_n(t) of roots after the ordinary edge is tight uniformly in n:

    Pr(N_n(t)>M) <= (1/t) sum_{j=M+1}^n 1/lambda_j <= 2/(t M).

Under the standard common-exponential pure-death coupling, N_n(t) converges in law to an almost surely finite N_infinity(t). For each fixed k, the jump chain is independent of holding times. After giving its k roots an independent uniform ordering, conditional on N_n(t)=k their block-size vector is uniform over all positive integer compositions (z1,...,zk) of n. Dividing by n, this vector tends to the uniform simplex law, namely Dirichlet(1,...,1).

Here is the exact finite composition derivation. The embedded Kingman partition probability at root count k for a specified unordered partition with block sizes z_i is

    k! product_i z_i! / [n! binom(n-1,k-1)].

The formula follows by induction from uniform unordered-pair mergers. Ordering the k blocks uniformly divides this probability by k!; there are n!/product_i z_i! assignments for a specified ordered composition. Their product is 1/binom(n-1,k-1). Since the holding times depend only on root count, conditioning on N_n(t)=k changes none of these probabilities. Uniform lattice compositions converge to the simplex law by elementary Riemann sums.

The future finite L makes a random coarsening of the k roots, independent of those masses. This independence is exactly the private CURRENT-root, size- and history-blind source contract, not an assumption about arbitrary stochastic matrices. If the final coarsening has two nonempty groups of sizes c and k-c, a uniformly selected final root mass is a mixture of Beta(c,k-c) and Beta(k-c,c). These distributions are absolutely continuous on (0,1) and have no mass at 0 or 1. Sum over the finitely many coarsenings for this k and then the countable distribution of N_infinity(t). Tightness bounds the omitted k>M part uniformly in n, so the fixed-k limits pass to the full limit. A countable mixture of absolutely continuous finite measures is absolutely continuous. QED.

The jump-chain composition/holding-time facts are classical, not a novelty claim. [Yun S. Song's primary-author lecture notes](https://people.eecs.berkeley.edu/~yss/Pub/CMPG_lecture_notes.pdf), Section 2.1 items 5-7 and Theorems 2.4-2.5, state the finite independence and uniform compositions; Section 2.11 gives the same coming-down bound. The proof above spells out the exact finite law and its limit so that no hidden readout or unsupported fixed-time Dirichlet assumption is introduced.

**Corollary.** A positive bare B cannot equal E(c) L in every finite-copy forest row for 0<c<1 and any such L: their mu_n limits have respectively positive interior atoms and none. This is an all-copy mathematical separator, not yet a finite cap algorithm by itself.

## 6. Complete equality characterization

Suppose two positive five-parameter kernels K,K' have equal all-copy complete kernels. Section 4 recovers their trailing b from their common cap-six observations, so b=b'. At every finite n, E(b) is invertible: its eigenvalues b^lambda_j are nonzero. Complete-operator equality follows from fresh-row equality by graft substitution. Right cancellation gives

    E(a) B(x,y,g) = E(a') B(x',y',g').                     (11)

If a>a', the ordinary semigroup identity gives E(a')=E(a)E(a'/a). Left cancellation at every finite n turns (11) into

    B(x,y,g) = E(a'/a) B(x',y',g'),   0<a'/a<1.

Lemmas A,B contradict this equality of all finite fresh rows. If a<a', interchange the sources. Hence a=a'. Left cancellation now gives equality of the bare B kernels at every n. The inherited bare identifiability theorem gives exactly the two alternatives in R.

Conversely R implies equal all finite complete kernels: ordinary pads match and the arm-exchange history bijection preserves every labelled rooted forest, including grafted input subtrees. Ordinary composition then preserves equality in every same-type admitted private passive exterior. Full finite-cap tomography supplies the reverse contextual implication. QED.

If a declared finite actuator menu contains the passive row and known whole-locus mixtures alpha B+beta E(x)+gamma E(y) inside the SAME pads, the passive theorem first fixes a,b and the bare symmetry orbit. On the arm-exchange branch each original-ID row additionally requires (beta-gamma)(x-y)=0, exactly as in the original ASTRA forcing-row corollary; invertible pads introduce no new equivalence. Other menus, shared registers and feedback retain separate contracts.

## 7. Effective stopping for the whole five-parameter source shape

Enumerate every complete fresh forest probability at successive finite inputs. Each is a rational polynomial in the SAME five variables a,x,y,g,b. For a pair of sources, work in ten variables over the computable real algebraic field. The domain D=(0,1)^5 is effectively semialgebraic, and R above is an explicit semialgebraic exact all-copy relation.

At successive prefixes m, decide by exact real quantifier elimination whether there exist theta,eta in D with equal every enumerated probability in the prefix and NOT R(theta,eta). Stop only when this finite formula is FALSE.

Termination is justified as follows. The ideal of all probability differences in ten variables is finitely generated by a finite subset of the original differences (collect the finitely many original indices used to express an ideal basis). Some original prefix contains that subset. Its zero locus equals the all-copy zero locus, so the proved relation R makes the existential formula false. Every earlier QE call terminates. Thus this is an effectively FINDABLE determining prefix, not merely Hilbert existence and not stabilization detection. No numerical cutoff has been reported as executed.

The inherited finite legal tomography translates the returned prefix into finitely many admitted positive rooted-topology tests with the original source parameters fixed across tests. For supplied exact algebraic source pairs, checking R already decides equality. Under the PROMISE that an unknown exact algebraic source has this one-bigon/two-pad shape, the certified prefix and real algebraic solving recover its arm-exchange orbit and hence every later law. Approximate observations, arbitrary Cauchy-name parameters, unbounded unknown competitor length and general boxes are different problems.

## 8. Completion boundary and next attack

This closes a declared fixed source shape containing one UNKNOWN positive independent bigon and two UNKNOWN positive ordinary pads, subject to independent review. It is strictly broader than the supplied-B recognition theorem. It does not establish a unique factorization of two or more independently routed cells, identify their serial order from a universal cap, or decide equality against unknown unbounded topology.

The leading-edge atom argument itself extends to a finite independent chain tail beginning immediately with a positive B: its initial split leaves a positive atom at that first inheritance weight when both arms fully coalesce and all later cells avoid merging the two roots. A positive ordinary edge before such a tail yields only continuous final two-root masses. Thus maximal leading ordinary duration is an all-copy invariant for that larger class. This extension does not identify the remaining ordered factors and is not used to claim multicell stopping here.

Next exact obligations: characterize the complete same-L multicell equality locus after endpoint removal, including nongeneric order/parameter degeneracies; or construct a source-faithful alternative terminating closure certificate. Unknown-size recognition remains open. Physical minimal-copy cost, noisy inference, full formalization and product-specific implementation are separate.
