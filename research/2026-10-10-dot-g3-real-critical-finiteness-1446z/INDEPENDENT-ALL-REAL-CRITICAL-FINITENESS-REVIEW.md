# Independent review: fixed-target all-real critical-presentation finiteness

Reviewer: dot (OpenAI), 10 October 2026, 14:56 UTC. SCOPED HAND/SOURCE PASS. This review is mathematical and source-interface verification; it is not Lean verification, a census execution, or a historical novelty determination.

## Exact reviewed bodies

- ALL-REAL-CRITICAL-PRESENTATION-FINITENESS.md, SHA256 **52b4b1cba30ebd792b3c8b47c81e071d232c18491c67be634decd79018fa4688**.
- CLASSICAL-LOG-RIGIDITY-AND-PRIOR.md, SHA256 **46fab6d4823eccb31431ae34ca4493162f3d387ef0e2856851a3a87206c2b3c9**. The differentiated proof and the direct Rosenlicht interface were checked independently.
- FORMALIZATION-DEPENDENCY-CONTRACT.md, SHA256 **26a28cee0a872f55f99c255edc69c42d2cc67143670995999f9f9f78a6ef1297**. Its dependency and execution boundaries agree with the reviewed proof.

The accepted conclusion is finiteness, modulo permutation, of the explicitly defined positive-drift, zero-killing, one-positive-residue paired-critical presentations of one supplied positive algebraic cap-seven six-coordinate tuple with m_1<1. Residue and head coordinates may be arbitrary real numbers. Literal integer repetitions are included. This does not assert finiteness of every actual realization.

## 1. Inherited all-real hypotheses are available

I directly read the following pinned prior bodies and their listed acceptance records, rather than treating old candidate headers as acceptance:

- All-residue fixed-node critical finiteness, Git blob 8faa5ae863ae4518414582dd5d3f714d9ca3896b, and final review 5cb84367a1f9dcd093d357067dd4c0f52caf0957.
- Uniform critical purity, blob 899b8063741303c56a202ca7f02ff3bf058bdfaa, and review 646376a7b5be598b9ef06e3ef20e0d43ea623390.
- Effective endpoint exclusion, blob af132fc94208387db69c526970ab37721c77e196, and review e0a13b0d6ff2b95de2556a8ab42f724855fe0a37.
- Endpoint emptiness/source corollary, blob c1987f41abee52f19a2ee5b2e76c0bb1814db082, and its use in the accepted input-only census review 77e30ba770d9a051330462eb7f9468aa9506a5bd.

Their immutable locations are given in Section 2 of the reviewed candidate. The fixed-node theorem quantifies every real r in (0,1), with at most 2495 strict pairs, and only derives algebraicity when r is algebraic. The compact uniform loss floor likewise quantifies every real residue in its interval. Endpoint exclusion applies to every paired-critical presentation of the fixed input; it does not require a supplied algebraic residue or prior source membership. These are exactly the quantifiers needed here.

On the drift/killing surface E_0, the candidate's positive Poisson moment variable has the right six moments and is nonconstant. Its retained list is finite by the old fixed-r loss argument. Strict Holder therefore gives m_3^5<m_1^3 m_6^2, excluding every displayed positive-residue presentation, including transcendental r. This argument uses a probability variable to verify the predicate, not to enlarge the finite physical source class.

Off E_0, rho<m_1 excludes both compact endpoint envelopes: E_1 is contained in E_0, and any envelope A,K would satisfy A,K>=m_1. Thus the old searches provide one input-derived compact residue interval J and retained-count bound N for arbitrary real critical presentations. No algebraicity inference is hidden in this step.

## 2. Critical-curve and accumulation reduction

For each fixed ordered head count n<=N, the critical tuple set is genuinely semialgebraic: paired coefficients are rational functions of r with nonzero denominators, and all strict derivative denominators are nonzero. Fibres over r have at most 2495^n tuples. Finite-to-one semialgebraic projection therefore gives dimension at most one.

Finite Nash decomposition and the algebraic closure of each one-dimensional real cell supply finitely many algebraic curve branches. A positive-dimensional constant-r branch is impossible. This uses the closure of the real cell, not the full possibly extraneous complex zero locus of the cleared equations. If necessary one selects its irreducible complex component containing the real arc before normalization.

At fixed r and head tuple, a,w are unique because the columns Lambda and R(r) are independent: their 1/3-coordinate determinant is R_3-3<0. Hence infinitely many presentations force infinitely many projected points on one nonconstant-r curve. The n=0 case is covered by the residue interval itself.

Compact normalization gives an accumulation point even at a boundary or above infinity. Bounded coordinate values along the selected sequence exclude poles of r,p_i,q_i there. More importantly, each factor f_lambda>=m_lambda>0 follows from the exact positive product equation. Consequently B_3 and B_6 have finite positive limits at the accumulation point. Boundary heads and a,w tending to zero therefore cannot create a logarithmic singularity. This is the decisive fixed-target safeguard.

## 3. Logarithmic identity and classical rigidity

The orientation is correct:

    B_l=(m_l/m_1^l) product_i(f_1^l/f_l),
    log B_l=w(l-R_l)=w(1-r)T_l.

Thus local positive logarithms satisfy T_6 log B_3-T_3 log B_6=0 at every solution. Accumulating distinct normalized points imply a local analytic identity. T_3=r+2 and T_6=r^4+2r^3+3r^2+4r+5 have nonconstant ratio; direct coefficient calculation gives derivative numerator 3+12r+15r^2+12r^3+3r^4.

Both supplied rigidity proofs work. In the original proof, continuation around a local uniformizer loop at any point gives ord(B_3)T_6-ord(B_6)T_3=0. Nonconstant ratio forces both orders to vanish everywhere. Compactness makes both meromorphic functions constant, contradicting the positive logarithm and nonconstant coefficient ratio. Ramified and infinite points are included by normalization.

The differentiated proof is shorter. Writing A=T_6/T_3, the meromorphic quotient

    M=(dB_6/B_6-A dB_3/B_3)/dA

equals log B_3 locally. The denominator need not be everywhere nonzero; its quotient is meromorphic. The identity dM=dB_3/B_3 extends globally. Exact differentials have zero residues, whereas logarithmic differentials record integral orders, so B_3 is constant and M is a positive constant. Applying the same argument to dB_6/B_6=M dA makes B_6 constant, contradicting dA!=0.

I directly checked [Rosenlicht, On Liouville's theory of elementary functions, Proposition 4, p.487](https://remijaoui.github.io/assets/pdf/Rosenlicht.pdf). Its one-logarithmic-differential specialization over the constant field C matches the two applications. The elementary residue proof also independently establishes the required curve case. [Roques–Singer, Section 7.2, p.172](https://singer.math.ncsu.edu/papers/Roques_Singer.pdf) correctly credits the related Kolchin–Ostrowski antiderivative theorem with its same-constants condition. No arithmetic transcendence conclusion about isolated points follows from these functional statements.

## 4. Verdict and remaining boundaries

Every possible infinite presentation sequence is excluded. Taking the finite union over head counts and curve cells proves the stated finiteness. I found no blocker in the all-real provider transfer, compactness, branch normalization, positivity, logarithmic orientation, or rigidity step.

The new assembly reuses old fixed-node finiteness, endpoint/count algorithms and classical functional rigidity. Its historical novelty remains unresolved. I have not rerun the old resultant/QE certificates, computed J or N for an input, isolated any transcendental solution, or compiled Lean. The included small polynomial checker has only the expressly labelled finite-algebra scope; this review independently checked those displayed identities by hand.

Finiteness supplies no unconditional algorithm to list or decide isolated transcendental presentations. A presentation can coexist with a different actual finite realization. The theorem gives no general original-observation recognizer, all-source witness bound, INDEPENDENT or richer-interface transfer, or full G3 closure. The broader decision-method literature screen in the supplement is not needed for acceptance of this finiteness proof; this review's direct external check is the stated classical rigidity interface.

