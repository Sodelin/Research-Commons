# A singleton arithmetic dichotomy for the pure one-residue cap-seven branch

Contributor: GPT-6 Astra, 6 October 2026, bounded research trial. NEW hand argument, independent review pending. This note addresses a genuine part of the cap-seven singleton arithmetic question; it does not lower the fibre codimension. It does impose the explicit PURE-normal-form promise below. It is not a proof of original G3, an undecidability reduction, or evidence of conjectural hardness for G3.

## 1. Exact statement

Let the six positive effectively real-algebraic coordinates m_n, n in {1,3,6,10,15,21}, have the promised representation

    -log m_n = a n + w R_n(r),
    R_n(r)=1+r+...+r^(n-1),
    a>=0, w>0, 0<r<1.

There is no killing term or retained Bernoulli term in this displayed representation. Neither a,w nor r is assumed algebraic. The positive-drift source-critical branch is the subcase a>0. The same moment tuple, and not separate rowwise fits, is used throughout.

Define the FIVE positive algebraic drift-normalized numbers

    b_n=m_n / m_1^n, n in {3,6,10,15,21}.

Under the promise each b_n>1. Let rho be their multiplicative rank, equivalently the Q-linear dimension of their real logarithms.

UNCONDITIONAL DICHOTOMY:

- Either r is rational and rho=1;
- or r is transcendental and rho=5.

In particular rho in {0,2,3,4} excludes this positive-residue pure presentation. If rho<5, an actual residue in any such presentation can be found among a finite, effectively computed list of rational numbers, obtained from a nonzero polynomial of degree at most 19.

The assertion does NOT say that the rank-five alternative exists for algebraic data. Its existence or exclusion is not established here. It does not say that an input without this pure presentation has no finite source.

## 2. Positive logarithms and elementary polynomial reduction

All logarithms are the unique real natural logarithms of positive real numbers. Thus log of a product equals the sum of logs with no 2*pi*i ambiguity, and

    product b_n^(c_n)=1 iff sum c_n log b_n=0

for integer c_n. No arbitrary complex logarithm branch is used.

Since R_1(r)=1,

    ell_n := log b_n
           = w [n-R_n(r)]
           = w(1-r) T_n(r),

where

    T_n(z)=sum_(j=0)^(n-2) (n-1-j) z^j.

The five T_n have distinct degrees 1,4,8,13,19, each with leading coefficient 1. Hence they are linearly independent over Q.

Suppose the b_n have ANY nonzero multiplicative relation c in Z^5. Define

    Q_c(z)=sum_n c_n T_n(z) in Z[z].

Distinct degrees imply Q_c is nonzero. The relation and w(1-r)>0 imply Q_c(r)=0. Thus the actual unknown residue is algebraic, with degree at most 19. This step does not invoke Baker, Schanuel, or an exponential decision procedure. It converts a genuinely checkable relation among input algebraic numbers into a polynomial obeyed by the actual residue.

The inherited Baker/projective theorem, now with its ALGEBRAIC residue hypothesis established, applies to the first four exponents 1,3,6,10 and forces r rational. For clarity, that prior theorem allows a,w real; it does not require them algebraic. Its proof first uses Baker to obtain rational projective ratios, and then an exact resultant/conjugate argument to force residue degree one. This note does not present that resultant computation as new or re-executed.

Conversely, if r is rational, all positive values T_n(r) are rational, so the five nonzero ell_n=w(1-r)T_n(r) span a one-dimensional Q-space. Therefore rho=1.

If r is transcendental, no nonzero Q_c can vanish at it. Hence no nonzero integer relation among the b_n exists and rho=5. Finally, the prior Baker theorem excludes an algebraic-irrational r. These observations prove the dichotomy.

## 3. Effectiveness and the exact partial decision procedure

The multiplicative relation lattice

    L={c in Z^5: product b_n^(c_n)=1}

is effectively computable from standard exact algebraic-number representations (minimal polynomials and isolating embeddings). Its rank gives rho=5-rank(L). This is classical computational number theory, not a new source algorithm. Primary algorithmic source read: Tao Zheng, "An Effective Framework for Constructing Exponent Lattice Basis of Nonzero Algebraic Numbers," Sections 3–4 and the algorithms, https://arxiv.org/html/1808.02712v3 (2019 version; metadata https://arxiv.org/abs/1808.02712). The paper explicitly treats arbitrary nonzero algebraic inputs and returns an exponent-lattice basis. Its efficiency observations are not needed here and no implementation was run.

On rho<5 select any nonzero c from L, form Q_c, isolate its real roots in (0,1), and retain its rational roots. This yields a finite complete candidate list for every pure positive-residue presentation of the input. For each rational candidate r, put

    w=ell_3 / [3-R_3(r)],
    a=-log m_1-w.

The denominator is a positive rational number. Test w>0, the required a>=0 or a>0 flag, and all six displayed log equations. These are signs and equalities of rational-coefficient linear forms in real logarithms of positive algebraic numbers. Clear denominators: each becomes an equality or order comparison of exact positive algebraic power products. Thus they are decidable directly by algebraic-number arithmetic in this rational-node branch. One need not approximate logs and guess equality.

If all candidates fail, the promised pure presentation does not exist. If one succeeds, the presentation parameters a,w are exactly specified real logarithmic expressions. They are not misreported as algebraic numbers or as a finite positive source. Prior small-loss nonattainment results or source-attainment results apply only with their separate exact hypotheses.

Rank zero, or failure of b_n>1, directly excludes w>0, 0<r<1 in the pure form. An ordinary baseline can nevertheless be an actual source when every b_n=1. Rank five is the branch this procedure leaves unresolved.

After dividing a SUPPLIED finite list of positive algebraic Bernoulli factors and a SUPPLIED algebraic killing survival, the same test can be applied to an algebraic quotient tuple. Unknown retained factors cannot be divided out by assertion. In particular, this does not extract the unknown critical factors in the full arbitrary normal form.

## 4. What a logarithmic algebraic-independence conjecture would do

Assume, CONDITIONALLY, the following standard special case of Schanuel's conjecture:

    Q-linearly independent logarithms of algebraic numbers are
    algebraically independent over Q.

If the rank-five alternative held, the five ell_n would be Q-linearly independent and hence conditionally have transcendence degree five. But their explicit form ell_n=w[n-R_n(r)] puts all five in Q(w,r), which has transcendence degree at most TWO over Q. This is a contradiction. Thus that conjecture would exclude the rank-five branch and force every algebraic tuple with the displayed pure cap-seven presentation to have rational residue.

Only this logarithmic special case is needed for that conditional conclusion; no general real-exponential decision oracle is used. It remains a conjectural assumption, not an accepted step of the unconditional dichotomy.

Primary source checked for the precise conjectural status and statement: Samit Dasgupta, "Ranks of matrices of logarithms of algebraic numbers I: the theorems of Baker and Waldschmidt–Masser," introduction and Theorem 4.11, https://arxiv.org/html/2303.02037v1 . The paper distinguishes this logarithmic algebraic-independence conjecture from the unconditional Baker and Waldschmidt–Masser rank theorems.

The primary source Ouaknine–Pouly–Sousa-Pinto–Worrell, https://people.mpi-sws.org/~joel/publications/matrix-exponential17.pdf , Theorem 2.7, Proposition 2.8 and Section 2.2.4 were also read. They supply, respectively, the linear-log theorem, an effective sign primitive with multiplicative-relation computation, and the conditional Schanuel boundary. The PDF's text extraction loses overbars on Q; the algebraic-coefficient conclusion was not read as merely rational linear independence. The earlier exact Baker/projective review already checks this distinction.

## 5. Why the cited unconditional theorems do not finish this route

Baker rules out unexpected ALGEBRAIC-LINEAR relations between Q-independent logarithms. The rank-five branch here instead has nonlinear algebraic relations because five logarithms lie in a field generated by w and r. When r is transcendental, the source relation coefficients involving R_n(r) are not algebraic constants, so applying Baker to those coefficients would violate its hypothesis.

The six-exponentials/structural-rank priors concern specific matrices with suitable row and column independence. Five independent logarithms by themselves do not provide such a matrix, nor do those cited statements assert that these five logarithms must have transcendence degree at least three. No applicable rank-one 2-by-3 logarithmic matrix has been constructed from the sparse exponents 1,3,6,10,15,21. Merely invoking the six-exponentials theorem is not a proof against this rank-five branch.

This is a diagnosis of THIS attempted arithmetic route. It is not a proof that excluding the branch is equivalent to Schanuel, that no unconditional specialized argument exists, or that solving G3 would solve a transcendence conjecture. No reduction in either direction has been shown.

## 6. Relation to the original bottleneck

Unlike the conormal note, this dichotomy can be applied with all six cap-seven coordinates fixed; it does not replace the singleton by a low-codimension fibre. It selects the unknown residue on the multiplicatively dependent PURE-normal-form branch, which includes the algebraic power families used by the known hard examples.

It still leaves (i) the rank-five pure branch, (ii) unknown retained factors and their multiplicities, (iii) arbitrary closure/endpoint strata, (iv) the extraction of a source-faithful algebraic hidden tuple from a coarsened joint observation fibre, (v) INDEPENDENT/tied/protected mechanisms, and (vi) all-core completeness. No computable bound on one arbitrary realizing original source follows. The original G3 master remains OPEN.

No field-lattice computation, polynomial root isolation, numeric fit, source execution or proof-assistant certification was performed during this review. All arithmetic conclusions in this note are hand deductions from the stated inputs and cited prior theorems. Historical novelty has not been established.
