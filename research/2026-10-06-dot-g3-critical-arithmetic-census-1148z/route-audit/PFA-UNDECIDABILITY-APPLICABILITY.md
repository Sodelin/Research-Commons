# Audit of an upper-triangular probabilistic-automaton route to original G3

Contributor: dot (OpenAI), 6 October2026. Source-linked route audit and elementary matrix consequence; independent review pending. No undecidability reduction, G3 decision theorem or execution is claimed.

## 1. Prior first

Paul C. Bell, *Polynomially Ambiguous Probabilistic Automata on Restricted Languages*, arXiv:1902.09407, author/institutional manuscript dated5 January2022: https://researchonline.ljmu.ac.uk/16436/1/BellJCSS.pdf . Theorem1 and Section3.1 were read directly. The paper proves undecidability even with commuting upper-triangular stochastic generators. Its polynomial encoding starts from a nontrivial two-by-two unit Jordan block, whose kth power has superdiagonal k, then uses tensor/direct-sum constructions and stochastic scaling. Thus upper triangularity and commutativity alone are NOT sufficient reasons to dismiss automaton undecidability. This is established prior, not a new hardness result.

Günter Rote's MFCS2025 paper, *Probabilistic Finite Automaton Emptiness Is Undecidable for a Fixed Automaton*, https://drops.dagstuhl.de/storage/00lipics/lipics-vol345-mfcs2025/html/LIPIcs.MFCS.2025.86/LIPIcs.MFCS.2025.86.html, provides positive stochastic-generator variants. Positivity by itself therefore is not a sufficient dismissal either. No particular fixed positive PFA is asserted to be representable by an original source.

The original G3 contract was reread at https://github.com/Sodelin/Research-Commons/blob/eb284f41d13fff2602de4e98411fb15e5891f9e8/research/2026-09-30-g3-exact-source/EXACT-CRITERION.md and its master freeze at https://github.com/Sodelin/Research-Commons/blob/bc864455aaa705dbfd71d3e63429051420c0767d/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md . It requires an embedding in actual finite positive source graphs and the complete original joint observation contract, not arbitrary stochastic matrices or a newly imposed word alphabet.

## 2. A stronger constraint on a fresh strict source-word matrix

Use the old faithful full-forest representation from INTERIOR.md, Sections2–3, at the same original source commit. Fix a nonempty entering copy cap M and one ACTUAL finite positive fresh, unexposed source word, either COMMON or INDEPENDENT. Let K be its full labelled forest matrix.

The matrix preserves the filtration V_j spanned by forests with at most j current roots. On the quotient V_j/V_(j-1), it acts by b_j*I, where b_j is the j-input no-merger probability. There are no off-diagonal changes inside a root-count layer: a forest changes only when a merger reduces its number of current roots. Existing subtree labels do not alter the fresh word's no-merger probability.

For the literal strict word grammar,

    1=b_1>b_2>...>b_M>0.

Positivity follows from a positive-probability no-merger history through the finite word. Sampling consistency gives b_(j+1)<=b_j. Strictness can be seen in the initial positive ordinary population: there is positive probability that the extra root merges with one of the j retained roots there, no retained pair merges, and no further merger occurs anywhere in the finite word. Deleting the extra leaf removes that merger, so this event contributes to no merger among the retained j roots but not among all j+1. Strict ordinary leading padding is part of the inherited word realization. This argument is not asserted for a boundary cell or arbitrary exposed register interface.

Consequently

    product_(j=1)^M (K-b_j*I)=0.

Indeed K-b_j*I sends V_j into V_(j-1), and the factors commute since they are polynomials in K. Applying them successively down the filtration kills the whole space. The polynomial has distinct real roots, so K is diagonalizable over R.

The empty-input identity block, if adjoined, is isolated and introduces no Jordan coupling to the one-root block. The argument uses the CURRENT-root transition filtration, not an unverified identification with a different left-regular arity representation.

This is an elementary consequence of the old source representation, not a new characterization of its generated semigroup. Different source words need not have the same eigenbasis, and INDEPENDENT products remain noncommutative.

## 3. Exact obstruction to one natural automaton embedding

A fixed source word K has, for every fixed pair of real linear readout vectors, a repeated-word sequence of the form

    alpha^T K^n beta=sum_j c_j*b_j^n.

No nonzero n*b^n term can occur. Equivalently its recurrence has a square-free characteristic polynomial. A genuine nontrivial Jordan block, or any operator with such a polynomial-times-exponential sequence, cannot be conjugate to K or appear as a linear invariant-subspace quotient of K: the quotient/restriction minimal polynomial divides K's square-free polynomial.

Bell's displayed integer-variable encoding uses exactly such nontrivial repeated-eigenvalue behavior before stochastic scaling. Therefore that encoding cannot be copied letter-by-letter into fixed strict fresh source words by a fixed linear intertwining/readout that preserves arbitrary repetition. Making the source words longer does not remove this obstruction: every resulting fixed positive word still has the strict root-count spectrum above.

This does NOT exclude a different encoding using noncommuting words, nonlinear readouts, changing parameters or a more elaborate legal original interface. It does not establish that every PFA in Bell's theorem must use the same obstruction in every alternative representation. The claim is restricted to the displayed Jordan-based construction and direct repetition-preserving linear simulations.

## 4. Additional missing original-source bridges

Even a successful matrix simulation would still need a finite original observation input that forces every competing source to obey the simulated alphabet and shared-parameter rules. A finite list of arbitrary transition matrices is not an admitted source alphabet by default. Original control IDs and once-drawn registers cannot silently be reused as an unbounded sequence of independently programmable state transitions.

One must also preserve the original rooted unranked readout/coarsening, positive natural parameters, legal graph admission, one graph and one parameter assignment across all rows, and all alternative source cores. Approximate simulation, a limiting zero-duration source, an arbitrary signed linear statistic or a supplied-chain promise would not suffice.

Thus this prior search identifies both a genuine nearby undecidability theorem and a precise structural obstacle to its most direct transplantation. It gives neither evidence that original G3 is undecidable nor a positive recognition theorem. The cap-seven arithmetic/critical-fibre gap remains, and exposed/tied/general joint interfaces require separate analysis.
