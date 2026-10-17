# Contact-changing rotation attempt: exact fixed-hopping admission obstruction

17 October 2026, 03:25 UTC. dot (OpenAI). Local research checkpoint; no independent review, publication, novelty or master-resolution claim.

## Target retained

Same real 60-site Rashba Hamiltonian, t=501643/20000, lambda=5/2, Delta=1/5, identical fixed leads, one potential vector per device in the same prescribed bounded class, full field interval [0,2], opposite fixed reflection-determinant margins at B=2. The accepted sign/reversal transformations preserve Q; their proofs are not repeated. Criterion11 supplies a specified-pair algebraic test; execution12 rejects the existing near-equality pair as an exact collision. Neither closes the unknown-pair question.

## A direct contact-changing family and why it fails

Let A be the 60-site path adjacency matrix, A_(j,j+1)=A_(j+1,j)=1, and K the skew matrix K_(j,j+1)=1, K_(j+1,j)=-1. Write S_a=diag(a)-t A. A real spatial rotation O(theta)=exp(theta K), acting identically on spin and Nambu coordinates, commutes with K. It therefore preserves the spin-orbit hopping term, field term and pairing term under conjugation, and generally changes the endpoint contact subspaces. A successful construction would require

    O(theta) S_a O(theta)^T = diag(b(theta))-t A.

This is an actual fixed-family admission condition, not a consequence of spectral equality.

Differentiate at theta=0:

    S'(0)=[K,diag(a)]-t[K,A].

The off-diagonal entries of [K,diag(a)] at each neighboring pair are both a_(j+1)-a_j. Also

    [K,A]=2(E_11-E_60,60).

Thus preserving every fixed hopping to first order requires a_1=...=a_60. For a uniform profile a=cI, the first derivative is diagonal but

    S''(0)=-t[K,[K,A]]
           =2t(E_12+E_21+E_59,60+E_60,59).

The endpoint hoppings consequently change by t theta^2+O(theta^3). Since t is nonzero, no open neighborhood of theta=0 in this rotation family stays within the admitted scalar-onsite-only class, even at uniform a. For nonuniform a it already leaves the class at first order.

The two displayed commutators were directly evaluated with exact integer SymPy 1.14.0 matrices at N=60. This is a finite algebraic control, not a numerical spectral fit. It rules out this continuous small-rotation construction only. It does not exclude isolated nonzero theta values, other rotations, parameter-dependent generators, or equality of only the lowest branch. Holding the contacts fixed is essential: moving contacts together with H would be a different experiment.

## The remaining exact join for a broader rotation ansatz

Diagonalize sigma_x by a fixed real spin basis change. The field term is then diagonal in spin. Restrict, explicitly as an ansatz rather than a completeness claim, to orthogonal transformations diag(O_plus,O_minus) on the spatial coordinates of the two spin sectors, acting trivially in Nambu space. Such a transformation intertwines the complete B pencil within the fixed model exactly if

    O_plus S_a O_plus^T = S_b,
    O_minus S_a O_minus^T = S_b,
    O_plus K O_minus^T = K.

The last equation preserves the fixed spin-orbit coupling. Since N=60 is even, K is invertible (its determinant is 1 by the elementary tridiagonal recurrence). It forces

    O_minus = K^(-1) O_plus K,
    O_plus (K K^T) O_plus^T = K K^T.

These are simultaneous constraints; choosing an arbitrary eigenbasis rotation of a single Hamiltonian does not solve them. In addition, both profiles must belong to the same declared bounded class and the unchanged-contact scattering determinants must have opposite prescribed margins. No solution to these simultaneous equations has been obtained here. General unitary intertwiners can mix Nambu and spatial coordinates, so failure of this ansatz would not establish full exclusion. Lowest-branch equality does not itself imply any fixed intertwiner.

## Prior applicability check

The previously recovered tight-binding supersymmetry construction changes hopping and therefore does not supply this admission join (see NOVELTY-COMPARISON-20261017.md, section 7).

Fresh primary access:

- Hatinoğlu et al., Ambarzumian-type Problems for Discrete Schrödinger Operators (2021), https://doi.org/10.1007/s11785-021-01169-5 . The official full-text article defines scalar Jacobi operators with fixed off-diagonal entries and free/partly known diagonal data. Its free-spectrum and mixed two-consecutive-eigenvalue uniqueness results do not apply to arbitrary unknown 60-site spin/Nambu profiles observed only through the lowest absolute-energy branch across a field interval. No reduction to its premises is established.
- Isomorphic inverse problems for Jacobi operators (2026), supplied publisher locator https://www.sciencedirect.com/science/article/pii/S0024379526003472 . The direct read returned HTTP403. Its actual theorem assumptions were not inspected, and no result is imported from a search snippet.

## Exact unresolved information

An admissible opposite-margin pair still requires either an exact solution of a contact-changing full-pencil construction that returns to the fixed scalar-onsite class, or a direct common-factor/lowest-root certificate that need not be fully isospectral. Full exclusion requires all admitted parameter strata, including reducible characteristic factors and degeneracies. Neither the rotation calculation nor the recovered inverse-spectral suppliers provides this information. No speculative public theorem or new generic component is proposed from this pass.
