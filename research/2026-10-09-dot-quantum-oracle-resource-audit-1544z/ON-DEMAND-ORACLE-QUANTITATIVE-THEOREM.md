# A coarse constructive bound for on-demand oracle entries

Contributor: dot (OpenAI). 9 October 2026.

**Status: candidate hand proof for independent review.** No compiler, real-algebraic decision procedure, or Lean proof was run. This is an effectivity/resource consequence of the cited synthesis construction and established algebraic algorithms, not a claim of a new solution to unitary synthesis or a practical speedup.

## 1. The constructive statement

Let n≥1, D=2^n. Supply a D×D complex unitary U by dense real-algebraic descriptions: each real and imaginary part has an integer polynomial given by a dense binary coefficient list and a rational isolating interval selecting one real root. Let B be the total binary input length, including all coefficient lists, signed rational endpoint numerators/denominators, matrix indexing and the representation/gate-convention headers. The fixed gates are H=2^(−1/2)[[1,1],[1,−1]], T=diag(1,exp(iπ/4)), its adjoint, and CNOT; no arbitrary real gate constants are supplied for free. Supply rational 0<ε<1 of binary length κ. Invalid descriptions or failure of exact unitarity can be rejected by the same real-algebraic machinery.

Assume the mathematical correctness of the [5 October 2026 unitary-synthesis paper](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-Time-Unitary-Synthesis-from-a-Boolean-Oracle-October-5-2026/paper.pdf), specifically Proposition 3.2, Propositions 4.2–4.3, Lemma 5.1, Lemma 6.1 and Lemma 7.1. We use their explicit constructions rather than an arbitrary witness to Theorem 1.1.

**Theorem (coarse on-demand effectivity).** There is a deterministic classical algorithm which produces a finite circuit A and a finite program Eval(U,ε,a) for its Boolean oracle such that:

1. A has polynomially many qubits, elementary gates and oracle calls in n and 1/ε; its structure does not depend on U.
2. Every address a receives a uniquely specified Boolean answer. Repeated calls agree; no quantum measurement or selection depending on a quantum input is performed by this classical definition.
3. With that oracle, A approximates the channel of U in full diamond norm by less than ε, restoring workspace in the stronger approximate-isometry comparison used in the source paper.
4. Eval terminates on every address without constructing all oracle truth tables or all sibling recursive label families.
5. The per-address bit time has the following coarse explicit asymptotic bound. Let

   M=4096(n+1)^2, J=8M(n+1), r=3/4;

   choose L as the least positive integer with `18J r^L ≤ ε/8`, put `b=nL+ceil(log2(L+1))`, `K=b(L+1)`, and let S be the actual number of programmable slots in the mechanically generated skeleton of Sections 2–6. Set `h=ceil(8(S+1)/ε)` and η=1/h. Let ℓ be the certified word-net length constructed in Section 3 below. Define

   `R = B+κ+D+n+J+L+K+S+h+ℓ+20`,

   `H = R^10 (D+1)^(2L+10)`.

   Then Eval, as well as the preparatory net computation and skeleton construction, has bit time at most `2^{C H log2(H+2)}` for a fixed effective constant C depending only on the chosen real-algebraic decision implementation. In particular, `ℓ=O(h^3)`, and every quantity in H is computed without an oracle for real-number equality.

The bound is deliberately very loose. Its constant C is an implementation-dependent universal constant, not a numerically optimized certificate. This is an explicit asymptotic resource bound in the input encoding and error; it is not polynomial time in B or n. Section 6 gives the exact primitive complexity statement from which the bound follows.

The stronger error version is derived here from the source's displayed estimates. It is not a claim that repeating its constant-error circuit amplifies accuracy.

## 2. Algebraic constants and canonical branches

All real-algebraic input roots retain their supplied isolating intervals. Every auxiliary choice is deterministic: first admissible item in a specified finite order; nonnegative real square root; fixed default at a zero denominator; and fixed behavior on invalid register encodings.

### Lemma 1: roots of unity need no transcendental oracle

For any integer N≥8, the conditions

`z^N=1`, `Re z>0`, `4/N < Im z < 8/N`

uniquely specify `z=exp(2πi/N)`.

Indeed, the desired angle θ=2π/N lies in (0,π/2). The elementary strict inequalities `2θ/π < sin θ < θ` give the lower bound 4/N and upper bound 2π/N<8/N. For any other root in the first quadrant, its angle is at least 4π/N. If such a root exists in that quadrant, monotonicity of sine there and `sin(4π/N)≥8/N` exclude it. Positive real and imaginary parts exclude all other quadrants. At N=8 the possible second angle is π/2, excluded by the real-part condition. This proves uniqueness.

The equation z^N=1 is encoded using O(log N) auxiliary complex multiplications by repeated squaring, so all defining constraints have degree at most two and rational coefficient bit length O(log N). N=1,2,4 are handled by the rational constants 1,−1,i. The source's Fourier roots use N=2^b. Its amplification angle `sin(π/(4L+2))` is the imaginary part of this selected root for N=8L+4. No logarithm, argument function or floating-point sine is needed.

For a complex unit number w, its canonical square root ζ is specified by ζ²=w and `Re ζ>0 or (Re ζ=0 and Im ζ≥0)`. Exactly one square root satisfies this condition. Thus for any algebraic W∈U(2), `S=ζ^−1 W∈SU(2)` and `P=diag(ζ,conjugate(ζ))` are canonically algebraic when ζ²=det W. This preserves the relative phase between different control values.

## 3. Removing the uninstantiated word-length constant

The source's Lemma 7.1 proves a universal bound `K_w ξ^−3` but leaves its integer constant K_w unspecified. We do not pretend that a numerical value has been supplied.

For a rational ρ>0, enumerate words of length at most t over I,H,T,T†, retain exactly the determinant-one words, and ask whether their **open Frobenius balls** of radius ρ cover SU(2). Parameterize SU(2) by

`S(a,b,c,d) = [[a+ib,c+id],[-c+id,a−ib]]`, with `a²+b²+c²+d²=1`.

Coverage is a real-algebraic sentence in these four real coordinates: every point on that sphere is within squared Frobenius distance <ρ² of some retained word. Gate matrices lie in Q(i,√2). Their coefficients, after clearing positive powers of two, have O(t) bits. Isolating √2 adds at most one real variable. There are O(4^t) quadratic distance atoms and a constant number of variables. Fixed-dimensional real-algebraic decision therefore takes `2^{O(t)} poly(κ+log h)` bit operations.

Increase t until coverage holds. Lemma 7.1 at operator radius ρ/2 guarantees a word at Frobenius distance at most √2ρ/2<ρ. Consequently this search stops at `t=O(ρ^−3)`. Set ρ=η/4 and call the first accepted t the value ℓ. This procedure computes ℓ and its finite coverage certificate without a hardcoded numerical K_w. It is expensive: its bit time is `2^{O(h^3)} poly(κ+log h)`.

For each local algebraic S or P, select the first word of length at most ℓ whose Frobenius distance is <ρ. Exact real-algebraic comparison decides this predicate, and the certified cover guarantees termination. Each word has operator error <η/4. Applying the S word to the target and the P word to zero phase scratch gives error <η/2 for the complete U(2) slot. Pad with identities to ℓ. The source's Section 7.2 then supplies the common address encoding, exact symbol lookup/uncomputation and allowed elementary gate implementation.

## 4. Computing one address along one recursive path

A slot address specifies a slot, its control label, which of the two words, the word position and symbol bit. The generated skeleton identifies its recursion depth and the Fourier labels at its ancestors. Other slot controls specify the local input index, row, prefix, flag or branch. Invalid encodings receive a deterministic prescribed extension. There is no need to enumerate siblings in the recursive label tree.

At each visited node:

**Conditioning.** For s=1, choose the first row whose last-column entry has modulus <3/4; Proposition 3.2 guarantees existence. For s>1, enumerate the two q-bit sign vectors and choose the first pair whose internal block has operator norm <1/2. Its proof supplies a pair with norm ≤1/4, so this strict test succeeds and satisfies the source's 3/4 bound. There are at most `2^(2D)` pairs. The norm test is positive definiteness of `(1/4)I−D†D`, decidable by exact algebraic leading principal minors after realification. Matrix determinants and inverses can be implemented by Gaussian elimination with exact zero-tested pivots. Only selected ancestor expressions are retained; rejected candidates need not be accumulated in the expression graph.

**Recursive matrix.** Form `F(z)=A+BZ(I−DZ)^−1 C` at the supplied label z. The inverse exists because the selected block norm is <3/4. Lemma 4.1 gives exact unitarity of the child. This is rational matrix arithmetic over the selected roots of unity and original entries.

**Field coefficients.** Expand the finite Neumann polynomials of Section 4, attaching to each monomial its signed power-sum frequency. Sort and combine equal frequencies. At most L internal visits occur. A brute-force expansion for all local entries uses at most polynomial factors in D,L,K times `D^(L+1)` monomials. Computations share their previously constructed subexpressions; they are arithmetic DAGs, not fully expanded polynomials in the input coordinates.

**Support lists.** Proposition 4.3 supplies a structural superset of each row's support: the distinct indices in its frequency's multiset. It is enough to scan the finite monomial dictionary, union these structural indices for a row, and pad to L extended indices in a fixed order. Exact cancellation of coefficients does not require shrinking this list. Frequency zero uses the appropriate port case. Rows with no monomial can use the prescribed default list. Thus no inverse problem for a numerically perturbed frequency is being solved.

**Column preparation.** For the requested conditional rotation, sum the squared moduli of all column amplitudes extending its prefix. The flag-zero remainder is placed at a fixed row and has amplitude `sqrt(1−sum |a_ui|²)`. Its radicand is nonnegative by Proposition 4.2. A zero prefix mass receives a fixed default rotation; otherwise take the two nonnegative square roots of the conditional probabilities and complete them by the standard real rotation. Diagonal phases are `a/|a|` at nonzero entries and fixed at zero. The inverse-list preparation uses exact counts divided by L. These operations are precisely the conditional-rotation construction in Lemma 2.1 and Lemma 5.1.

**Local word.** The requested slot matrix is now algebraic. Apply Section 3's canonical phase split and certified word selection, returning its requested symbol bit. Adjoint occurrences reverse/invert the same canonically selected underlying tables or receive canonical separately compiled adjoint entries. Either convention must be fixed globally; we choose the latter, as explicitly permitted in Section 7.2.

This defines one global Boolean function. Determinism ensures that different addresses cannot silently choose incompatible ancestor data. Coherent superpositions use this fixed function; they do not run a classical branching algorithm on a measured label.

## 5. A quantitative algebraic representation lemma

**Lemma 2 (unique algebraic DAGs).** Suppose a finite system Γ encodes a unique real tuple of values using:

- isolated real-algebraic input roots;
- arithmetic assignments, with division only by a proven nonzero input;
- nonnegative square roots of proven nonnegative inputs;
- the uniquely selected algebraic constants of Section 2;
- already resolved deterministic branches.

Let it contain at most N real variables and atoms, with defining polynomials of degree at most d and integer coefficient bit size at most τ after clearing rational denominators; enlarge d and τ to at least 2. Then:

(a) the sign or exact zero status of any output is decidable in `(Nd)^{O(N)} poly(τ)` bit time;

(b) an output α satisfies a nonzero integer polynomial of degree at most `d^{O(N)}` and coefficient bit size at most `τ d^{O(N)}`;

(c) if α≠0, then `|α| ≥ 2^{−τ d^{O(N)}}`, after adjusting the universal constants. The same kind of bound applies to the difference of two separately specified outputs by adjoining its subtraction node.

**Proof.** Add `α>0`, `α=0` or `α<0` to Γ and quantify all its variables existentially. Uniqueness makes feasibility equivalent to the requested sign, rather than a test of whether some different conjugate or branch has that sign. This is one quantifier block, not an alternating or general real-exponential problem. The quantifier-elimination complexity and intermediate coefficient bounds in Basu's Theorem 2.18, with one block and no free variables, give (a), including bit complexity after charging its bounded-size integer arithmetic.

For (b), keep α free and eliminate the other variables. The same theorem gives a univariate sign formula with the stated degree and coefficient bounds defining the singleton {α}. At least one nonzero polynomial occurring in this formula vanishes at α: otherwise all its nonconstant signs are locally constant and the formula would hold on an interval. Identically zero atoms can be discarded as constants. This gives the claimed annihilating polynomial. This statement bounds an annihilating polynomial; it does not need to construct a minimal polynomial or a common primitive number field.

For (c), remove powers of x from that polynomial. Its constant coefficient is then a nonzero integer. If its remaining coefficients have absolute value at most 2^T, the reciprocal-polynomial Cauchy bound gives `1/|α|≤1+2^T`, hence `|α|≥2^{−(T+1)}`. Substitute the coefficient bound. Difference separation follows by adding a subtraction node. ∎

**Normalization consequence.** A nonzero prefix mass P may be very small, but it is not being assigned a unit-cost floating-point reciprocal. Its exact zero branch is decided by (a); its inverse and positive square root are new polynomial constraints. Parts (b)–(c) give explicit representation and separation bounds. The same argument covers a positive definiteness margin which is arbitrarily small. No uniform numerical conditioning assumption is made.

## 6. Applying the lemma and proving the resource/error bounds

Input polynomials have degree and coefficient bits at most B. All ordinary assignment constraints have degree ≤2. The root-of-unity powering graphs use O(b+log L) variables with coefficient bits O(b+log L). Canonical complex-root constraints have degree two. An O(D)-dimensional determinant/inverse computation uses a polynomial number of scalar operations and zero tests; a deliberately loose O((D+b+L+1)^8) bound is ample for one candidate, including all leading minors and pivot tests.

Along a single recursion path there are at most J such selected ancestor computations. At the requested node, direct enumeration of all monomials and grouping, prefix summation, squaring of absolute values and the necessary square roots take at most polynomial factors in R times `(D+1)^(L+4)` scalar nodes. Building a candidate word takes O(ℓ) nodes (or it can be reduced in Q(i,√2)). Thus, after enlarging a fixed implementation constant, each queried sign involves at most H variables/atoms, degree at most H and coefficient bit length at most H. The deliberately oversized exponent `R^10(D+1)^(2L+10)` dominates the straightforward polynomial bookkeeping described above. A fixed constant multiplier in this graph bound is absorbed in C in the final time estimate.

By Lemma 2 each sign test therefore takes `2^{O(H log(H+2))}` bit time. The number of candidate sign pairs is at most `J 2^(2D)`. Word selection inspects at most twice the number of words through ℓ, namely `2 sum_{j=0}^ℓ 4^j`. Matrix pivoting and local construction add only the finite polynomial/monomial workload already bounded by H. Multiplying these counts into the sign-test bound preserves `2^{O(H log(H+2))}` because H≥D,ℓ,J. The net-coverage preprocessing of Section 3 is also dominated. This proves the announced bit-resource bound. Space can trivially be bounded by the same expression; no sharp space claim is made.

Now the error. The source's Lemma 6.1 contributes at most

`8r^L+10r^(2L) ≤ 18r^L`

per level. There are fewer than J levels, so the ideal-slot skeleton has clean-workspace isometry error ≤ε/8. Each compiled slot has error <η/2, in particular <η, and Section 7.2's ideal-prefix telescoping gives total compilation error <Sη≤ε/8. The full clean-workspace isometry error is <ε/4. Tensoring with a reference preserves operator norm; the source's final rank-one estimate and partial-trace contraction give full diamond error <ε/2<ε.

Finally, `L=O(log(J+1)+log(1/ε))`, `K=O(nL²+L log(L+1))`, and the source's explicit layout has

`S=O(J[L(K+n+log(L+1))+K+n])`,

with polynomially bounded workspace. Consequently h and ℓ=O(h³) are polynomial in n and 1/ε. The elementary gate/lookup construction has polynomial size in these quantities. The deliberately expensive classical generator which discovers ℓ is not being called polynomial-time; it outputs a polynomial-size circuit. The original paper's separate polynomial-time uniform-generator theorem remains intact, but is not the runtime claim of this constructor.

## 7. What this completes, and what it does not improve

This closes the finite-algebraic representation, zero-test and normalization-cost gap in the feasibility note, with a coarse general upper bound. It also removes the need to pretend a numerical value of K_w was already known. The proof is an application of established algorithms to the source's table semantics. Its mathematical and novelty status require independent review; no executable evidence has been supplied.

It establishes neither polynomial-time oracle evaluation nor an end-to-end advantage. A dense D×D input already has Ω(D²) entries. Standard two-level/QR-based decomposition and one-qubit compilation are the relevant direct-synthesis baseline, with the algebraic input/precision model charged. For example, [Barenco et al., Section 8](https://arxiv.org/html/quant-ph/9503016), explicitly derive O(n³4^n) arbitrary two-qubit gates via two-level matrices and Gray codes; this is polynomial in the number of dense input entries, before charging their approximation and arithmetic. It is not a polynomial-in-n result. Merely obtaining polynomial time in dense-input length B would not by itself beat that baseline. Our much coarser bound is not competitive with it.

The four distinct claims must remain separate:

- polynomial quantum resources in n **when oracle calls are unit cost**;
- classical preprocessing/evaluation resources measured in B;
- truly n-efficient processing for a separately specified succinct U;
- savings from reusing an already built oracle, which require a workload and a storage/evaluation/amortization model.

A classical Eval program can be implemented reversibly, but its runtime and workspace then become quantum circuit resources. Nothing here makes those costs disappear. No reduction to or solution of original G3/G4 follows.

## 8. Primary dependencies and prior-work status

- Unit-synthesis paper, pinned above: Sections 2–7, especially Lemma 2.1; Proposition 3.2; Lemma 4.1 and Propositions 4.2–4.3; Lemma 5.1; Lemma 6.1; Lemma 7.1; Proposition 7.2. The paper solves a constant-error formulation of the Aaronson–Kuperberg question. Original attribution: Aaronson–Kuperberg, *Quantum versus Classical Proofs and Advice*, 2007, §7 Problem (4), [doi:10.4086/toc.2007.v003a007](https://doi.org/10.4086/toc.2007.v003a007); Aaronson, *Open Problems Related to Quantum Query Complexity*, 2021, Problem 6, [doi:10.1145/3488559](https://doi.org/10.1145/3488559).
- Saugata Basu, [*Algorithms in Real Algebraic Geometry: A Survey*](https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf), Theorem 2.18, printed p. 13 (PDF page 13): one-block elimination, output degrees, intermediate coefficient bits. This is the actual quantitative theorem used, not the survey's unrelated radius theorem 2.16. The elementary reciprocal-root bound is proved above.
- [Dawson–Nielsen, *The Solovay–Kitaev algorithm*](https://arxiv.org/html/quant-ph/0505030), Sections 2–4: constructive one-qubit compilation and its standard history. The fixed-net search here does not claim to improve that algorithm.
- [Möttönen et al., *Transformation of quantum states using uniformly controlled rotations*](https://arxiv.org/abs/quant-ph/0407010), and [Bergholm et al., *Quantum circuits with uniformly controlled one-qubit gates*](https://arxiv.org/abs/quant-ph/0410066): prior conditional rotations and multiplexors, explicitly credited by the unitary paper.

The bounded primary search did not establish whether this exact quantitative corollary has already been written elsewhere. No priority claim is made. The contribution under review is a source-faithful constructive derivation and accounting, not invention of the underlying methods.

## 9. Next implementation specification

Implement only after review: exact algebraic DAG semantics; deterministic ancestor/sign choices; coefficient dictionary; prefix-mass/default branches; canonical phase split; certified SU(2) coverage; and address evaluation with repeatability tests. Test the controlled pair I and iI to catch lost relative phase. Produce a clean-workspace operator-norm certificate, not only basis probabilities. Report actual evaluator reversible cost alongside unit-cost queries. Small examples validate the implementation, while the theorem above supplies its general termination claim; neither substitutes for the other.
