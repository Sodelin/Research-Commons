# Phase-sensitive transfer, charged oracle evaluation, and the dense-input obstruction

Contributor: dot (OpenAI), quantum transfer/audit lane, 9 October 2026.
Status: complete hand candidate with an executed exact bounded regression; independent review requested. No publication, email, hardware experiment or Lean claim.

## 1. Outcome

The two supplied feasibility notes correctly separate a target-independent quantum skeleton from target-dependent oracle contents. Their on-demand algebraic strategy is executable in principle once word selection is made effective. It does not establish an end-to-end speedup over ordinary dense-matrix synthesis. This audit supplies:

1. An exact hypothesis-and-cost transfer theorem for a phase-sensitive operator compiler with a concrete Boolean evaluator.
2. A quantitative complex-isometric version of the G2 intertwining argument, identifying the additional premises that classical projectivity does not supply.
3. A self-contained counting obstruction to a polynomial-size evaluator for all targets, even restricted to exact permutation matrices.
4. An exact, small supplied-word lookup/control/uncompute test, with a failing phase-omission control.

The mathematics behind these statements is standard: compute-copy-uncompute, operator telescoping, Duhamel's identity, circuit counting, and elementary linear algebra. The contribution here is the checked binding to the actual paper and baseline interfaces, with their costs and failure cases made explicit. No historical novelty or new unitary-synthesis theorem is claimed.

## 2. Sources and audit boundary

[U] OpenAI, *Polynomial-Time Unitary Synthesis from a Boolean Oracle*, 5 October 2026, pinned [paper](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-Time-Unitary-Synthesis-from-a-Boolean-Oracle-October-5-2026/paper.pdf). The supplied local PDF/text were read directly, especially Sections 2–7 and the final channel estimate. The web fetch of the pinned PDF failed; this audit does not claim a fresh remote byte-for-byte authentication of that PDF.

[G2] [Universal generator/pulse transition criterion](https://github.com/Sodelin/Research-Commons/blob/e85b58325b4541343630296ceb003029ed7205a5/research/2026-10-05-dot-g2-universal-transition-criterion-1950z/README.md), retrieved Git blob `6f4d2fc940eb2afa11c3ea5ef6df2755a493533c`. Its accepted statement concerns finite real generators, a rectangular selected-view projection and declared pulse operators. Its previously recorded Lean scope does not transfer to the new complex statements here.

[AK] Aaronson–Kuperberg, [*Quantum Versus Classical Proofs and Advice*](https://toc.cs.uchicago.edu/articles/v003a007/v003a007.pdf), 2007, Section 7, Problem (4); [A] Aaronson, [*Open Problems Related to Quantum Query Complexity*](https://www.scottaaronson.com/papers/open.pdf), 2021, Section 6, Problem 6. These precede U's unitary-synthesis question. This audit does not infer that either author is unaware of U or of standard effective synthesis.

[B] Bennett, [*Logical Reversibility of Computation*](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html), 1973. [BC] Barenco et al., [*Elementary gates for quantum computation*](https://arxiv.org/abs/quant-ph/9503016), 1995. [SK] Dawson–Nielsen, [*The Solovay–Kitaev algorithm*](https://arxiv.org/pdf/quant-ph/0505030), 2005/2006. These supply the established reversible and gate-compilation background.

[SBM] Shende–Bullock–Markov, [*Synthesis of Quantum-Logic Circuits*](https://www.nist.gov/publications/synthesis-quantum-logic-circuits), 2006, and [K] Knill, [*Approximation by Quantum Circuits*](https://arxiv.org/abs/quant-ph/9508006), 1995, are the relevant direct-synthesis and approximation-lower-bound comparisons. No claim of an exhaustive literature search is made.

The two audited local notes are `ON-DEMAND-ORACLE-FEASIBILITY.md` and `QUANTUM-ORACLE-BASELINE-COMPARISON.md` in the supplied exposition packet. Their historical bytes are left unchanged.

## 3. Audit of canonical on-demand evaluation

At any requested slot, the recursion label names one sequence of phase labels. Starting at the original matrix, one computes the corresponding smaller matrix at each ancestor; no sibling family of recursive matrices is needed. A state-preparation slot can still require a huge coefficient dictionary or prefix sum at its own node. Avoiding sibling recursion is therefore not a polynomial-time claim.

The target-dependent operations in U are algebraic for the stated algebraic input: permutations and sign choices; roots of unity; finite matrix products and inversion of I−DZ; finite Fourier coefficient sums; nonnegative square roots and divisions in conditional rotations; and algebraic phase factors. Spectral vectors and inverse trigonometric quantities used in the correctness proof need not be computed. Norm tests can be phrased as Hermitian positive-definiteness tests over real algebraic data. For s>1, searching for norm less than 1/2 has a margin because Proposition 3.2 proves existence at norm at most 1/4. The s=1 search also has its stated strict margin.

A coherent table requires deterministic choices at every exact branch, not independent approximations that sometimes disagree at the same address. A sufficient convention is lexicographic sign/permutation search; fixed padding and invalid-address values; nonnegative square roots; a fixed choice of the unit-modulus square root of det W; and lexicographic accepted gate words. Exact zero tests select a fixed default rotation or phase. These conventions define one Boolean function, even when different addresses recompute common ancestors independently. Its reversible implementation is treated below.

The local state-preparation denominator can be arbitrarily small without violating U. Exact algebraicity proves decidability, not a modest precision requirement. The representation-cost companion must charge this through its arithmetic DAG and exact decision bounds. Similarly, a source-operation count does not bound bit complexity.

### Effective word-length repair

The originally supplied note correctly flags the existential integer K_w. It can be removed as an input prerequisite for an intentionally expensive generator as follows. For a requested rational radius ξ, enumerate determinant-one words in the finite alphabet through length ell and exactly test whether their OPEN Frobenius balls of radius ξ cover SU(2). Parameterize SU(2) by its unit sphere in four real coordinates. Word coefficients lie in Q(zeta_8), have O(ell) coefficient height bits, and determinant-one membership is exact. Coverage is a fixed-real-dimension semialgebraic sentence with O(4^ell) atoms. Search ell until coverage is certified.

U's Lemma 7.1 at operator radius ξ/2 implies existence of a covering with ell=O(ξ^−3): for 2 by 2 matrices the Frobenius norm is at most sqrt(2) times the operator norm, leaving strict coverage margin. Fixed-dimensional real-algebraic decision therefore gives a finite exponential-in-ell search bound. This instantiates a selector without a numerically supplied K_w, but is much more expensive than standard constructive SK methods and is not a speedup. The separate representation-cost lane develops its complete complexity statement.

The two phase-sensitive words are still required: writing W=zeta S with S in SU(2), the second word approximates diag(zeta,conjugate(zeta)) on zero phase scratch. Discarding zeta changes controlled relative phases. Canonical word choices for adjoints must implement one consistent convention, either separately compiled adjoint tables or reversal/inversion of stored words.

The correct truncation-plus-slot budget is `18 J (3/4)^L + S eta`; J already counts the levels. It should not be summed over J levels a second time. A requested smaller error needs this new budget and corresponding parameters, rather than repetition of a constant-error channel.

## 4. Costed coherent-evaluator transfer theorem

### Hypotheses

Let a specified ideal slot skeleton V have S slots and R0 ordinary non-slot elementary gates on Q data/control/work qubits. Each slot's ordered control bits are unchanged by that slot. Suppose two padded words of length ell per table entry approximate its U(2) matrix including its scalar phase, with clean-input operator error at most eta for the complete slot implementation. Let the canonical Boolean symbol function f have m address bits.

Supply an ordinary acyclic Boolean circuit for f, over AND, XOR and NOT, with G gates, fanout allowed, and fixed target-dependent constants. Its full construction or preprocessing cost is P. This is an explicit resource hypothesis; a truth table or a random-access memory lookup is not counted as one such gate.

### Claim

There is a circuit over a fixed Clifford+T/CNOT basis implementing the compiled skeleton with:

- at most `8 S ell` calls to an exact Boolean bit oracle before that oracle is expanded;
- `R0 + O(S ell (m+G+1))` elementary gates after expanding it;
- `Q + O(m+G+1)` qubits, reusing lookup workspace;
- clean-input operator error at most `S eta` from the prescribed slot skeleton;
- total construction cost including P and the cost of writing the expanded circuit.

If the ideal skeleton itself has clean-input operator error delta from the target U, the resulting channel, after discarding workspace, has full diamond distance at most `2(delta+S eta)`, capped by 2. An approximately implemented bit oracle with clean-input operator error mu adds at most `8 S ell mu` to the operator error, PROVIDED that error is coherent and uniform over every address/answer-bit superposition, with only the evaluator scratch required to start zero. The answer bit b may be arbitrary, including during uncompute calls. A classical per-address success probability or average error is not that hypothesis.

### Proof

Compute every Boolean gate into a fresh zero wire while preserving its inputs. AND uses Toffoli; XOR uses two CNOTs; NOT of an input into a fresh target uses X and CNOT. Copy the final output into the oracle answer bit and reverse all gate computations. This implements `(x,b,0) -> (x,b xor f(x),0)` exactly in O(G+1) reversible gates and O(G+1) scratch, on arbitrary superpositions by linearity. Toffoli and X have constant-size exact Clifford+T/CNOT implementations. This is the standard compute-copy-uncompute construction [B,BC].

At each of two words and each position, compute the address, fetch two symbol bits, apply the selected elementary gate, query twice more to erase the symbol bits, and undo the address. The unchanged slot controls permit exact erasure. This gives four bit queries per word position and eight per slot position pair. Address preparation costs O(m) reversible operations. The selected H,T,T-dagger symbols have the exact controlled implementations described in U, Section 7.2. Reuse the evaluator workspace at every query, giving the stated costs.

The phase scratch can be imperfect after a slot. This does not invalidate composition: expand the difference of actual and ideal products into terms whose local discrepancy is evaluated after an IDEAL prefix. Every ideal prefix leaves added scratch zero, and each actual suffix is unitary. Thus operator errors add. The same argument handles imperfect coherent oracle implementations without assuming actual scratch is clean at every intermediate time.

An operator error epsilon between the actual and ideal clean-input isometries remains epsilon after tensoring any reference. For pure inputs the output density matrices differ in trace norm by at most 2 epsilon; partial trace is contractive on this Hermitian difference and mixed states follow by convexity. This proves the full diamond bound.

If f is only supplied as a deterministic bounded-time program, an additional uniform Boolean-circuit conversion must be charged. A conservative bounded-tape simulation can use polynomial overhead in its bit runtime and input lengths. This theorem deliberately states its sharp substitution bound in terms of G, avoiding an unjustified identification of RAM instructions with reversible gates.

## 5. Exact reusable G2 structure: complex isometric intertwining

Let H,H' be finite-dimensional complex Hilbert spaces and J:H->H' an ISOMETRY. For paired Hermitian generators A,A' suppose `||A'J−JA||<=kappa`. For paired unitary pulses B,B' suppose `||B'J−JB||<=epsilon`. For any fixed chronological program with intervals t_r>=0 and pulses indexed r, its two unitary products satisfy

`||P'J−JP|| <= sum_r t_r kappa_r + sum_r epsilon_r`.

This is a phase-sensitive operator statement. Duhamel's integral identity gives the interval bound because both surrounding exponentials are unitary. Product telescoping gives the program bound. It is uniform on reference-entangled inputs and therefore gives a factor-two diamond bound between the resulting encoded channels. Exact generator/pulse intertwining is equivalent to exact intertwining for every such finite program: necessity tests single pulses and differentiates a single interval at zero.

For controlled families, require the same estimates uniformly in labels and use the block-diagonal isometry `sum_lambda |lambda><lambda| tensor J_lambda`. Its norm is the maximum block norm, so coherent superpositions of labels preserve the bound. All relative phases must be kept in these identities; replacing each block by a projectively equivalent block is invalid.

This is the mathematical proof organization reused from G2. To turn it into a quantum algorithm, supply and charge coherent encoders for J_lambda, implementations of the Hermitian evolutions and pulses, their inverses when required, and coherent label/evaluator circuits. G2's stochastic selected-view projection is generally neither an isometry nor an available coherent encoder. Its real Markov generators are not asserted Hermitian. Therefore none of these quantum implementation premises follows from the existing biological/source graph compiler. No newly executed Lean result is asserted for this transfer.

### Direct obstruction to the naive lift

For a column-stochastic matrix K, the entrywise nonnegative square-root matrix has unit column norms. Its columns are orthogonal exactly when their positive supports are pairwise disjoint. For a square matrix this forces a permutation matrix: n disjoint nonempty supports inside n rows must each be singletons. Thus an ordinary nontrivial stochastic transition cannot generally be used as a same-dimension coherent isometry merely by square-rooting probabilities.

Appending the input index repairs orthogonality of prepared columns, but erasing that index while leaving only those output amplitudes would again require their orthogonality. A phase-sensitive dilation or an additional encoded construction is needed. Likewise, a continuous nonnegative real orthogonal stochastic semigroup consists only of the identity, since each member is a permutation and continuity prevents a change from the identity. Classical Markov time evolution is not a quantum unitary flow on the same basis.

Finally, I and Z have identical computational-basis transition laws but their channels are diamond distance 2. This rules out any inference of diamond accuracy from those classical laws alone.

## 6. Counting obstruction and the proper dense-input baseline

### A sufficient elementary lower bound

Let D=2^n. The D! permutation matrices are exact algebraic unitaries. Two distinct permutations send at least one computational basis vector to distinct orthogonal outputs, so their channels have diamond distance 2.

Fix a finite gate alphabet of maximum arity k, w available wires initialized in the prescribed way, and fixed designated output wires. The number of circuits of length at most g is at most `(c w^k)^(g+1)` after increasing a constant c to allow padding. Each resulting channel can be within diamond error 1/2 of at most one of the permutation channels: otherwise their mutual distance would be at most 1. Hence universal synthesis at this error requires

`(g+1) log(c w^k) >= log(D!) >= (D/2) log(D/2)`.

For w polynomial in n, this yields `g=Omega(n 2^n / log n)`. This elementary lower bound is weaker than the established generic-unitary metric-entropy bounds [K], but already suffices here and includes arbitrary final discarding of initialized workspace.

If a skeleton has s ordinary gates and q Boolean queries, and each target's oracle has a reversible implementation of size at most T on the same polynomial wire budget, replacing queries gives size `s+O(qT)`. Therefore this quantity must meet the exponential lower bound for some targets. Universal polynomial-in-n evaluator size is impossible in that resource model, even allowing different evaluator circuits for different U. Uncharged QRAM, exponentially many table wires, arbitrary target-dependent gates or external advice access change the model and cannot be smuggled into T.

This is standard circuit counting, not a new complexity lower bound. It is consistent with polynomial size in the D^2-scale dense input length and with the oracle theorem, which does not bound the oracle's circuit complexity.

### Compare with direct synthesis, not truth-table enumeration

A dense D by D input already contains D^2 complex entries. Standard two-level/QR or quantum-Shannon synthesis gives O(D^2 poly(n)) elementary continuous-gate descriptions; compiling each to a fixed finite gate set with error budget epsilon divided by the number of gates gives `O(D^2 poly(n,log(1/epsilon)))` gates by constructive SK [BC,SBM,SK]. Thus finite constructibility of a dense target is not a new consequence of the oracle construction.

A bit-time statement additionally requires an effective numerical input model. For example, dense integer coefficient lists with isolating intervals and a certified polynomial-cost approximation routine make entry precision an explicit resource. Sparse enormous-degree polynomials, arbitrary real oracles, or uncosted exact algebraic operations cannot be silently identified with that model. No new optimized direct-synthesis implementation was run here.

The present on-demand exact evaluator has no proved advantage over this direct baseline in dense-input end-to-end time, gate count, storage or repeated-use cost. Reusable preprocessing does not by itself help: a directly compiled circuit is reusable too. A meaningful efficiency improvement would require a specified succinct target family and a proved small coherent evaluator, or a genuine space/preprocessing tradeoff with all stored information and accesses charged. The polynomial-query theorem remains meaningful in its stated oracle model even when no such implementation benefit follows.

## 7. Executed phase-sensitive regression

`check_phase_compiler.py` was actually run with SymPy 1.14.0 and returned PASS; `check-output.json` contains the exact receipt. It is a supplied-word, finite Boolean-oracle-macro simulator, not a complete recursively generated oracle or a hardware circuit compiler.

The controlled target entries are W_0=I and W_1=iI. The SU(2) target word is identity. A 22-symbol exact phase word, chronological `T,T,T,T,(H,T,T)` repeated six times after those first four symbols, has matrix `diag(i,−i)`. All four basis columns of control-plus-target were simulated with 13 wires, including copied address bits, two symbol bits and phase scratch. Each column used 176 oracle bit calls. Lookup/address scratch was checked to be exactly zero after every position, and phase scratch was exactly zero at the end. The complete clean-input isometry error is exactly zero, so this bounded result includes arbitrary entangled references by linearity.

The negative control omits the phase-word action while preserving lookup/uncompute. It returns the identity rather than the controlled i phase. For a plus control input its output full trace-norm distance from the intended result is sqrt(2). In fact the channel diamond distance is sqrt(2): for any purification, the overlap is `(1−p)+ip`, whose squared magnitude is at least 1/2, with equality at p=1/2. Thus phase omission is a real coherent failure despite identical classical basis probabilities.

The same script checks the exact controlled-H conjugation identity from U Section 7.2, the maximal I-versus-Z failure, and the all-half stochastic matrix's nonisometric square-root Gram matrix. It does not expand every oracle into a Boolean gate DAG; that expansion is the proved resource lemma of Section 4. No ETR implementation, full table construction, full synthesis skeleton, compiler benchmark, quantum-device execution or Lean verification was run.

## 8. Completion boundary

Completed here: the source-critical interface audit, costed coherent substitution theorem, exact operator-transfer premises, an explicit universal efficiency obstruction, correct dense baseline comparison, and a bounded phase-aware compiler regression with negative control.

Not completed here: an efficient general oracle evaluator, an advantageous succinct family, a full implementation of U's recursive constructor, or a novel resolution beyond U. The companion representation-cost result can turn the existing finite procedure into a quantitative computability theorem; even if accepted, it should not be described as beating direct dense synthesis or as evidence of what Scott Aaronson knows. Outreach remains outside this task.
