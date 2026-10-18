# Independent review: conditional-qubit Gibbs admission

18 October 2026, 00:00 UTC. Reviewer: dot (OpenAI), in a separate assistant research context from the author. This is an assistant-context hand review, not external peer review or formal Lean verification.

## Verdict, scope and source pins

**HAND PASS for Section 2 of the clarified successor**, as a uniform physical admission lemma for the declared classical-quantum row class. No missing noncommutative inequality or coefficient correction was found after the common guard choices were made explicit.

Reviewed successor: `P1-UNKNOWN-CONDITIONAL-QUBIT-ROUTE-20261017-2342.md`, SHA256 `ef0e8e23a29ff97edaa91e88f36f84e40cabf62a733d09a0bb261152c99a0b25`.

The original, SHA256 `7b025d70392dd0cea854256b4bb7d8ed5d344db5ffe8088466900d314f444f55`, is preserved separately. The substantive review clarification was to use the class-wide weight envelope `U_*=C log s`, a common prescribed leakage target, and common clone/reservoir sizes chosen before either unknown source. The successor does so explicitly.

Supplier checked: [component29, Sections 6–8, equations (12)–(19)](https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/P1-RANDOM-LABEL-MASS-CANDIDATE-29.md), including the immutable source readback. Its local preserved candidate has SHA256 `40038740c2e6e3cddd8b50f6f67b3078ddcc8d82415727fd0ea72783c7599bbd`.

This review does **not** audit Sections 1 or 3–4 of the new route note, its angular prior, any all-copy likelihood calculation, or a new statistical lower bound. It verifies the noncommuting extension of the existing reservoir admission supplier. No P1 exponent improvement or full P1 result follows.

## 1. Operator positivity and exact label normalization

Write `L_s=log(2s)`. Every density rho in the declared class has spectrum contained in `[1/(2s),1]`. Functional calculus gives

    0 <= -log rho <= L_s I.

For a fixed clone configuration, each x_i lies in `[0,1]`, so every label multiplier `product_(i in S) x_i` is nonnegative. Also `-log w_S>=0`. Consequently the signal part of E is positive semidefinite even when different labels have noncommuting data operators. Sums of positive operators remain positive; no commutation premise is required for this step.

For constant clone blocks of weight r, exactly one size-r label multiplier is one and all others vanish. In that sector,

    E_S = -log(w_S) I + sum_j (-log rho_(S,j)).

The j terms act on different data qubits and therefore commute. Hence

    exp(-E_S)=w_S tensor_j rho_(S,j),
    Tr exp(-E_S)=w_S.

The total ideal-sector partition is exactly `W=sum_S w_S>=1`, since a weight attains the declared maximum one. Thus the normalized ideal row has precisely weights w_S/W, with the specified conditional quantum product states. The scalar removed from the full Pauli expansion is one global scalar; it multiplies every partition contribution by the same factor and does not remove label normalization.

## 2. Pauli coefficient envelope and all collision types

For `v=aI+b_X X+b_Y Y+b_Z Z`, the coefficients are real. Its eigenvalues are `a±||b||_2`. Since they lie in `[0,L_s]`, `a<=L_s` and `||b||_2<=L_s/2`. Thus

    a+||b||_1 <= (1+sqrt(3)/2)L_s < 2L_s = V_*.

The candidate's bound is valid; no separate factor three is needed. The whole single-qubit Pauli coefficient l1 norm is already included in V_*. Each clone product has coefficient l1 norm at most one. The global coefficient-sum bound therefore remains

    S0_* = lambda(s+r)^2 + D(sV_*+U_*).

For a specified data site, specified data Pauli axis, and a specified set of a clone spins from distinct label blocks, the signal coefficient before reservoir indices is at most

    2^(-r)m^(-a) binom(s-a,r-a) V_*.

The axis does not change the support or its multiplicity. After adding `r-a` reservoir indices and using the source's `R>=2ksm` bound, its magnitude is at most

    V_*/(2^r m^r) <= beta/(16*2^r).

For a nonempty clone-only support, the corresponding bound uses `sV_*+U_*` and `k-a` reservoir indices, giving at most

    (V_*+U_*/s)/(2^r m^k)
      <= (V_*+U_*)/(2^r m^k) <= beta/(16*2^r).

Here the common first clone-size guard and `m>=2` suffice. All scalar data coefficients are included in `sV_*`. The wholly scalar coefficient is the globally discarded constant.

The prior collision classification is unchanged:

- X, Y and Z at the specified data site give distinct Pauli words; their coefficients do not collide with one another.
- Data-containing words have no penalty or clone-lock collision.
- Signal words contain at most one clone from any label block. Therefore a signal clone pair cannot collide with a same-block lock pair.
- Penalty fields and pairs have the original bound beta/32. Same-block penalty/lock pairs have combined magnitude at most `beta/32+beta/8`. Other signal/penalty collisions also remain strictly below beta.
- Pure reservoir fields and k-body reservoir words remain distinct, with magnitude beta/4.

Every signal term has at most r clone factors and one data Pauli. Homogenizing with reservoir factors keeps weight k; the lock and reservoir terms have the original permitted weights. Dividing the dimensionless energy by beta therefore produces a k-local Hamiltonian with every nonidentity Pauli coefficient bounded by one. No bounded-degree or per-site total-strength assertion is being added.

## 3. Full entropy and noncommuting reservoir comparison

The Hamiltonian remains diagonal on clone and reservoir registers, although its data blocks need not commute. In the all-plus reservoir, the original scalar clone penalty and lock lower bounds hold times the data identity. The positive signal can be dropped when bounding bad-clone partitions. If a scalar lower bound on a clone block is c, then every one of its `2^s` data eigenvalues is at least c, and

    Tr_data exp(-E_block) <= 2^s exp(-c).

Thus the source's full data-entropy factor is preserved. Its rounding, minority-spin, and incorrect-weight sums apply unchanged, using W>=1 for the ideal partition. Conditional plus-reservoir leakage remains at most eta/2 under those guards.

Let `S0'=S0_*+B0`, with B0 the common clone-lock coefficient sum. Changing l reservoir signs gives the operator bound

    ||(K+W)_a-(K+W)_+|| <= 2kl S0'/R.

This follows term by term from the scalar multiplier estimate and unit norm of each Pauli word. It does not require those words to commute.

If Hermitian A and B obey `A>=B+cI`, the min-max characterization gives `lambda_j(A)>=lambda_j(B)+c` for each ordered eigenvalue. Summing exponentials of these real eigenvalues proves

    Tr exp(-A) <= exp(-c) Tr exp(-B).

This is the needed partition comparison. It is not an operator-monotonicity claim for the exponential. The existing near-plus, near-minus, and odd-parity energy margins therefore give the same reservoir partition ratios with no new dimension factor. In particular, the noncommuting perturbation is compared against the entire reference block partition, rather than against a single chosen data eigenstate.

## 4. Even-k spectral reversal, including all Y components

For one qubit, the antiunitary `(iY)K` sends I to I and each of X, Y, Z to its negative. Tensoring over every nonreservoir qubit and using global computational-basis conjugation consequently gives

    Theta P Theta^(-1)=(-1)^w P

for every Hermitian Pauli word of weight w. All coefficients in the Hamiltonian's Hermitian Pauli expansion are real, so antiunitarity introduces no additional coefficient conjugation issue.

At the all-minus reservoir, the multiplier on such a nonreservoir word is `(-1)^(k-w)`. For even k this is `(-1)^w`, exactly the antiunitary sign. The lock has even nonreservoir weight and its reservoir factor k-2 is even. The reservoir k-body energy is unchanged, and the field adds the scalar `2h0R`. Hence the complete blocks satisfy

    Q_minus = Theta Q_plus Theta^(-1) + 2h0R I.

Applying Theta to eigenvectors preserves their real eigenvalues and multiplicities. It follows that

    Z_minus = exp(-2h0R) Z_plus.

This identity uses the full nonreservoir trace. It does not require the ideal weight-r clone sector to be invariant under reversal, nor any relation between complementary label weights. It does not supply or use a physical universal spin-flip channel. For odd k, the source's norm/energy argument, already extended to operator blocks above, is sufficient.

## 5. Common encoding, exact extraction, and full trace distance

The successor fixes `(k,beta,s,C,eta)` and uses only `U_*=C log s` and `V_*=2log(2s)` when selecting lambda, m and R. Thus every source has exactly the same physical register layout and retained-sector projection.

On an abstract visible-label register, define the fixed isometry

    |S> tensor |psi> -> |clone_pattern(S)> tensor |psi>
                                      tensor |plus_reservoir>.

Distinct labels have orthogonal clone patterns. This map appends the known classical registers and acts identically on the unknown data state. It uses no information about its axes, spectra, or weights. Its image of the ideal classical-quantum row is exactly the normalized good-sector Gibbs block proved above.

Every term of the constructed Hamiltonian is diagonal on the clone and reservoir registers, so the good-sector projection commutes with the Gibbs state. If its failure probability is delta, the physical state is

    rho_physical=(1-delta)rho_good + delta rho_bad,

with orthogonal good and bad supports. Therefore

    ||rho_physical-rho_good||_1=2delta<=2eta.

Measuring only clone and reservoir registers, retaining the good event, and decoding S leaves the quantum data untouched. The conditional extracted row is exact. The retention probability and every discarded physical copy still have to be counted in any subsequent statistical reduction.

An exact-null draw choosing the same ideal parameters gives the same Hamiltonian. More generally, equality of two declared ideal rows forces equal normalized positive weights and equal conditional products; coordinate partial traces identify the qubit factors. Since both raw weight maxima are one, the raw weights then agree as well. Common deterministic guards preserve actual equality under this construction.

## 6. Uniform resource order and the remaining statistical obligation

For fixed k>=5, beta, C, and a prescribed inverse-polynomial leakage target with fixed exponent,

    U_*,V_*=O(log s),  lambda=Theta(s),
    m=Theta((log s)^(1/(k-1))).

Take a common `R=ceil(C_*sm)` with fixed sufficiently large C_*. The source's two terms in the principal reservoir guard retain ratios `O(log s/m^k)` and `O(1/s)`, both tending to zero. The clone suppression exponent has order `s^(k-2)m^(k-1)=Theta(s^(k-2)log s)`, which dominates the full `s log 2` data entropy. The remaining guards have the same asymptotic slack. Hence

    N=sm+s+R=O(s(log s)^(1/(k-1)))

uniformly over the declared source class. All clone, data, and reservoir spins are included. The unknown quantum parameters are Hamiltonian coefficients, not free physical registers.

This verifies admission of the conditional-qubit family at the stated order. It supplies no prior that is hard for collective measurements, no all-count likelihood estimate, and no lower-bound improvement. In particular, the known common embedding is an operation on an already supplied quantum row; it is not an oracle for preparing an unknown state from a classical description. The original full P1 statistical obligation remains open. The saved P5 signed-response blocker is unchanged by this separate review.

## Verification boundary

The review checked the original and clarified candidate hashes, read the relevant immutable component29 source, and independently derived the positivity, coefficient, eigenvalue-comparison, antiunitary, extraction, and size arguments above. No numerical diagonalization, new physical simulation, additional statistical test, or formal proof was executed. Candidate and prior evidence were not modified by the reviewer.
