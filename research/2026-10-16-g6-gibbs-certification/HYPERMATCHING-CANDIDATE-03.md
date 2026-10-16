# Unknown hypermatchings: candidate logarithmic strengthening of the Gibbs testing floor
Date: 2026-10-16. Hand proof prepared by dot for Nolan.
Status: complete candidate derivation awaiting independent review. Not Lean-verified or computationally tested. Novelty unresolved: the construction extends the signed unknown-matching method of Canonne–Diakonikolas–Kane–Stewart; a limited targeted prior search did not settle whether this hypermatching consequence is already recorded.

## Claim and exact source class
Fix an integer q>=3. Put n=qm, 0<epsilon<=1/16, b=4epsilon, t=b/sqrt(m), and beta>=atanh(t). For all sufficiently large m (depending only on q), testing equality of two unknown n-qubit Gibbs states against full trace norm at least epsilon requires Omega_q(n log n/epsilon^2) TOTAL copies. The Hamiltonians are q-local with every nonidentity Pauli coefficient bounded by one and zero identity gauge. No interaction partition is supplied. The bound holds even for collective quantum measurements. Additional uniform spectator qubits extend it to general n by m=floor(n/q); any k>=q admits the construction.

This is a lower bound for the class, not a minimax characterization. Its temperature admission and asymptotic m threshold are essential. The proof below is self-contained except for standard elementary inequalities. The measurement reduction is the same exact diagonal-state simulation recorded in [Checkpoint 01](https://github.com/Sodelin/Research-Commons/blob/ec136c4e6056e9901a67db082eb1d4e5349d85d7/research/2026-10-16-g6-gibbs-certification/SCOPED-LOWER-BOUND-CHECKPOINT-01.md).

## 1. Admitted family and separation
Let M be a uniformly random partition of [qm] into m unordered q-element sets. Assign independent uniform signs s_e to its blocks. Define
  H_(M,s) = -atanh(t)/beta * sum_(e in M) s_e product_(i in e) Z_i.
The blocks are disjoint. The Gibbs density relative to the uniform distribution U on {+/-1}^(qm) is exactly
  L_(M,s)(x)=product_(e in M)(1+t s_e chi_e(x)),
  chi_e(x)=product_(i in e) x_i.
The coefficient admission follows from atanh(t)/beta<=1. H=0 gives the null.

Under U the m block parities are independent fair signs. Write L-1=t S+W where S=sum_e s_e chi_e and W contains degree at least two in these m parity coordinates. Then
  EW^2=(1+t^2)^m-1-mt^2 <= exp(b^2)-1-b^2 <= b^4,
  ES^2=m, ES^4<=3m^2, and E|S|>=sqrt(m/3).
Consequently ||P_(M,s)-U||1 >= b/sqrt(3)-b^2 > epsilon.
Thus EVERY member of the alternative prior is admitted and far. One (M,s) is chosen and held fixed across all copies.

## 2. Exact two-prior overlap
Take two independently chosen signed partitions (M,s),(M',s'). Construct a bipartite multigraph whose left vertices are the blocks of M and right vertices the blocks of M'. Each ORIGINAL coordinate i contributes one incidence edge between its two containing blocks. Parallel incidence edges are retained. Every vertex has degree q.

For a Fourier term selected in the product L_(M,s)L_(M',s') to survive expectation under U, each original coordinate must occur zero or twice. Thus the selection status of the left and right block at every incidence edge must agree. Equivalently, the selected block vertices form a union of whole connected components.

A connected component has the same number r of left and right vertices: equality follows by counting its q-regular incidence edges on each side. Its nonempty selection contributes t^(2r) times the product xi_C of all its block signs. Therefore the exact one-copy overlap is
  E_U[L_(M,s)L_(M',s')] = product_C(1+xi_C t^(2r_C)).
Conditional on M,M', the xi_C are independent fair signs, since components use disjoint nonempty sets of independent block-sign variables.

Let Q_N be the mixture E_(M,s) P_(M,s)^(tensor N), and put
  f_N(u)=((1+u)^N+(1-u)^N)/2.
The second-moment identity and sign averaging give EXACTLY
  1+chi^2(Q_N,U^(tensor N))
    = E_(M,M') product_C f_N(t^(2r_C)).
For 0<=u<1, f_N(u)<=cosh(Nu)<=exp(N^2 u^2/2).

A component with r=1 is precisely a common q-block of M and M'. Let L be their number. Every other component has r>=2, and there are at most m components. With a=f_N(t^2)>=1, it follows pointwise that
  product_C f_N(t^(2r_C)) <= a^L exp(N^2 m t^8/2).

## 3. Common-block factorial moments, with no independence assumption
Fix M. The number of partitions of qm labels into q-blocks is (qm)!/[(q!)^m m!]. For any prescribed l distinct blocks of M, the probability that M' contains all of them is
  (q!)^l (m)_l/(qm)_(ql),
where (z)_l=z(z-1)...(z-l+1) and (z)_0=1.
Thus, for 0<=l<=m,
  E binom(L,l) = (m)_l^2 (q!)^l/[l! (qm)_(ql)].

For l>=1, group the denominator factors into q-tuples:
  (qm)_(ql)
   = product_(i=0)^(l-1) product_(j=0)^(q-1)[q(m-i)-j]
   >= (m)_l^q.
Also (m)_l >= (m/e)^l. One proof is that the average of the first l terms in the decreasing sequence log m,log(m-1),...,log1 is at least the full average, and log(m!)>=m log m-m.
Therefore, writing C_q=q! e^(q-2),
  E binom(L,l) <= [C_q/m^(q-2)]^l/l!.
Expanding a^L=(1+(a-1))^L and summing these nonnegative factorial moments gives
  E a^L <= exp[C_q(a-1)/m^(q-2)].
This bound uses the exact dependent partition law; no independent-edge approximation is made.

## 4. Copy scale and indistinguishability
Choose any fixed 0<c<q-2 and an integer
  N <= c m log(m)/b^2.
Then Nt^2<=c log m and a<=cosh(Nt^2)<=m^c. Combining Sections 2–3,
  1+chi^2(Q_N,U^(tensor N))
   <= exp[ c^2 b^4 log^2(m)/(2m) + C_q m^(c-(q-2)) ].
Both exponent terms tend to zero as m tends to infinity, uniformly for b<=1/4. Hence the total variation between Q_N and U^(tensor N), at most sqrt(chi^2)/2, is eventually strictly less than 1/3.

Any test having error at most 1/3 on the null and every alternative would also have such errors for this mixture, forcing total variation at least 1/3. Contradiction. Since b^2=16epsilon^2 and q is fixed, this proves the claimed Omega_q(n log n/epsilon^2) floor, subject to review.

## 5. Quantum and two-source transfer
All these states are diagonal in one common known computational basis. Any collective POVM on N copies is a classical stochastic kernel applied to their N full bitstrings: the kernel entries are the POVM's diagonal entries. Thus allowing collective quantum measurements cannot distinguish the mixture better than those full classical samples.

The second unknown source may be fixed to the uniform Gibbs state, since this is an admitted subclass. It can be simulated freely. A TOTAL-budget-N protocol, including adaptive source choices, uses at most N hard-source samples. The same lower bound therefore holds for the two-source task. The upper-bound access restriction to individual copies is not needed for this particular obstruction.

## Prior and limitations
The q=2 ancestor is [Canonne et al., Testing Bayesian Networks, COLT 2017, Theorem 57 / Section 8.1](https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf), using signed unknown matchings. This note preserves that attribution and supplies the q>=3 component/counting calculation. Its displayed bound does NOT give a logarithmic gain at q=2 because the exponent q-2 vanishes.

The limited search checked combinations of hypermatching, uniformity testing, k-spin testing, and Ising testing n log n. It did not establish novelty or exclude another known general result. Independent review should focus on (i) the component selection equivalence, (ii) sign independence after conditioning on partitions, (iii) exact common-block factorial moments, and (iv) admission and copy quantifiers.

If accepted, the q=3 subclass strengthens the recorded fixed-k>=3 floor from linear n to n log n in the feasible regime. It leaves a large gap to the general n^(2k)/epsilon^4 upper bound and does not close P1. It neither proves a physical preparation procedure nor transfers biological recognition theorems.
