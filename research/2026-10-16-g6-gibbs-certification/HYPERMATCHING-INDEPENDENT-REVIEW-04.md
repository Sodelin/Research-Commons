# Independent review of the signed hypermatching Gibbs-testing lower bound
Date: 2026-10-16. Independent hand review prepared by dot for Nolan.

## Verdict and exact object
**Scoped PASS.** No blocking mathematical defect was found in the stated fixed-q, admitted-temperature, constant-error lower bound. This is a source and hand-proof review, with no independent execution, exhaustive experiment, Lean verification, novelty determination, or general P1 closure.

Reviewed candidate:
- [HYPERMATCHING-CANDIDATE-03.md](https://github.com/Sodelin/Research-Commons/blob/baacfd78289f1b1b6c922eb172d5e32c206cdef3/research/2026-10-16-g6-gibbs-certification/HYPERMATCHING-CANDIDATE-03.md).
- Commit baacfd78289f1b1b6c922eb172d5e32c206cdef3; Git blob d25d147048bb14467dec2c9cc687a824e3581e72.
- The [frozen source-class checkpoint](https://github.com/Sodelin/Research-Commons/blob/ec136c4e6056e9901a67db082eb1d4e5349d85d7/research/2026-10-16-g6-gibbs-certification/SCOPED-LOWER-BOUND-CHECKPOINT-01.md) was read separately.

## 1. Source admission and every-instance separation
The Hamiltonian uses disjoint q-body Z strings and coefficient magnitude atanh(t)/beta, with t=4 epsilon/sqrt(m). Thus beta>=atanh(t)>0 is exactly sufficient for every nonidentity coefficient to be at most one. No identity term is introduced. The Gibbs density relative to uniform factorizes exactly, rather than replacing an exponential by a linear approximation.

For each fixed partition and fixed signs, the m block parities under uniform are independent Rademacher variables. Orthogonality of their characters gives the displayed remainder second moment. The bound exp(b^2)-1-b^2<=b^4 holds throughout b<=1/4. Holder interpolation gives E|S| >= (ES^2)^(3/2)/(ES^4)^(1/2) >= sqrt(m/3). Consequently
  ||P-U||_1 >= b/sqrt(3)-b^2 >= epsilon(4/sqrt(3)-1) > epsilon.
The middle inequality uses epsilon<=1/16. Every prior member is therefore far in full L1, hence in full trace norm for these diagonal states. The prior does not rely on merely average separation.

## 2. Exact component selection, including parallel edges
Each original coordinate occurs in exactly one left and one right block. In a Fourier expansion, its parity is even if and only if those two block-selection indicators agree. Equality propagates along each connected incidence component, and conversely a union of whole components satisfies every coordinate constraint.

Parallel incidence edges are retained; they represent different coordinates and create no extra selection freedom. Counting q times the left and right vertex numbers proves that each component has equally many blocks on both sides. A component with one left and one right vertex is exactly a common q-element block, joined by q parallel incidence edges.

Conditional on both partitions, each component sign uses a disjoint, nonempty collection of independently drawn block signs from the two prior draws. Each product is a fair sign and the products are independent. Even coincident blocks have independent signs between the two draws. Thus sign averaging of the Nth power gives the exact product of f_N factors stated in the candidate. The signs and partition of an actual alternative are chosen once, before all samples.

## 3. Dependent common-block moments
For any prescribed l blocks, partition counting gives
  Pr(all occur in M')=(q!)^l (m)_l/(qm)_(ql).
Multiplying by binom(m,l) yields exactly the candidate's factorial moment. This includes l=0 and l=m.

For k=m-i>=1, each qk-j, 0<=j<=q-1, is at least k. Grouping factors therefore proves
  (qm)_(ql)>=(m)_l^q.
Also the average of the first l terms of log m,...,log 1 is at least the average of all m terms; log(m!)>=m log m-m gives (m)_l>=(m/e)^l. Since q>=3, these inequalities imply
  E binom(L,l) <= [q! exp(q-2)/m^(q-2)]^l/l!.
The binomial expansion at a>=1 has nonnegative terms, so summation gives the claimed exponential moment bound without an independence assumption about common blocks.

## 4. Chi-square bound and uniform quantifiers
The elementary inequalities (1+u)^N<=exp(Nu), (1-u)^N<=exp(-Nu) give f_N(u)<=cosh(Nu). For all remaining components r>=2, t^(4r)<=t^8; there are at most m components. Thus the residual factor is bounded by exp(N^2 m t^8/2).

At N<=c m log(m)/b^2, a=f_N(t^2)<=m^c and
  N^2 m t^8/2 <= c^2 b^4 log^2(m)/(2m).
Combining the factors gives the exact displayed upper bound in the candidate.

To make the theorem's threshold quantifier explicit, choose c=(q-2)/2. Since b^4<=1/256, the exponent is at most
  c^2 log^2(m)/(512m) + C_q m^(-(q-2)/2).
This tends to zero with a threshold depending only on q, uniformly in 0<epsilon<=1/16. Choosing that exponent below log(13/9) makes chi-square<4/9 and total variation<1/3. No numerical threshold is extracted here. Integer floors do not affect the asymptotic rate.

The temperature condition is pointwise: the conclusion is asserted only when beta>=atanh(4 epsilon/sqrt(m)). For a fixed beta>0 this holds eventually, but no uniform lower bound at beta=0 follows. For arbitrary n, m=floor(n/q) and fewer than q uniform spectators preserve both distances and the testing reduction; m log m is Theta_q(n log n) for sufficiently large n.

## 5. Testing, quantum measurements, and total budget
A test whose rejection probabilities differ by at least 1/3 between the null and every alternative would have the same gap for the fixed-prior mixture. Its error guarantee therefore forces total variation at least 1/3. This contradicts the strict upper bound above. The factor one-half in TV<=sqrt(chi-square)/2 and the use of full trace norm for separation are consistent.

On diagonal states, every collective POVM is exactly a stochastic channel of the full computational-basis sample string, by taking its diagonal entries. An adaptive protocol likewise defines a parameter-independent channel from a pre-drawn list of up to N hard-source bitstrings, together with its internally simulated uniform-source state/samples and internal randomness. No measurement advantage is lost in using the full classical samples for a lower bound.

Fixing the second source to the maximally mixed state is an admitted subclass, even though the full problem leaves both sources unknown. It can be generated without hard-source queries. Thus a worst-case TOTAL-copy budget N implies at most N hard-source draws, including adaptive source selection. The proof is for a bounded total budget; it does not separately establish an expected-stopping-time lower bound.

## 6. Prior and remaining scope
The primary [Canonne–Diakonikolas–Kane–Stewart paper, Theorem 57 and Section 8.1](https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf) was inspected. Its signed unknown-matching construction is the correctly attributed q=2 ancestor. This review does not establish whether the q>=3 consequence has appeared elsewhere.

The primary [Bluhm et al. source, Theorem 17](https://arxiv.org/html/2603.29809v1#S4.SS2) was inspected for the Gibbs coefficient cube, known common beta, trace norm, and two-unknown-source task. The candidate is an admitted hard subclass. It is a constant-error information-theoretic lower bound, not a matching upper bound or a preparation algorithm. It strengthens the recorded floor for fixed k>=3 in the stated feasible regime; general P1 remains open.

## Evidence boundary
All checks above are symbolic hand deductions from the immutable candidate and the cited primary definitions. No source code was executed, no experimental frequency is claimed, and no numerical search or formal proof certificate is supplied. Candidate status and authorship remain preserved in its original bytes.

