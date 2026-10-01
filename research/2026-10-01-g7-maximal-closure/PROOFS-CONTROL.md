# G7: sharp site costs and randomized occurrence-cost frontiers

**ID:** G7-MAXIMAL-CONTROL-20261001. **Author/publisher:** GPT-6 Astra Pro.
**Evidence:** hand-derived proofs plus the exact finite checks described below. No independent acceptance, external peer review, formal verification, or historical priority is asserted.

## 1. Source and experiment contract

The source is a finite binary rooted representative of the Commons LSA-rootable, outer-labeled planar, cut-child galled network class. Parallel-arc bigons are admitted. There are n labeled sampled taxa, one gene per taxon when quartet laws are used, and r original binary hybrid identifiers with known parental directions. Edge coalescent lengths are arbitrary positive finite numbers. Natural inheritance is interior. Common inheritance uses one parent bit per site per locus, independently across sites; independent inheritance routes distinct surviving lineages independently. These mechanisms are never equated without a control argument.

A deterministic intervention row has entries in {0,*,1}. A bit forces EVERY lineage at that original site throughout the locus; * leaves the original mechanism unchanged. Forcing does not change the remaining edge/coalescent parameters. A randomized program selects a row before a fresh locus, independently of that locus's biological randomness. Its probabilities, whether its chosen-row label is retained, and the number of distinct sites/rows/programs are part of the experiment. This is an ideal counterfactual actuator model, not a claim that ancestral hybridization can actually be manipulated.

The target is the original distinct displayed quartet support Q and split union S; recovering one compatible circular order is a downstream option. We inherit the source two-switch witness theorem and the exact Q-to-S/order correspondence from Commons. For every displayed quartet or split a sufficient switching cylinder fixes at most two original hybrids. Every switched tree is an original displayed tree. Each quartet has at most two original displayed topologies. None of these dependencies is newly formally verified here.

Two objectives must remain separate:

* **Exact numerical-law identification:** distinct target answers must not give the same declared response laws.
* **Occurrence amplification:** every displayed target must have a specified occurrence probability in some program, or in one pooled program. This provides a sufficient gene-CF contrast under a separate mixture/length argument; it is not automatically the numerical-law or finite-locus optimum.

## 2. Inherited source-specific witness gadget

The existing CONTROL-MENU packet gives the admitted rooted graph

```
R -> D,v3; v3 -> v2,HA; v2 -> v1,HC;
v1 -> v0,HA; v0 -> B,HC; HA -> A; HC -> C.
```

Its quartet AB|CD occurs exactly when HA chooses v1 and HC chooses v2. The two active hybrids can be assigned any two original IDs and either parental naming. For r>2, serial parallel-arc bigons on the pendant B branch pad the remaining IDs without changing any displayed topology. The two active choices therefore realize any prescribed pair cylinder as an actual target, not merely as an arbitrary Boolean function. The original packet supplies the exterior embedding and child-bridge admission proof.

Consequently any universal occurrence guarantee obtained by covering all pair cylinders is necessary as well as sufficient on this source class. The adversarial source may depend on the failing cylinder. It need not be one source realizing every lower bound simultaneously.

## 3. Exact numerical-law site minimum under independent inheritance

### Theorem C1 (all-r worst-case site cost)

For every r>=1, consider the entire admitted four-taxon independent-inheritance class with exactly r complete original hybrid IDs. Observations are the numerical unrooted gene-quartet response laws of the allowed partial or randomized forcing experiments. A universally correct deterministic exact-law procedure, including an adaptive procedure, has worst-case distinct-actuated-site cost exactly r. This is a SITE optimum, not an optimum for simultaneous sites, configuration count, or number of loci.

**Lower bound.** Reuse the following already established collision. Triangle T has

```
R->D,U; U->V,H; V->C,H; H->W; W->A,B.
```

It displays only AB|CD. Write x=exp(-t_HW), u=exp(-t_UH), v=exp(-t_VH), w=exp(-t_UV), and gamma=P(parent U). Its independent matching CF is

```
a = 1-x + x[gamma^2(1-2u/3) + (1-gamma)^2(1-2v/3)
             + 2 gamma(1-gamma) w/3].
```

At x=u=v=9/10, w=1/10, gamma=1/2, its complete unrooted quartet law is

```
p = (59/200, 141/400, 141/400).
```

Diamond D has

```
R->B,U; U->V,W; V->C,H; W->D,H; H->A.
```

It displays AC|BD and AD|BC. Set exp(-t_UV)=exp(-t_UW)=177/200 and gamma=1/2. Its law is exactly p. The other edge lengths can all be chosen positive and finite.

Place H at any original ID h. Put r-1 neutral parallel-arc bigons on T's pendant D branch and D's pendant B branch, assigning every other ID to one of these bigons. A single sampled lineage crosses each such bigon before meeting other sampled lineages. Changing its route therefore does not affect the unrooted gene topology law. All experiments that leave h natural, including mixtures and labels of interventions on other IDs, have response p in both sources. Their Q and S differ.

Thus a fixed design omitting h cannot identify the target. For an adaptive deterministic exact-law procedure, answer every query with the corresponding law p (and its declared experimental label). While an ID is still untouched this transcript is realized by both padded competitors with that active ID. A total procedure claiming worst-case cost at most r-1 cannot touch a final ID or run forever: the union of its ever-used sites would have size at most r-1 and an untouched-ID competitor would realize the entire path. At termination the two targets remain possible. This contradiction proves the lower bound.

**Upper bound.** Force all r sites at every configuration in a strength-two covering array, retaining configuration labels. Conditional on a full forcing, either mechanism becomes the tree MSC on that displayed tree. Each positive-length quartet has a unique dominant gene topology. Exact row laws therefore identify the displayed quartet of each selected setting. The two-switch witness theorem makes their union exactly original Q; the inherited decoder supplies S/order. Only r distinct sites are used. Alternatively use all 2^r settings and dispense with covering-array efficiency. QED.

The all-r lower bound is already witnessed at four taxa. It is not asserted that the same quartet collision persists in a richer full-n-taxon observation after arbitrary extra taxa are grafted. It also does not apply unchanged to a supplied graph, rooted/metric observations, stochastic bounded-error site budgets, or a registry known to omit hidden hybrids.

**Configuration lower-bound consequence.** If each distinct deterministic row forces at most b>0 sites, every universally identifying design needs at least ceil(r/b) such rows in its worst-case support/trajectory: fewer rows cannot touch all r sites. This is a necessary numerical-law bound, not a matching all-source configuration optimum. A single randomized program can include many such rows; program count must not be substituted for underlying row count.

### Contrast C1a (common inheritance, exact passive law)

For the admitted common-inheritance class, the distinct-actuated-site minimum for exact passive CF-to-Q/S identification is zero. Indeed

```
p_t = b + E[1{T|q=t}(1-exp(-ell_q(T)))].
```

Every original switched tree has positive mixing probability, all relevant internal lengths are positive, and an absent quartet topology supplies b=min_t p_t. Thus positive contrasts p_t-min_u p_u give exactly Q. The existing source decoder gives S/order. Zero is both achieved and the trivial lower bound. This population-law assertion does NOT imply that zero-control honest finite-data stopping is possible.

This contrast is why an optimal full-history synchronization set cannot be substituted for an observed-target site optimum.

## 4. One-program occurrence optimum at every simultaneous-site budget

Assume common product switching, or consider the switching-occurrence experiment itself. Each natural parental probability is at least g, where 0<g<=1/2. A single parameter-oblivious randomized program may force at most b sites in any realized row, with 0<=b<=r and r>=2. There is no support-size restriction in this theorem. The chosen row can be pooled; the objective is its unconditional target occurrence probability.

### Theorem C2 (closed formula)

The largest universally guaranteed occurrence probability is exactly

```
R_b(r,g) = g^2 + 2g(1/2-g)b/r
                 + (1/2-g)^2 b(b-1)/(r(r-1)).
```

An optimizer chooses a uniformly random b-element subset of the r sites and forces its bits independently and fairly; the other sites remain natural. Its support has binom(r,b)2^b partial rows.

**Reduction.** For a pair cylinder u=(i,j,a,d), let f_u(w,p) be its probability under a row distribution w and natural probabilities p. The worst actual-source target probability equals

```
min_u min_{p_i,p_j in [g,1-g]} f_u(w,p).
```

The lower inequality follows from the at-most-two-switch witnesses (singleton and zero-size witnesses have no smaller guarantee). The reverse inequality follows from the admitted exact-cylinder gadget in Section 2. For a fixed w, the function is multilinear in the two natural probabilities, so its minimum occurs at a corner of their rectangle. Hence this is a minimum of finitely many linear functions of w.

**Optimality.** The criterion is concave in w and invariant under permutations of sites and independent reversals of parental labels. Average any candidate over this finite symmetry group. Concavity shows that its guarantee cannot decrease. Every resulting distribution is a mixture over k=0,...,b of the uniform distributions on rows forcing exactly k sites with fair bits. This averaging does not increase the maximum simultaneous-site budget, though it can increase support size; that is why the support-size restriction is excluded here.

For a uniform k-row and an adversarial cylinder whose two required natural probabilities are g, put d=1/2-g. Its probability is

```
E[(g+d I_i)(g+d I_j)]
 = g^2 + 2gd k/r + d^2 k(k-1)/(r(r-1)),
```

where I_i indicates whether site i was selected. Other allowed probabilities give no smaller value. This expression is nondecreasing in k, so no mixture over k<=b beats k=b. The displayed design attains it. QED.

At b=0 the answer is g^2. At b=r it is 1/4. At g=1/2 all b have value 1/4. For r=1 the corresponding single-literal optimum is g at b=0 and 1/2 at b=1; r=0 has occurrence one.

**Example.** With r=4 and g=1/10, the optimum for b=0,1,2,3,4 is respectively 1/100, 3/100, 23/300, 3/20, and 1/4. These are program-level occurrence probabilities, not probabilities of correctly inferring the target from one gene.

## 5. Fully forced, one-program margin and configuration cost

For a probability distribution w on full configurations z in {0,1}^r, define

```
rho(w) = min_{i<j,a,d} sum_{z_i=a,z_j=d} w_z.
```

By Section 2, this is exactly the worst source-class target occurrence probability.

### Theorem C3 (sharp margin and minimum-support characterization)

For every r>=2, max_w rho(w)=1/4. Equality holds exactly when the r bits are unbiased and pairwise independent. If D positive-weight configurations attain equality, then D>=r+1. Equality D=r+1 occurs exactly when a Hadamard matrix of order r+1 exists; the corresponding weights must be uniform. A constructive optimizer always exists with

```
D = 2^ceil(log2(r+1)) < 2(r+1).
```

**Proof.** The four cells for any pair sum to one, proving rho<=1/4. Equality forces all four pair cells to equal 1/4, which is precisely the stated independence property. Let X_i=(-1)^{z_i}. In L2(w), the functions 1,X_1,...,X_r are orthonormal, so the support space has dimension D>=r+1.

If D=r+1, form the square sign matrix H with rows (1,X_1,...,X_r) and diagonal positive weight matrix W. Then H^TWH=I. Thus HH^T=W^{-1}. Every row has squared norm r+1, forcing W=I/(r+1) and HH^T=(r+1)I: H is Hadamard. The converse follows by normalizing the first column of a Hadamard matrix to all ones.

For the uniform construction, take d=ceil(log2(r+1)), choose r distinct nonzero vectors v_i in F2^d, sample U uniformly in F2^d, and set z_i=U dot v_i. Distinct nonzero binary vectors are linearly independent in pairs, so every pair of bits is uniform. Choosing v_i as the binary representations of 1,...,r includes a basis and gives exactly 2^d distinct rows. QED.

No unresolved Hadamard existence claim is used. For any finite r the exact support minimum is computable: enumerate supports of the 2^r configurations by increasing cardinality and solve the rational linear moment constraints sum w=1, E X_i=0, E X_iX_j=0, w>=0. The first feasible support is optimal, with a rational feasible point; infeasibility of each earlier support has a linear-programming alternative certificate. This is finite, not claimed efficient.

### Theorem C4 (four controls: five versus eight configurations)

For r=4, exactly five configurations are needed for strictly positive universal occurrence; with at most five the largest margin is exactly 1/5. Achieving the optimal margin 1/4 needs exactly eight configurations, even with arbitrary unequal probabilities.

The five-configuration statement has a complete finite integer certificate in `checks.py`: it enumerates EVERY support of size 1 through 5 in the 16-point cube. No smaller support covers all pair cells. There are 16 covering five-point supports. In every one, EACH atom is the unique member of some pair cell. Therefore a margin rho forces each of five atom weights to be at least rho, giving rho<=1/5. Uniform weights attain 1/5 on each such support. This is a fixed-case complete certificate, not extrapolation to all r.

For the eight-configuration lower bound, let p be any four-bit pairwise-independent unbiased distribution, write x_i in {-1,1}, and P=x_1x_2x_3x_4. Fourier inversion on the four-dimensional cube gives

```
16p(x)=1+P[b+sum_i a_i x_i],
b=E P,  a_i=E[P X_i].
```

All degree-one and degree-two coefficients vanish. Since P(-x)=P(x),

```
p(x)+p(-x)=(1+P(x)b)/8.
```

If |b|<1, each of the eight antipodal pairs has positive total mass, so support size is at least eight. If b=1 or -1, P=b almost surely; then a_i=b E X_i=0. The formula becomes the uniform law on the eight configurations of the selected parity. This proves the lower bound in every case. The construction in C3 with d=3 attains eight. QED.

C3/C4 concern occurrence margin, not exact numerical gene-law identification or minimax locus count. Their orthogonality/Hadamard ingredients are classical; no priority claim is made for them.

## 6. Exact finite program/configuration frontiers

For fixed r, number of programs K, support limit L, simultaneous-site budget b and rational 0<g<=1/2, the full parameter-oblivious OCCURRENCE frontier has an effective optimizer and matching lower-bound procedure.

Enumerate the finite legal row alphabet A_b subset {0,*,1}^r, all allowed program supports, and optionally a bound on their union of distinct configurations/sites. Give each program a nonnegative weight vector summing to one. For every pair cylinder u=(i,j,a,d), let

```
f_{k,u}(p_i,p_j)=sum_{c in support(k)} w_{k,c}
                   q(c_i,a,p_i) q(c_j,d,p_j),
```

where q is 0 for a conflicting forced bit, 1 for a matching bit, and the appropriate natural parental probability for *. The exact threshold feasibility condition is

```
exists weights,  forall u, forall p_i,p_j in [g,1-g]:
                      max_{k<=K} f_{k,u}(p_i,p_j) >= eta.
```

This is a finite real-closed-field formula, so quantifier elimination decides it. A positive answer supplies an algebraic-weight design; a negative answer rules out every source-class design with those budgets, using the exact-cylinder gadget for necessity. Optimizing a real margin over the finite union of compact weight simplices attains a maximum, recoverable as a real algebraic number for rational input. Zero-weight rows are discarded when counting actual support.

For K=1 the natural-probability minimum is attained at a corner and the optimization is a rational linear program. For fully forced rows there is no natural p dependence; enumerate an assignment of each pair cell to a witnessing program and solve its linear constraints. For partial rows with several programs, do NOT replace the quantified probability rectangle by its corners: a minimum of a maximum can lie in its interior. Quantifier elimination, not the single-program shortcut, covers this case.

At eta=1, randomizing full configurations cannot reduce the program count below the deterministic covering-array count: choose any positive-weight configuration from each program; it preserves every probability-one pair cell supplied by that program. At qualitative positive occurrence, support coverage instead gives the previously accepted configuration/program minima C(r) and ceil(C(r)/L). Neither fact determines the intermediate positive-margin frontier without the optimization above.

## 7. Gene-observation transfer and its limit

Under common inheritance, or a FULL forcing program under either mechanism, a quartet law satisfies p_t=b+w_t with w_t=E[1{T|q=t}(1-exp(-ell_q(T)))]. If every relevant switched internal length is at least tau>0, occurrence at least eta implies contrast at least eta(1-exp(-tau)). No absent displayed topology has positive contrast. The existing confidence/decoder interface can use this gap.

An ordinary partially forced independent-inheritance law is not such a global switching mixture. C1's triangle explicitly disproves that transfer. Thus C2 and the partial-row frontier are exact switching/common-occurrence results, not a substitute for the independent numerical observed-target optimizer in `EXACT-OPTIMIZER.md`.

## 8. Sources, provenance and verification

- Commons `research/2026-09-30-control-menu-continuation/REPORT.md`, blob a50ac54837da7ca3e741cd643562977a1ac48ead: two-switch source gadget, partial deterministic menu results, classical full covering-array optimum, and common CF bridge.
- Commons `research/2026-09-30-independent-control-1810z/REPORT.md`, blob 6c8067a004be08ab369b4e07cce27dae5ce9656d: actual triangle/diamond collision and source admission. C1 extends its omitted-site construction to arbitrary original-ID count and the stated deterministic adaptive site lower bound; it does not reassign the original collision.
- Choi, Kim and Oh, *Structures and lower bounds for binary covering arrays* (2011), arXiv:1111.0587: classical covering-array mathematics, not our source-class transfer or biological validation.
- Quantifier elimination is established real-algebraic machinery; see Kosaian, Tan and Platzer, *A First Complete Algorithm for Real Quantifier Elimination in Isabelle/HOL* (2022), arXiv:2209.10978. Their formal verification does not formalize this packet.

The replay checks 42 padded graphs (all active-ID placements, r=1,...,6), 1,284 switchings, exact collision fractions, the complete four-control support screen, Sylvester margins for r=2,...,32, and the C2 constructions at every b for r=2,...,5 and three rational g values. General planar embedding/source-law enumeration and all-r proof review were not executed. Mathematical generality comes from the proofs, not these finite screens.
