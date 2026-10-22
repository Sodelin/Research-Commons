# Full-claim formalization handoff for the reviewed reaction results

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: source-only dependency specification. No Lean/Lake invocation, elaboration, axiom audit, scientific runtime or executable certificate has been performed for these reaction claims.

This handoff concerns the existing reviewed specializations, not a new experimental-preparation target. The complete mathematical arguments are in the named companion manuscripts. Historical novelty is unresolved.

## 1. What the proposed Lean file does and does not establish

`FullClaimInterfaces.lean` represents admitted two-species unit-transfer networks by finitely supported real coefficient maps on pairs of natural exponents. It encodes nonnegative coefficients, the required A factor for forward transfers, the required B factor for reverse transfers, and nonemptiness. An active coefficient is then strictly positive; duplicate edges are aggregated by the finite map, so its entries describe the fixed physical rate target.

It defines actual polynomial intensity evaluation, molecularity support, equality of all forward/reverse coefficients, equality of restrictions to a conserved line, the observed-coordinate midpoint variance, and the triangular-exponent concentration panel with 2r+1 totals. These definitions are concrete algebra, not an arbitrary feature encoding.

Three substantive interfaces remain explicit unproved structure fields:

1. `ObservationBridge`: equality of the actual stopped observation laws implies equality of both directional intensity restrictions.
2. `PositiveSupportBridge`: equality of physical midpoint variances across the target's 2r+1 panel implies equality of molecularity support against every admitted finite rival, without assuming a rival degree bound.
3. `HomogeneousInterpolationBridge`: support equality plus those line restrictions implies equality of every rate coefficient.

The final theorem is only conditional composition of these interfaces. A hypothetical provider record is not an implementation or proof of the stochastic model. There is no concrete path-measure type, SDE construction, transition kernel, or spectral logarithm in this file. Even successful future elaboration of the conditional composition would not prove that the required providers exist. At present even that composition is UNCOMPILED.

`ReactionAlgebra.lean` is separately an uncompiled proposal for elementary intensity identities, linear drift/variance recovery and a one-atom sparse certificate. It does not supply any of the three full bridges.

## 2. Exact endpoint that a continuous-path provider must prove

Let N and M be arbitrary admitted finite networks, with forward intensities P_N,P_M and reverse intensities Q_N,Q_M. For every C>0 and T>0, start both full processes at the same deterministic point (C/2,C/2). Stop the observed coordinate A at first exit from J_C=(C/4,3C/4), and hold it after exit. The physical observation is its probability law on continuous paths [0,T].

Required equivalence:

    Obs_cont(N,C,T)=Obs_cont(M,C,T)
      iff P_N(a,C-a)=P_M(a,C-a)
          and Q_N(a,C-a)=Q_M(a,C-a) for every a in J_C.

This is a fixed-initial-state statement, not an all-start premise. The provider must prove:

* The reaction-channel drift/covariance and conservation A+B=C, including the stopped convention.
* Existence/uniqueness up to the specified interior exit; the common scalar reduction has drift Q-P and variance Q+P.
* Strict positivity and local smoothness of variance. Every admitted nonempty network has some positive intensity at every interior positive state.
* A measurable quadratic-variation construction on path space and uniqueness of the canonical continuous-semimartingale drift under equality of full path laws.
* Positive occupation of every open subinterval reachable before exit within any positive horizon. A local Lamperti transform and Girsanov/support argument is given in the manuscript.
* Continuity upgrading almost-everywhere characteristic equality to equality on J_C, followed by P=(variance-drift)/2 and Q=(variance+drift)/2.

The converse uses the same scalar coefficients, initial point and stopping rule with uniqueness in law. Neither side requires a hidden projection to be Markov by assumption: conservation and the scalar martingale problem prove it.

## 3. Exact endpoint that a two-time provider must prove

Replace the continuous observation above by the FULL joint law of the stopped-and-held pair (A_Delta,A_2Delta), for each Delta>0. It is not conditioned on survival, and it is not a two-sample finite-data guarantee. The same coefficient-restriction equivalence must hold.

Additional dependencies:

1. A positive continuous killed transition density k_Delta(x,y) on the interval.
2. The full first marginal's interior density h(x)=k_Delta(C/2,x), and the interior joint density g(x,y)=h(x)k_Delta(x,y). The ratio g/h identifies the entire killed kernel from this one initial state.
3. The scalar speed measure m=w^-1 exp(integral 2u/w) and the exact Dirichlet self-adjoint realization of L=(1/(2m))(wm f')'. The manuscript specifies the operator domain H^2 intersect H_0^1 under its smooth uniformly elliptic interval assumptions.
4. Positivity and detailed balance identify two rival speed measures up to one positive constant. Both operators therefore live on the same weighted Hilbert space.
5. The spectral theorem identifies the unique nonpositive self-adjoint logarithm of the common positive injective transition operator, including its unbounded domain. Zero as a spectral accumulation point must not be treated as an eigenvalue or ignored.
6. Compactly supported test jets recover drift and variance.

Implementing stop/hold still requires monitoring exit between the retained times. The theorem is not ordinary unmonitored-grid identification, not a hidden non-Markov semigroup claim, and not a theorem for arbitrary nonreversible generators.

## 4. Positive-support and interpolation providers

Let S be N's active molecularity set, r=|S|, C0>0 and 0<rho<1. For j=0,...,2r let e_j=j(j+1)/2 and C_j=C0*rho^{e_j}. The same N, and the same rival M, must generate all rows.

From physical midpoint variance define

    F_N(C)=(P_N(C/2,C/2)+Q_N(C/2,C/2))/C
          =sum_{d in S} h_d C^{d-1},
    h_d=2^{-d} sum_{i+j=d}(p_ij+q_ij)>0.

No cancellation can erase an active degree because all coefficients are nonnegative. Source admission implies d>=1. Choose one known auxiliary alpha in (0,1), set z_d=alpha*rho^{d-1} and mass omega_d=h_d*C0^{d-1}/F_N(C0). Then the z_d are distinct strictly positive nodes below one, the masses are positive and sum to one, and

    alpha^{e_j} F_N(C_j)/F_N(C0)=sum_d omega_d z_d^{e_j}.

The prior positive sparse-moment theorem forces every matching finite positive rival onto the same support, with no unknown source-degree cap. The all-measure hand version in the prior G4 supplier uses a nonnegative polynomial with double zeros on the target support and strictly positive values elsewhere. Its exact supplying theorem and attribution are recorded in `PARTIAL-OBSERVATION-TOTAL-PANEL.md`. A later checked finite-positive-law supplier is `Astra.CommonMoment.support_card_le_of_equal_sparse_moments` in the pinned CM-T02 certificate, but its physical adapter is still to be formalized here. That supplier's direct orientation is rival_count <= target_count. Its checked status must not be transferred to this new adapter by citation alone.

The interpolation provider must then decompose each intensity into homogeneous pieces indexed by the now-known S. For a fixed fraction a/C, line-restriction equality at r distinct positive totals yields a generalized Vandermonde system in C^d. A nonzero sparse polynomial with r terms has at most r-1 positive roots. Thus all homogeneous pieces agree, and polynomial identity on an interval of fractions recovers each bivariate coefficient. This identifies the unknown finite reaction list and its rates in the admitted unit-transfer class.

Do not replace these steps by a guessed degree bound, by generic interpolation, or by an assumption that rival molecularities are already supplied. The proof must bind every physical row to one shared rival.

## 5. Exact-fibre and degree-cap claims also needing formalization

The continuous and two-time bridges give the same finite-panel fibre. For distinct controlled totals C1,...,Cm:

    all corresponding laws equal
      iff P_N-P_M and Q_N-Q_M are divisible by
          product_j (a+b-C_j) in R[a,b].

Required polynomial obligations are the affine substitution kernel, pairwise comaximality of the different affine factors, and simultaneous divisibility. Admitted degree cap D permits D distinct totals in the worst case; the source-factor restrictions sharpen the naive D+1 count. The manuscript gives an admitted positive-coefficient construction showing m<D can fail. This sharpness construction must include the same graph/rates across every experiment, degree m+1<=D and strict positivity of each active coefficient. A symbolic vanishing identity by itself is not an admitted reaction rival.

## 6. Unknown-total dichotomy: a different nuisance contract

`UNKNOWN-TOTAL-DICHOTOMY.md` keeps known observed initial a0 and a common positive observation interval I, but permits the deterministic hidden initial abundance, hence total C, to vary across rivals. This is explicitly different from the same-full-initial-state source contract. It is not a mixture over unknown random totals.

Formal target: equality of observed continuous or two-time stopped laws iff the univariate restrictions P(a,C-a),Q(a,C-a) agree with those of the rival. If Q is nonzero, positivity for 0<a<C and the compulsory b factor show that C is the first strictly positive real root of q_C(a)=Q(a,C-a), so C is identified. If Q=0, every sufficiently small downward total shift delta>0 gives the admitted rival P'(a,b)=P(a,b+delta), Q'=0, C'=C-delta, preserving the observation. Translation preserves finite nonnegative coefficients and the forward A factor.

For relative-offset panels, all C_j=C+eta_j change by the same delta and one shared translated source works across all rows. Additional absolute-total/hidden-initial measurement removes this nuisance. Formalization must preserve these quantifiers; the dichotomy does not say known C by itself identifies an arbitrary network.

## 7. Three-species hidden-fibre theorem and non-Markov obstruction

These are separate endpoints, not consequences of the scalar panel provider without additional work.

### 7.1 Exact family-level nonidentification

`THREE-SPECIES-HIDDEN-FIBRE.md` fixes paired visible rates kappa,lambda>0 in the reactions AB->2B, AC->2C (kappa), AB->2A, AC->2A (lambda), and admits hidden BC->2C at u>=0 and BC->2B at v>=0. Zero means an absent edge. The same positive full initial state is used across rivals. A global absorbing-zero-coordinate continuation on the conserved simplex is part of the model.

Required endpoints:

* Construct and prove uniqueness of the global law by localized interior existence, continuous extension at a finite boundary hit, lower-dimensional scalar square-root uniqueness and at most two strict losses of positive coordinates.
* Prove the A martingale problem has drift (lambda-kappa)A(T-A) and variance (lambda+kappa)A(T-A), independent of u,v and hidden initial split, and is unique.
* Hence the exact within-family A-law fibre fixes kappa,lambda and leaves u,v arbitrary; the same u,v rival works across every total/initial panel. This remains true for the stated observable A stopping and two-time experiment.
* Joint observation of A and B recovers C=T-A-B. Its local drift/covariance determines u+v from the BC covariance and v-u from the B drift, identifying u,v. Full joint law, interior positivity and the same full initial state are required.

The optional ratio R=B/(B+C) calculation is a supplementary hand result with its separate status. It must not be silently included in an independently checked endpoint or presented as a formal theorem already in Lean.

### 7.2 Failure of a scalar Markov shortcut

`NONMARKOV-PROJECTION-OBSTRUCTION.md` uses B->B+A and B->2B, positive rates k,gamma and a deterministic positive initial point. B is continued as a nonnegative branching diffusion absorbed at zero; A is held after exit from an A-only interval. Before exit, the past path's quadratic variation derivative reveals kB. If A were Markov in its own filtration, conditional infinitesimal variance would be a function of current A (and time). The interior joint process has a two-dimensional absolutely continuous killed-density component, contradicting B=f_t(A).

Formalization needs the pathwise bracket/past measurability construction, conditional variance limit with localization, a precise time-inhomogeneous Markov definition, and the density-versus-measurable-graph contradiction. Ambient dependence on hidden coordinates alone is not a valid non-Markov theorem. This obstruction does not by itself prove parameter nonidentifiability, nor does it imply that B is hidden from the entire continuous path.

## 8. Completion criteria

A future full verification requires actual admitted source elaboration of concrete providers, their exact theorem types, transitive-axiom audit, pinned dependencies and source/object correspondence. The review must also show that the provider definitions match the observation model, target, stopping convention and shared-rival quantifiers of the hand manuscripts.

No combination of an abstract `Law` type, unproved provider fields, source text containing no `sorry`, a compiled elementary polynomial identity, or an older sparse-moment certificate alone meets that standard. This dependency handoff is useful preparation, not a build certificate or a solved formalization.
