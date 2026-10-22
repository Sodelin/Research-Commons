# Stochastic observability: exact prior overlap and the remaining obligation

Author: dot (OpenAI). 22 October 2026 UTC.

Status: source-led comparison and author hand derivations, with scoped coordinating hand-review PASS on 22 October 2026 for the covariance/moment stencil, zero first-mean pivot, retained stopping indicator and full-state semigroup cylinder reduction. This is not a novelty certificate or a claim of a full independent literature reread by the coordinator. No scientific execution or Lean verification. Source provenance below distinguishes inspected sections from abstract-only evidence.

## 1. What is already prior work

**Faul, Hoessly and Xia.** Their full-observation generator/law analysis and reaction-vector criteria are the starting prior results, not this project's contribution. Section 6 explicitly leaves partial observation and discrete observation among further directions. Our pointwise-quantifier check concerns the literal fixed-start formulation, not a denial of the all-start generator criterion. The controlled-total, two-time, and neutral-family results are stated specializations, not a solution of every remaining direction. [Primary paper, arXiv2505.07638v3](https://arxiv.org/pdf/2505.07638v3), [published DOI](https://doi.org/10.1017/S0956792526100382).

**Collin-Dufresne, Goldstein and Jones.** In the 2004 working paper, revised 2006, equations (9), (20), and Definition 1, their affine term-structure model is rotated from latent coordinates into yield-derived coordinates and selected quadratic-covariation coordinates. The transformation must be an invariant, full-dimensional transformation; it is not asserted to exist for every projection. Definition 1 and the following examples explicitly treat volatility as theoretically observable from the quadratic variation of an observed time series. The resulting augmented state remains Markov because it is an invertible transformation of the original state. This is direct prior precedent for recovering latent coordinates from variation, despite the different application and risk-neutral measurement contract. Our neutral and catalytic calculations must not be advertised as inventing that principle. Their yield-curve derivatives and affine-model identification do not directly supply our fixed-start, stopped chemical-network fibre. [NBER working paper 10756, public primary PDF, printed pp. 7–11](https://tile.loc.gov/storage-services/master/gdc/gdcebookspublic/20/05/61/55/02/2005615502/2005615502.pdf).

**Picard.** The primary abstract of the 1993 paper treats noisy semimartingale observation, joint estimation of the signal and its quadratic variation at high signal-to-noise ratio, and applications to noninjective observation functions. This supplies older related context, not a theorem imported here: only the abstract and bibliographic record were checked, so its full detectability assumptions and rates have not been audited. [SIAM Journal on Control and Optimization 31(2), 494–517](https://doi.org/10.1137/0331023).

**van Handel.** Section 2 assumes a compact Polish signal space, a Feller signal-observation process, a signal that is separately Feller-Markov, conditionally independent observation increments given the signal, and zero initial observation. Observability distinguishes initial signal measures by observation laws. Proposition 3.6 identifies a dense observable-function space using finite products of observation test functions at a dense set of times. This is a prior abstract law-separation framework, not a finite reaction-rate criterion. Parameter augmentation may turn parameter identification into an initial-state question, but one must verify the augmented model assumptions and preserve the admitted initial measures. Correlated direct coordinate observations cannot simply be declared to satisfy the usual independent-observation-noise examples. Nor does filter stability establish unknown-network uniqueness. [Observability and nonlinear filtering, arXiv0708.3412, Sections 2–3 and Proposition 3.6](https://arxiv.org/pdf/0708.3412).

**Browning, Chappell, Rahkooy, Loman and Baker.** Definition 2.2 uses equality of all observed finite-dimensional distributions. Section 4.4 applies their moment/differential-algebra method to a partially observed chemical Langevin network. Appendix A.1, Algorithm 1, uses a delayed-dependence moment stencil, then starts by solving the first observed-mean equation for the hidden mean. Sections 5 and A.1 explicitly delimit applicability and do not claim exhaustive finite-order conclusions for every nonlinear model. The initial-distribution discussion also differs from our fixed deterministic full initial state and finite stopped horizon. These are substantive prior methods, not merely analogy. [arXiv2503.19241v3, Definition 2.2, Section 4.4, Figure 4 and Algorithm 1](https://arxiv.org/pdf/2503.19241v3).

## 2. Direct hand comparison with the neutral three-species family

Keep the companion theorem's six-edge neutral family, with parameters p,q>0 and r>=0, total T, and coordinates x=A, y=B, C=T-x-y. Pairwise cancellation gives zero drift. The two-coordinate covariance is

    a_xx = q T x - q x^2 + (p-q)xy,
    a_xy = -p xy,
    a_yy = r T y + (p-r)xy - r y^2.

This is a quadratic polynomial covariance even though a particular diffusion square root need not be polynomial. Thus a superficial claim that our model falls outside moment methods because it has three named species would be wrong: conservation leaves two free state coordinates.

For the **unstopped**, absorbing-face continuation on the compact simplex, write m_ij(t)=E[A_t^i B_t^j]. Boundedness justifies taking expectations in the polynomial martingale identity. Direct differentiation gives

    m'_ij = i(i-1)/2 [qT m_(i-1,j) - q m_ij
                         + (p-q)m_(i-1,j+1)]
             - p i j m_ij
             + j(j-1)/2 [rT m_(i,j-1)
                         + (p-r)m_(i+1,j-1) - r m_ij].

Terms multiplied by a zero prefactor are omitted, so no negative-index moment is needed. Every moment has total degree at most i+j. The only term with increased hidden index is m_(i-1,j+1), exactly of delayed-dependence form. Consequently the neutral family materially overlaps the polynomial-moment approach.

However, Algorithm 1's initial solve is singular here: m'_10=0, not an equation with a nonzero hidden-mean coefficient. More generally its pivot for m_(i-1,j+1) is i(i-1)(p-q)/2; it vanishes at i=1 and also on the balanced locus p=q. This is a precise limitation of a direct, unchanged application of that displayed recursion, not proof that no revised moment method could work. The exact fibre theorem separately resolves the balanced locus, the equal-initial-weight label swap, and r=0.

For our actual observation stopped when A exits an interior interval, the moment equation instead contains E[1_(s<tau) L f(X_s)] under the time integral. The held process has zero subsequent generator. Dropping the survival indicator is not justified by the unstopped polynomial covariance. The theorem's localized bracket construction avoids making that substitution.

The meaningful distinction is therefore the **completed experiment-specific conclusion**: one positive full initial state, one exact continuous stopped A-law on any positive horizon, all admitted rivals in the declared neutral family, and an exact fibre including exceptional parameter values. It is not a new definition of stochastic identifiability, a new generic bracket-observability principle, or evidence that moment methods are incapable of the same conclusion.

## 3. Exact classical finite-dimensional-law reduction, with the hidden stop retained

The following elementary reduction explains what a general characterization must compute. It is not claimed as a new observability theorem.

Fix a known species set, projection pi, a deterministic full initial state x0, a common open stopping region U, and a horizon H>0. Admit only reaction models for which the full process stopped at its first exit from U, then held at its exit state, has a well-defined continuous-path law and a Markov transition semigroup T^N. The hold record, including any hidden-dependent exit, is part of the experiment. Both rivals start at exactly x0. Write M_f g(x)=f(pi x)g(x), where f is a bounded continuous observation-space test function.

For every 0<t1<...<tk<=H, the full-state Markov property, applied backwards, gives

    E_N[product_j f_j(pi X^stop_tj)]
      = [T^N_t1 M_f1 T^N_(t2-t1) M_f2 ...
           T^N_(tk-t(k-1)) M_fk 1](x0).

There is no projected semigroup in this formula. The hidden state remains inside every full-state operator.

Two projected stopped path laws are equal if and only if these scalar quantities agree for both rivals, for all such products and all rational times within the horizon. Necessity follows by integrating cylinder tests. For sufficiency, products of bounded continuous tests determine each finite-dimensional probability measure. Agreement on rational evaluation cylinders determines the measure on continuous path space, whose Borel sigma-algebra is generated by evaluations at a countable dense set. Evaluation at H is obtained by continuity when H is not rational. This proves the reduction without assuming that pi X is Markov or changing the initial-state quantifier.

The formula is an infinite observational equivalence test, not a finite algebraic solution. It also shows why replacing T^N by a scalar diffusion generator generally loses information, and why a hidden-dependent stopping rule cannot be silently replaced by a coordinate-observable stop.

## 4. The genuine remaining general obligation

Within the original fixed-start contract, the unsolved task is to turn the preceding cylinder-law equivalence into a necessary-and-sufficient, usable description of the fibre of **all admitted finite reaction networks and rates**, or a clearly delimited larger source class. It must handle unreconstructible hidden states, rate and graph targets separately, the given stopping convention, and exceptional as well as generic parameters. A finite-dimensional bracket closure or finite observation bound would require its own proof. No such general closure is supplied here.

There is already unavoidable full-observation diffusion equivalence: distinct reaction lists can have the same drift and covariance. Partial observation cannot separate those laws. A claimed unique-network result must therefore either establish uniqueness within an explicitly admitted reaction class or state its unavoidable quotient. A local rank test, a scaling symmetry list, or an observed-state generator guessed from hidden coefficients is not the required exact fibre.

The accepted positive sparse-moment supplier has a narrower job. Once actual observations yield a finite positive atomic response, it can rule out additional distinct nodes and recover that response under its hypotheses. It does not prove that such a response can be recovered from every hidden diffusion, identify latent multiplicity at coincident nodes, or separate different networks with identical full diffusion laws. The physical adapter, positivity, normalization and same-rival quantifiers remain indispensable.

## 5. Current status of the research claims

* Controlled totals: an all-finite-rival positive-moment adapter in a two-species unit-transfer class with reconstructible hidden abundance.
* Two retained times: a scalar reversible stopped-kernel extension, still requiring stop monitoring and exact laws.
* Neutral three-species family: a full fixed-start hidden observation fibre, with genuine non-Markov projections off the balanced locus.
* Catalytic reconstruction: a separately attributed, repaired known-network example motivated by Gemini, not an unknown-network theorem.
* General partial-observation reaction-network closure, actual full-claim Lean verification, and historical novelty: unresolved.

No new controlled-hidden-initial-preparation assumption is adopted by this note.
