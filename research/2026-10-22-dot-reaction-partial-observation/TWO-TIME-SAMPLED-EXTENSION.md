# Two fixed sampling times suffice for the stopped scalar specialization

Author: dot (OpenAI).
Date: 22 October 2026 UTC.
Status: complete author-checked hand proof; scoped coordinating hand-review PASS on 22 October 2026.
Formal verification: not performed.
Novelty: unresolved. Scalar spectral identification is classical prior work.

## 1. Exact claim and observation change

This note strengthens the observation contract of [the controlled-total reaction theorem](PARTIAL-OBSERVATION-TOTAL-PANEL.md). It retains the same two-species unit-conversion reaction class, known controlled total C, common initial state (C/2,C/2), and stopping at the first exit of A from J_C=(C/4,3C/4), followed by holding the path constant. The unobserved coordinate remains reconstructible as B=C-A.

Fix any Delta>0. Instead of the continuous path law, suppose the data for experiment C are only the exact joint probability law of

    (A_{Delta wedge tau_C}, A_{2 Delta wedge tau_C}).

The theorem below proves that these data determine the same drift and variance on J_C, and therefore the same complete observational fibre, as the continuous stopped path law. All controlled-total conclusions then survive: D distinct totals suffice under a common degree cap D, and 2r+1 geometric or triangular-geometric totals identify a target with r active molecularities against every finite-degree rival.

This is two sampling times in an exact population-law experiment, NOT two realized observations from one trajectory. The joint law is required; two unpaired marginal distributions are not substituted. The stopping/holding protocol remains part of the experiment. Fewer retained observation times do not remove the monitoring needed to implement that stop/hold record, and do not give a two-sample statistical guarantee. No claim is made for an unmonitored free diffusion observed only on a grid, for which paths can leave and re-enter between samples. The stopping time itself and the unsampled path are not included in the data.

## 2. Classical sources and what is reused

[Kent (1978), Time-Reversible Diffusions](https://www2.stat.duke.edu/~sschmid/Courses/Stat376/Papers/Langevin/KentAdvAppProb1978.pdf), Theorem 8.1, records the symmetry of a one-dimensional nonsingular diffusion's transition density relative to its speed measure, including killing in the interval formulation. The boundary and speed-measure framework is explicit in Sections 8–9.

[Gobet, Hoffmann and Reiss (2004), Nonparametric estimation of scalar diffusions based on low frequency data](https://arxiv.org/pdf/math/0503680), equations (1.1)–(1.2) and Section 3.1, describes fixed-lag transition-operator identification through the exponential of a self-adjoint generator. Its statistical results use reflecting boundaries and an ergodic framework. Those estimation theorems are not invoked for this killed experiment. The paper credits earlier spectral identification work, including Hansen, Scheinkman and Touzi (1998).

Thus, uniqueness from a scalar diffusion's fixed-time transition operator is not proposed as a new theorem here. The work below supplies the precise one-start, two-time, interior-stopped observation reduction and joins it to the already stated reaction/G4 positive-support adapter. No existing scalar spectral method is being renamed as a new general hidden-state result.

The earlier primary paper [Hansen, Scheinkman and Touzi (1998), Spectral methods for identifying scalar diffusions](https://larspeterhansen.org/wp-content/uploads/2016/10/Spectral-Methods-for-Identifying-Scalar-Diffusions.pdf), explicitly treats nonparametric identification from discrete-time data under its scalar stationary framework. Its historical priority for the spectral method is retained here.

## 3. Scalar assumptions and the killed kernel

Let J=(l,r) be a finite connected interval, and x_0 in J. Consider a time-homogeneous scalar diffusion with generator

    Lf(x)=u(x) f'(x)+(1/2) w(x) f''(x),

where u,w are smooth on a neighborhood of the closure of J and w>0 throughout that closure. Let tau be its first exit from J and set Xbar_t=X_{t wedge tau}, holding at the reached endpoint after exit. These assumptions hold for every target and every rival in the controlled-total reaction class.

The killed transition operator is

    K_t f(x)=E_x[f(X_t) 1_{t<tau}],  x in J.

It has a continuous, strictly positive interior Lebesgue density k_t(x,y) for t>0 and x,y in J. Smooth uniformly elliptic Dirichlet heat-kernel theory gives continuity; strict positivity follows from the parabolic strong maximum principle, or from the Lamperti transform and positive killed Brownian bridge densities. The smooth coefficients and uniform ellipticity on this bounded interval are the relevant hypotheses. No stationary distribution is required for the killed process.

For interior x,y, the stopped process has the same transition density k_t(x,y). Boundary mass of the stopped process records trajectories already absorbed at an endpoint, and is excluded when passing to K_t. We do not confuse the conservative stopped kernel on the closed interval with the sub-Markov killed kernel on J.

## 4. Recovering a one-step kernel from one initial state

**Lemma 1 (two-time kernel extraction).** If two such diffusions, from the same x_0, have equal joint laws of (Xbar_Delta,Xbar_{2 Delta}), then their killed transition kernels K_Delta are equal for all initial points in J.

**Proof.** Equality of the joint laws implies equality of the first marginal. Its density on J is

    h_i(x)=k^i_Delta(x_0,x),

for model i=1,2. The densities are continuous and strictly positive, so their almost-everywhere equality implies h_1=h_2=h>0 everywhere in J.

By the Markov property and the stop/hold convention, the joint density restricted to J x J is

    g_i(x,y)=h_i(x) k^i_Delta(x,y).

This formula excludes paths absorbed before either sampling time. Equality of the full joint law gives equality of g_1 and g_2 almost everywhere; continuity makes the equality pointwise. Divide by h(x)>0 to obtain k^1_Delta(x,y)=k^2_Delta(x,y) for every x,y in J. QED.

The first marginal used here is the marginal of the full stopped pair law, including possible second-coordinate boundary values. Conditioning the data on survival to time 2 Delta would change this formula and is not an authorized substitution.

## 5. Recovering the generator without a small-time limit

**Lemma 2 (fixed-time scalar killed-kernel identification).** Under the assumptions of Section 3, equality of K_Delta for a single Delta>0 implies equality of u and w throughout J.

**Proof.** For each model choose a positive speed density

    m_i(x)=w_i(x)^(-1) exp(integral from x_* to x of 2u_i(s)/w_i(s) ds),

where x_* is any common reference point in J. Each m_i is smooth and bounded above and below by strictly positive constants on the closure. It satisfies

    (w_i m_i)'=2u_i m_i,
    L_i f=(1/(2m_i)) (w_i m_i f')'.

With Dirichlet boundary conditions, L_i is self-adjoint and nonpositive on L^2(J,m_i dx). One direct justification uses the closed form

    E_i(f,g)=(1/2) integral_J w_i f' g' m_i dx,
    domain(E_i)=H_0^1(J).

Uniform ellipticity and bounded positive m_i give the usual closed coercive Dirichlet form. Its self-adjoint generator has domain H^2(J) intersect H_0^1(J), acts by the displayed differential expression, and is the killed diffusion generator by uniqueness of the smooth Dirichlet parabolic problem. This specifies the extension and boundary conditions; formal integration by parts alone is not being used to choose an unspecified self-adjoint extension.

Consequently the killed kernels obey detailed balance:

    m_i(x) k^i_Delta(x,y)=m_i(y) k^i_Delta(y,x).

By hypothesis the two kernels are one common strictly positive function k. Divide the two detailed-balance identities. For every x,y in J,

    m_1(x)/m_2(x)=m_1(y)/m_2(y).

Thus the speed densities differ only by a positive constant. Rescaling one of them, both generators are self-adjoint nonpositive operators on the same Hilbert space H=L^2(J,m dx).

Let K be their common bounded transition operator on H. Semigroup theory gives

    K=exp(Delta L_1)=exp(Delta L_2).

The exponential is injective on the real line. By the spectral theorem, a nonpositive self-adjoint generator is uniquely recovered as

    L_i=Delta^(-1) log K.

This uses unbounded Borel functional calculus. Zero can be an accumulation point of the spectrum of K but is not an eigenvalue, since exp(Delta lambda)>0 for every finite real lambda. The logarithm therefore has its uniquely determined dense domain. Equivalently, the regular Dirichlet operators have compact resolvent; the eigenvalues of K are positive, and taking their real logarithms recovers the generator and its domain. There is no choice of complex logarithm branch and no assertion of uniqueness among arbitrary non-self-adjoint Markov generators.

Hence L_1=L_2 as self-adjoint operators. Every compactly supported smooth test function belongs to both domains. Equality of L_1 f and L_2 f in H, together with continuity, makes their differential expressions equal at each interior point. At an arbitrary x choose compactly supported test functions with jets (f'(x),f''(x))=(1,0) and (0,2), respectively. These recover u_1(x)=u_2(x) and w_1(x)=w_2(x). QED.

## 6. Complete two-time theorem

**Theorem 3.** For two scalar diffusions satisfying Section 3 and sharing x_0, J, and Delta>0, the following are equivalent:

1. Their joint stopped pair laws at times Delta,2 Delta are equal.
2. Their killed kernels at time Delta are equal.
3. Their drift and variance coefficients are equal on J.
4. Their stopped continuous path laws are equal on every finite horizon.

**Proof.** Lemmas 1 and 2 give (1)->(2)->(3). Localized uniqueness gives (3)->(4), and taking the two-time marginal gives (4)->(1). QED.

**Corollary 4 (sampled reaction-network identification).** In the reaction class of the controlled-total theorem, replace every continuous path-law experiment by the exact joint law of the stopped pair at Delta,2 Delta, for one common fixed Delta>0. Then:

- At a prescribed total C, equality is equivalent to divisibility of both intensity differences by a+b-C.
- At m distinct totals, equality is equivalent to divisibility by product_j(a+b-C_j).
- Under a common molecularity cap D, D distinct totals identify the graph and rates, and the previous worst-case sharpness construction remains valid.
- For a target with r distinct active molecularities, the 2r+1 totals C_j=C_0 rho^j, j=0,...,2r, identify the exact graph and active rates against every finite-degree rival. The triangular exponents j(j+1)/2 also work.

**Proof.** Conservation first proves that the observed A process is the scalar diffusion of Section 3. Apply Theorem 3 separately at each total, always to the same fixed rival source. Theorem 2, Corollary 3, and Theorem 5 of the controlled-total proof then apply without any further assumption on rival size. The variance response F(C) used for G4 is now recovered through the killed transition operator and its self-adjoint logarithm, not through a directly observed quadratic-variation path. QED.

## 7. Why this does not settle general discrete hidden-state observation

The proof depends on a scalar Markov process with positive interior transition density and a known regular absorbing boundary protocol. Conservation and the known total supply that scalar process here. For a genuinely unreconstructed hidden species, the observed coordinate need not be Markov; the factorization in Lemma 1 then fails. Even for a fully observed multidimensional process, a common self-adjoint speed-measure representation is not automatic. The scalar spectral logarithm argument cannot be asserted for a general nonreversible hidden model.

The result does not use reflected boundary dynamics. It neither replaces the original stop by reflection nor specifies a global nonnegative chemical Langevin continuation beyond the positive orthant. A different reflection rule, free evolution with missed excursions, interval censoring, rounded concentrations, or unknown observation times is a different experiment.

Exact identification also does not imply stable numerical inversion. Spectral logarithms amplify small high-frequency errors; the cited low-frequency literature studies related inverse-problem difficulty under its own statistical assumptions. No finite-sample guarantee, implementable exact law oracle, or bound on experimental repetitions is supplied here.

## 8. Review status

Scoped coordinating hand-review PASS was completed separately for this extension on 22 October 2026. The review checked the full stopped-pair first marginal, strict interior density, Markov quotient, Dirichlet form and operator domain, common speed measure, self-adjoint logarithm including its zero-spectrum issue, compact test jets, and same-rival multi-total composition. It does not certify generic nonreversible or hidden-state models, an unmonitored-grid protocol, historical novelty, or Lean verification. No runtime evidence is claimed. Classical scalar diffusion identification and the G4 positive-measure theorem are expressly credited.
