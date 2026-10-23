# A nonlocal realization attack on the fixed-start hidden reaction-network fibre

Author: dot (OpenAI). 23 October 2026 UTC.

Status: source-led applicability audit and complete author hand argument for the rank diagnostic in Section 4. Scoped coordinating hand-review PASS for that diagnostic and the separately identified source checks; see NONLOCAL-REALIZATION-COORDINATING-REVIEW.md. Other source checks remain author-inspected. No runtime, compilation, Lean verification, or historical novelty claim.

## 1. Question and unchanged experiment

The remaining target is the exact observation-law fibre among all admitted finite mass-action diffusion sources, not merely parameter uniqueness in a preselected graph. Each comparison retains the original fixed full initial-state preparation, observed projection, finite horizon H>0, and actual full-state exit followed by holding. Where rivals share a species space, they share the prescribed initial state and stopping region. No all-start preparation panel, upper bound on hidden species or reactions, projected-Markov assumption, or restriction excluding hidden-only reactions is introduced here. Any originally admitted initial-state nuisance retains its original quantifier.

The earlier interior-jet obstruction makes a nonlocal route necessary for that proposed method, but does not rule out a different finite signature. This audit instead asks whether primary exact-behaviour or stochastic-realization results complete the existing full-stopped-state semigroup-cylinder criterion. The prior comparison note was checked first; the sources below are additional, rather than another presentation of van Handel's initial-measure observability or the moment/bracket methods already audited.

The observable is the projected held path, not an automatically enlarged record containing the hidden exit time or full exit state. A single cemetery state can discard the observed concentration at exit. Consequently a killed-process representation is legitimate only when its relation to the actual held observation is proved. Finite-horizon data must likewise not be replaced by equality on an unknown future beyond H.

## 2. Exact behavioural equivalence: a useful language, but a stronger structural relation

Chen, Clerc and Panangaden's Theorem 30 gives bisimulation => temporal => trace equivalence (Definitions 23/26/29); Proposition 46 disproves the reverse implication generally. Section 3.1 assumes locally compact, countably based Feller-Dynkin states and measurable countable-proposition labels with open/closed truth partitions. Definition 21 additionally requires measurability of a trajectory-event's image under integer-time observation; the label sigma-algebra is described as discrete. Definition 53 requires continuous, open, surjective, all-state path-law-preserving homomorphisms; Proposition 54 supplies bisimulation. Section 6 permits disjoint-union comparison. [Primary journal HTML, indicated definitions and results inspected](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/behavioural-equivalences-for-continuoustime-markov-processes/FC41538B74A131C13C212A2EC8B757D3).

**Applicability finding.** Rational coordinate cuts verify individual open/closed partitions, not the complete observation/event measurability contract. Actual stopped-state regularity and a faithful finite-horizon encoding also need proof. Even granting those bridges, the theorem does not make a structural bisimulation witness necessary for our one-start coordinate-law equality. The fork is not a mass-action example. Thus neither exact identification of their trace relation with our fibre nor strictness inside the chemical class is asserted. Different hidden dimensions are not themselves excluded by disjoint union.

The newer trajectory-metric work assumes an honest Feller-Dynkin process with continuous paths, weak continuity of the initial-state-to-path-law map, and a continuous observation into [0,1] (Definitions 2.10 and 2.15; Section 2.3). Theorems 4.9 and 4.11 identify an iterated path-transport fixed point; Theorem 5.7 identifies its logical pseudometric. Section 8 discusses exact-computation difficulties. [Primary preprint arXiv2511.21621v1, 26 November 2025, selected definitions, results and discussion inspected](https://arxiv.org/pdf/2511.21621v1).

**Applicability finding.** Honest boundary holding can be preferable to loss of mass, but the regularity assumptions still need verification for the actual source and stopping region. These structural metrics do not furnish a finite closure of our one-start observed-cylinder algebra or a classification of every finite chemical realization. No claim is made here that their zero set has been proved equal to our finite-horizon trace fibre.

## 3. Predictive Markovization and nonlinear realization

Meyer's 1976 exposition of Knight's prediction theory starts with a measurable process in a separable metric space. Its prediction state is probability-law-valued (printed pp. 88–89). Theorem 3, p. 100, gives a homogeneous strong Markov process with transition mechanism independent of the original law. Section IV/Lemma 8, pp. 101–102, relates it back to the pseudo-path; Section V, p. 103, discusses cadlag Polish paths. [Primary exposition, indicated sections inspected](https://www.numdam.org/item/SPS_1976__10__86_0.pdf). Knight's original article was not available for a comparable full-text inspection here.

**Applicability finding.** This is a genuine nonlocal representation route: the full observed held-path law, including its stopping effects, can be encoded predictively without declaring the projected concentration Markov. Continuous paths are determined by their almost-everywhere time values. For a finite observed horizon one may extend the observed path constantly after H as a data encoding, not as an assertion about the physical process's unobserved future. However, the predictive state is a probability law on a path space. The cited theorem supplies neither finite-dimensional mass-action coordinates nor all finite chemical realizations of that law. Minimizing predictive information would still not enumerate nonminimal hidden extensions or identify hidden-only reactions. Markovization alone therefore does not close the requested fibre.

Lindquist, Mitter and Picci's nonlinear realization paper assumes, in Section 2, a centered, mean-square-continuous, purely nondeterministic stationary process on the whole real time axis, together with a Wiener innovation representation. Theorem 1 addresses minimal states within its chaos/splitting-space framework. Section 8 explicitly treats the development as structural rather than algorithmic and notes the nontrivial innovation-representation requirement. [Official primary PDF](https://mitter.lids.mit.edu/publications/32_toward_a_theory_LNCIS.pdf); [author-uploaded primary text used to inspect Sections 2 and 8 and Theorem 1](https://www.researchgate.net/publication/37592599_Toward_a_theory_of_nonlinear_stochastic_realization).

**Failed hypotheses.** A deterministic fixed start followed by a nondegenerate diffusion law is not stationary. Passing to equilibrium or a two-sided stationary version changes the experiment. No Wiener-innovation representation satisfying that theorem's assumptions has been established for the admitted general stopped projection. Thus this specific realization theorem cannot be imported unchanged. The official PDF was retrieved but its scan was not visually inspected; the section check used the identified author-upload text. A later Taylor–Pavon realization paper was accessible only at abstract level and supplies no theorem-level negative conclusion in this audit.

## 4. Finite observable-operator rank: a concrete failed hypothesis

Wu and Noe's OOM definition, equation (1), factors word probabilities through an m-dimensional linear state. Equation (6) is the past/future feature matrix C_12. Section 3.2, Assumption 2, explicitly assumes an m-dimensional OOM and an asymptotic stationarity condition; Assumptions 1 and 3 impose data-limit and rank conditions. Theorem 1 is conditional on all three. The continuous-observation Theorem 3 retains them, adding a closed Euclidean observation space and bounded features. [Primary 2016 conference paper, Sections 2.2–4.2 inspected](https://proceedings.neurips.cc/paper/2016/file/296472c9542ad4d4788d543508116cbc-Paper.pdf).

The relevant rank is linear predictive/Hankel rank, not number of chemical species. The following exact test uses the same adjacent-observation feature block as equation (6), with feature length L=1. It does not replace the continuous diffusion by a finite-state jump chain or coarse-grain the observation.

### Proposition: a one-reaction stopped diffusion has infinite observable two-time rank

Take the single reaction A -> 2A with rate 1. Fix x0>0 and I=(l,r) with 0<l<x0<r<infinity. Let

    dX_t = X_t dt + sqrt(X_t) dW_t,
    tau = first exit from I,
    Z_t = X_(t wedge tau).

The record is held at the reached endpoint. Fix any Delta>0 with 2 Delta<=H. For f,g in C_c^infinity(I), extended by zero to the endpoints, define the observed bilinear form

    B_Delta(f,g) = E_x0[f(Z_Delta) g(Z_(2 Delta))].

For every integer N>=1 there exist f_1,...,f_N and g_1,...,g_N of this class such that the N by N matrix [B_Delta(f_i,g_j)] is nonsingular. Consequently no exact finite-dimensional OOM representation of the sampled observed law can factor all these feature matrices.

**Proof.** All coefficients are smooth and uniformly elliptic on the closed interval. Write K_t for the Dirichlet killed semigroup on I, and k_t(x,y) for its interior density. The standard regular-interval killed-diffusion facts used in the previously reviewed two-time proof give continuity and strict positivity of k_t for t>0 and x,y in I. The generator is

    Lf = x f' + (x/2) f''.

For a direct specification of its self-adjoint realization, put

    m(x) = 2 exp(2x)/x,          p(x) = exp(2x).

Then Lf = m^(-1)(p f')'. The Dirichlet form

    E(f,g) = integral_I p(x) f'(x) g'(x) dx,
    domain(E) = H_0^1(I)

on L^2(I,m dx) is closed; m and p are bounded above and below by positive constants. Its nonpositive self-adjoint generator has domain H^2(I) intersect H_0^1(I) and the displayed expression. Its semigroup is K_t by uniqueness of the regular Dirichlet problem. In particular K_Delta is injective: if K_Delta g=0, the spectral theorem gives

    0 = ||K_Delta g||^2 = integral_(-infinity,0] exp(2 Delta lambda) dmu_g(lambda).

The integrand is strictly positive at every finite lambda, so mu_g=0 and g=0. Zero as a possible spectral accumulation point of K_Delta creates no kernel.

Let h(x)=k_Delta(x0,x)>0. The full stopped Markov property gives

    B_Delta(f,g) = integral_I h(x) f(x) (K_Delta g)(x) dx.       (A)

This is not survival-conditioned data. If absorption has occurred by the first time, f vanishes; if it occurs between the two times, g vanishes. Equation (A) is therefore an observable cylinder expectation of the actual held record, with exactly the required killing restriction and no extra exit indicator supplied as data.

Choose any N linearly independent g_j in C_c^infinity(I). Suppose a linear combination of the functionals f -> B_Delta(f,g_j) vanishes for every f in that test space. Equation (A) and distributional testing imply

    h K_Delta(sum_j c_j g_j) = 0  almost everywhere on I.

Since h>0, injectivity implies sum_j c_j g_j=0; independence gives every c_j=0. Thus the N functionals are linearly independent. The evaluation map f -> (B_Delta(f,g_1),...,B_Delta(f,g_N)) has range R^N: otherwise a nonzero linear functional annihilating its proper range would give the dependence just excluded. Choose f_i whose image vectors are the standard basis. The pairing matrix is then the identity. QED.

The density and regular Dirichlet operator providers are the same ones specified in [the reviewed two-time manuscript, Sections 3–5](TWO-TIME-SAMPLED-EXTENSION.md). The source history remains classical scalar diffusion theory, including [Kent's Theorem 8.1 and interval boundary framework](https://www2.stat.duke.edu/~sschmid/Courses/Stat376/Papers/Langevin/KentAdvAppProb1978.pdf). The proposition is an author hand diagnostic, not a new general spectral theorem.

### Exact connection to the cited observable feature matrix

Set the first two sampled observations to Z_Delta and Z_(2 Delta), and take phi_1=(f_i) and phi_2=(g_j). Their feature matrix C_12 is precisely the matrix in the proposition. If an m-dimensional OOM represented this law, integrating its word factorization against f_i and g_j would yield

    C_12(i,j) = [omega Xi(f_i)] [Xi(g_j) sigma],

and therefore rank(C_12)<=m for every feature choice. Taking N=m+1 contradicts the proposition. Boundary atoms cause no escape: the features vanish there; even granting an operator-valued-measure extension accommodating the mixed boundary/interior law, this finite-dimensional factorization has the same rank bound. Thus the failure is tied to the actual feature block, not to an unrelated operator on hidden states.

This one-species example is a legitimate subclass diagnostic: finite species and a finite reaction list do not imply the finite predictive rank required by this method. It is **not** a negative result about a finite-dimensional nonlinear state, finite parameterization, or a target-dependent finite identifying signature. This very process has a one-dimensional chemical realization, and the separate scalar adapter proves finite identifying signatures within its declared source class. Approximate low-rank models and coarsened observations are not excluded; they answer different questions from exact observational equivalence.

## 5. What the attack establishes, and the exact remaining bridge

Three tempting replacements for the missing theorem have now been checked rather than assumed:

1. A structural bisimulation/homomorphism gives a sufficient comparison, but the inspected theorem does not make it necessary for the fixed-start trace law of our admitted chemical class.
2. Predictive Markovization retains nonlocal path information, but does not identify every finite mass-action realization of the predictive law.
3. Exact finite-linear-rank realization cannot cover the whole admitted source class merely because each source is finite. The proposition disproves that particular hypothesis transfer without disproving nonlinear or finite-signature approaches.

The still-needed result is a stop-faithful, fixed-start, all-rival completeness theorem connecting observed path laws to the entire admitted physical reaction-network fibre, with its unavoidable full-generator equivalences. It must either justify a complete nonlocal signature or classify all compatible finite mass-action realizations without presupposing their hidden size. Hidden-only reactions cannot be removed merely because they have zero instantaneous projected covariance weight: they can affect later hidden coupling or the full-state exit clock.

No inspected provider supplies that bridge. This is a bounded conclusion about the named sources and their exact hypotheses, not a universal absence theorem and not a proof that the master problem is impossible. No further initial-jet component, stronger preparation experiment, changed stopping rule, or new runtime evidence is substituted for it.
