# P1 route assessment: unknown conditional qubits and an angular-prior test

17 October 2026. Author: dot (OpenAI), working with Nolan.

**Local route infrastructure and a failed small-chi-square attempt; not a new P1 lower bound.** Component 29C is published at `4e9bbabbf28b96beee04bef9f0352979f40611c6`. Its fixed-alphabet ceiling and all earlier bounds are unchanged. This note does not extend that ceiling to unknown means or to quantum states. The full optimal-copy question remains open. No historical novelty, external peer review, Lean proof, or experimental implementation is claimed.

## 1. Primary product-testing comparison

Canonne, Diakonikolas, Kane and Stewart, *Testing Bayesian Networks*, COLT 2017, Section 5.1 and Theorem 40 in Section 5.2, establish the matching order `max(sqrt(s)/epsilon^2, s^(3/4)/epsilon)` for equality testing of two unknown binary product distributions. The primary upper-algorithm passages on PDF pages 19–21 and lower theorem on page 26 were inspected. Its complete sample is an entire product vector. The lower proof's heavy/light construction is already credited in our components 26–29; unknown Bernoulli means alone are not a new source theorem.

https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf

Bhattacharyya et al., *Testing Product Distributions: A Closer Look*, ALT 2021, Table 2 and Theorems 2.5–2.8, distinguish the exact-equality results from the stronger near-linear **tolerant-null** lower bounds. Those tolerant bounds cannot be substituted for P1's exact null. The inspected source does not supply the needed stronger likelihood theorem for randomly sampled conditional labels.

https://proceedings.mlr.press/v132/bhattacharyya21a/bhattacharyya21a.pdf

In particular, multiplying a single-product sample lower bound by the number of labels is not a valid reduction: the global tester can pool information across labels, and each label has one shared pair of complete-row counts.

## 2. A concrete quantum admission extension, with the same resource order

This section records a mathematical extension of the already reviewed reservoir construction. It is infrastructure for a possible future statistical argument, not an exponent improvement. It has not received a separate review in this pass.

Fix `k>=5`, `r=k-1`, `D=binom(s,r)`, and the original fixed `beta>0`. At label S and data site j, choose any faithful qubit state `rho_(S,j)` with minimum eigenvalue at least `1/(2s)`. Allow different axes and spectra at different sites and labels. Put

    v_(S,j) = -log rho_(S,j),
    0 <= v_(S,j) <= log(2s) I.

Let positive label weights have maximum 1 and minimum at least `s^(-C)` for a fixed, declared class constant `C>=0`. Their sum is at least one. Write `U_actual=max(-log w_S)`, but use the common class-wide envelope `U_*=C log s`, so `U_actual<=U_*`, in every guard. Fix the requested leakage `eta` from the declared class parameters, independently of the unknown source. With the same clone fractions x_i as component 29, define the operator-valued energy

    E = lambda(sum_i x_i-r)^2 I
      + sum_(|S|=r) (product_(i in S) x_i)
           [-log(w_S) I + sum_j v_(S,j)].

For each fixed clone configuration all summands are positive operators on the data qubits, even when different labels use noncommuting axes. On constant clone blocks of weight r only one label term survives. The data factors act on different sites, so its exact unnormalized block is

    w_S tensor_j rho_(S,j).

Its trace is exactly w_S. Thus the ideal normalized state is the visible label with probability `w_S/sum_T w_T`, followed by its product of qubit states. No label partition term has been dropped.

For `v=a I+b dot Pauli`, positivity and the displayed spectral bound imply `a+||b||_1 <= (1+sqrt(3)/2)log(2s) < 2log(2s)`. Use the conservative common envelope `V_*=2log(2s)` everywhere in component 29's coefficient bounds. Set `lambda=16[s+log(2s/eta)]`, `S0_*=lambda(s+r)^2+D(sV_*+U_*)`, and `Vbar_*=V_*+U_*`. Choose one common clone size m using component 29 equation (15) with `Vbar_*`, and one common reservoir size R using equation (18) with `S0_*` and its corresponding lock contribution. These choices depend only on `(k,beta,s,C,eta)`, before either unknown source is selected; they do not depend on actual weights, axes, spectra, or source identity. The same clone and reservoir registers, retained-sector projection, and ideal embedding therefore apply to both sources and every member of the declared class. Each nonidentity data factor still has Pauli weight one, so signal locality remains `r+1=k`. Different X/Y/Z terms do not merge into the same Pauli word. The previous multiplicity and collision bounds apply componentwise with this enlarged envelope; every physical Pauli coefficient remains bounded by one after dividing the constructed dimensionless energy by beta.

The all-plus reservoir block remains classical on clone spins and quantum on data. Its bad-clone partition is bounded by `2^s` times the scalar energy bound because the signal is positive. This is the same full data-entropy factor already paid in component 29.

For other reservoir configurations, use the operator-norm perturbation bound on the data block. If Hermitian A and B satisfy `A>=B+cI`, the ordered eigenvalues obey the same inequality, hence

    Tr exp(-A) <= exp(-c) Tr exp(-B).

This trace comparison is sufficient. No false claim that the exponential is operator monotone is needed. The existing reservoir perturbation bound `2 k l (S0_*+B0)/R`, with B0 the common lock coefficient sum from component 29, and the same finite suppression guards therefore control the block partition functions uniformly over the class.

### The even-k reversal is spectral, not a universal physical spin-flip channel

Let L be the number of nonreservoir qubits, including **all clones and all data qubits**. In the computational basis define the antiunitary

    Theta = (iY)^(tensor L) K,

where K is global complex conjugation. For every Hermitian Pauli word P of weight w,

    Theta P Theta^(-1) = (-1)^w P.

This follows one factor at a time; global conjugation and the tensor product act on all data factors as well as the clones. It is valid for Y components. For even k, the all-minus reservoir multiplier `(-1)^(k-w)` is exactly `(-1)^w`. The clone lock has even nonreservoir weight and is invariant. Consequently the two nonreservoir block Hamiltonians are antiunitarily equivalent, apart from the known reservoir-field scalar `2h0R`.

Antiunitary conjugation preserves every real eigenvalue, with multiplicity: apply Theta to each eigenvector. Therefore the full data-tensor partition functions satisfy the same identity `Z_minus=exp(-2h0R) Z_plus`. This is a spectral argument, not a unitary or CPTP operation available to the tester. For odd k the existing direct norm/energy estimate is sufficient and requires no such reversal.

All finite guards remain satisfiable with the same class-wide choices `m=O((log s)^(1/(k-1)))`, `R=O(sm)` and total `N=sm+s+R=O(s(log s)^(1/(k-1)))`, when the requested leakage eta is inverse polynomial in s with fixed declared constants. The implied constants may depend on k, beta, C and the declared leakage exponent, but not on the unknown source. The known projection onto the all-plus reservoir, constant clone blocks and weight-r label sector retains the quantum data without measuring their unknown axes. Its conditional output is exactly the declared classical-quantum row. The ideal embedding merely appends the known clone/label and reservoir registers; it is source independent. Orthogonal-sector leakage at most eta gives full trace distance at most `2eta` from that embedding.

The supplier whose finite bounds are reused is component 29, Sections 6–8:
https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/P1-RANDOM-LABEL-MASS-CANDIDATE-29.md

This admits many conditional quantum parameters at the same asymptotic resource order. It supplies no hard prior, no stronger all-copy bound, and no uncounted preparation or Hamiltonian oracle.

## 3. A genuinely angular prior is more visible in the old chi-square method

The following checks an explicit alternative to the earlier shared-axis radial prior. It is not merely a change of label masses.

Set `r0=1-2/s`. At each coordinate independently, choose a heavy type with probability one half, giving `I/2` in both sources. For a light type draw a Haar-uniform proper rotation R. On the null both Bloch vectors are `r0 R z`. On the alternative they are

    r0 R z,
    r0 R(c z + sqrt(1-c^2) x).

Each source has the same one-source prior marginal as under the null, including all repeated copies from that source. When `|c|<1` and `r0>0`, the two light qubit states do not commute. All eigenvalues are the same as in the radial model, so Section 2's admission applies. The directions and types are drawn once, before all copies.

Write `C=X tensor X+Y tensor Y+Z tensor Z`. The null prior average for one P copy and one Q copy is

    M0=I_4/4+r0^2 C/24.

The alternative is `M1=I_4/4+c r0^2 C/24`. These averages commute, and M0 is faithful. Direct diagonalization using the eigenvalues 1,1,1,-3 of C gives exactly

    chi2(M1||M0)
      = r0^4 (1-c)^2 / [(6+r0^2)(2-r0^2)].          (A)

Here chi-square means `Tr[(M1-M0) M0^(-1) (M1-M0)]`. For the s independent coordinate priors, the one-cross-row value is `(1+chi2)^s-1`.

This angular alternative really can be far. Its squared one-qubit fidelity is `1-r0^2(1-c)/2`. Suppose at least s/3 coordinates are light, an event of probability at least `1-exp(-s/18)`. Put `c=1-b/s`, `b=24epsilon`, and take `s>=8` with the displayed angle admissible. Since `r0^2>=1/2`, product fidelity and the elementary trace/fidelity inequality give full trace distance at least

    2(1-exp(-b/24)) = 2(1-exp(-epsilon)) >= epsilon

for `0<epsilon<=1`. This is a conditional-row farness statement; global label weighting still has to be included in a complete lower prior.

For fixed positive b, equation (A) yields one-cross-row chi-square of order `b^2/s`. The previously recorded radial construction yields order `alpha^4/s^3`. These are exact two-row comparisons, not a claim that the full testing complexities have those orders.

### Retaining the mass-mixture denominator makes the failure quantitative

Try the same masking experiment as component 29: signal raw mass mu with probability `1-mu`, nonsignal raw mass 1 with probability mu, where `0<mu<=1/4`. Both sources share that mass. At the observed count pair `(n_P,n_Q)=(1,1)`, put `C_lambda=exp(-2lambda)lambda^2`. The contribution of this count sector to the label chi-square is exactly

    [(1-mu)^2 C_mu^2 /(mu C_1+(1-mu)C_mu)]
       times [(1+chi2(M1||M0))^s-1].

The prefactor is at least `mu^3/4`: bound the numerator below by `(9/16)exp(-1)mu^4` and the denominator above by `mu/2`. Also `(A)>=b^2/(48s^2)` for `s>=8`. Thus this single observed sector contributes at least

    mu^3 b^2/(192s).

Independence across labels gives full unconditioned chi-square at least `D mu^3 b^2/(192s)`. At component 29's chosen scale `mu=s/(1600 alpha^(4/3) D^(1/3))`, this is

    b^2 s^2 /(192 * 1600^3 * alpha^4),

which diverges for fixed positive b and alpha. Therefore the old small-chi-square argument **cannot** prove indistinguishability for this angular prior at that budget. This is a failure of that proposed proof mechanism. Large chi-square alone does not prove large total variation, a general tester ceiling, or impossibility of some different prior analysis. No independent per-coordinate clocks have been substituted: the sector uses the actual shared counts `(1,1)`.

## 4. Exact checks and the remaining gate

The adjacent `check_angular_qubit_route.py` was executed using installed SymPy. It verifies the two-copy twirl with 24 proper signed-permutation rotations, equation (A), the qubit fidelity identity, one- and two-qubit Pauli-weight reversal, and the rational constants above. The finite twirl has exactly the same second moments as Haar rotation; it is a check of the displayed two-copy identities, not a replacement for the stated all-copy Haar prior. The full tensor reversal and partition comparison are hand arguments. No physical simulation or all-count indistinguishability certificate was run.

No useful stronger P1 hard family is established in this pass. A shared unknown axis applied to the radial prior only transports the already known lower bound by a hypothesis-independent channel. The genuinely angular prior above is not hidden at the accepted scale by the same chi-square method. General unknown-mean product theorems neither supply the missing conditional-label observation bound nor justify a tolerant-null substitution.

The next decisive obligation is an actual different conditional prior, with exact equality under each null draw and sufficiently probable full-distance alternatives, whose complete shared-count quantum observation law is quantitatively close beyond the accepted lower scale after the above spin accounting. Alternatively, a full-class upper must handle arbitrary noncommuting states with every measurement-selection copy counted. Neither obligation is discharged here. Admission infrastructure is saved for reuse; no new public checkpoint or ceiling extension is proposed from this attempt alone.

## Revision record

At 23:58 UTC on 17 October 2026, Section 2 made the common source-independent guard choice explicit: all size and suppression bounds use the class envelope `U_*=C log s` rather than the source-specific maximum. The original 23:42 text is preserved in the adjacent `-ORIGINAL.md` file with SHA256 `7b025d70392dd0cea854256b4bb7d8ed5d344db5ffe8088466900d314f444f55`. This clarification does not change the failed statistical route or establish a new P1 lower bound.
