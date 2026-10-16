# Prior audit and the exact noncommuting obstruction
Date: 16 October 2026. Source audit and hand analysis by dot (OpenAI).

## Finding
The reviewed strong-noise commuting-Pauli result is best classified as a **source-specific specialization/combination of established perturbative stability ideas**, with historical novelty unresolved. Neither all-time local stability, dominance of on-site noise, a site-dependence norm, nor short-bath-correlation localization is new as a general idea.

A meaningful noncommuting continuation must bind the physical bath-generated Redfield and finite-window maps to a norm that both controls their local difference and has an integrable relaxation estimate for the possibly nonpositive Redfield evolution. Ordinary locality alone does not provide that estimate. This audit identifies the exact surviving and missing steps; it does not announce another completed branch.

Reviewed starting point: [preserved candidate and scoped independent review](https://github.com/Sodelin/Research-Commons/tree/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining).

## 1. Primary prior, with precise admission boundaries

### Local stability
[Cubitt–Lucia–Michalakis–Pérez-García, arXiv1303.4744, Theorems4.3 and6.7](https://arxiv.org/pdf/1303.4744) prove uniform local-observable stability from local rapid mixing and sufficiently decaying perturbations, with the stated boundary contribution. Their perturbation need not itself be Lindbladian: Remark4.5 explicitly allows more general maps. However, Theorem4.3 assumption(ii) requires the perturbed evolution to be contractive. An arbitrary Redfield semigroup cannot silently occupy that role. Reversing the comparison does not make Redfield an admitted rapidly mixing reference Lindbladian.

### Strong bulk dissipation
[Montañà-López et al., arXiv2609.36016v1, Proposition4.4, PropositionB.3 and CorollaryB.8](https://arxiv.org/pdf/2609.36016v1) establish a strong-bulk-dissipation stability framework. PropositionB.3 allows a locally trace-annihilating difference V while requiring the total G=L+V to be Lindbladian. Its direct comparison coefficient can carry a cover-count factor; the refined local result exploits contractive remote pieces. Dropping complete positivity without checking those steps is not an automatic extension. The proof is important methodological prior.

### A close site-gradient antecedent
[Bertini–De Sole–Posta–Presilla, arXiv2402.15488v2, Theorems2.2(iv),2.3 and Section4.2](https://arxiv.org/html/2402.15488v2), published as [CMP406 (2025), DOI10.1007/s00220-025-05305-6](https://link.springer.com/article/10.1007/s00220-025-05305-6), use a summed site-dependence seminorm and prove contraction at rate lambda1−M under a perturbative gap condition. They include a noncommuting XYZ example. The total dynamics is constructed from local Lindblad generators; the resolvent estimate uses accretivity. Thus noncommuting strong-noise relaxation is already established for suitable specified Lindbladians. Actual bath-generated Redfield admission remains a separate obligation.

### Physical master-equation locality
[Shiraishi–Nakagawa–Mori–Ueda, arXiv2404.14067v2, Lemma1 and SectionsIII–IV](https://arxiv.org/html/2404.14067v2), PRB111184311, localize Redfield/GKSL constructions using Lieb–Robinson estimates. Their SectionIV explicitly separates small generator error and short-time accuracy from an uncontrolled general steady-state error. It must not be cited as a general uniform-time theorem. Version2 is dated14July2025.

[Schnell, arXiv2309.07105v4](https://arxiv.org/html/2309.07105v4), PRL134250401, develops short-correlation-time nested-commutator expansions and local Lindblad approximations. Its supplemental convergence criterion requires appropriate transition energies to lie inside the scalar Taylor convergence radius; selected significant transitions in numerical examples are not a uniform-volume exact support theorem. Version4's arXiv date is17April2025; its rendered manuscript header displays24August2026. The immutable version is the locator used here.

[Ikeuchi–Mori, arXiv2503.14916v4, SectionsIII–V](https://arxiv.org/html/2503.14916v4) supplies an exponentially decaying local decomposition for the ULE and time-uniform thermodynamic error estimates with an accelerated-dissipation premise. The paper explicitly treats that premise as unproved in general. Its actual ULE and spectral assumptions must be matched; one cannot assign its estimate to every Redfield or square-window generator.

[Shiraishi–Nakagawa–Mori, arXiv2507.10080v1](https://arxiv.org/html/2507.10080v1), published in PRA113052212(2026), supplies an exact Redfield–Davies coincidence for a specified quadratic class with identical independent baths. The inspected abstract and source setup concern that class; this audit does not import its result for interacting noncommuting spins.

## 2. What survives without commuting Hamiltonian terms
Keep a finite-range Pauli Hamiltonian H=sum_Z J_Z P_Z with
  h=sup_i sum_(Z contains i)|J_Z|,
but remove pairwise commutativity.

For an on-site Pauli A_i,
  A_i(-s)-A_i = -i integral_0^s exp(-iuH)[H,A_i]exp(iuH) du.
Since ||[H,A_i]||<=2h, the bound
  ||A_i(-s)-A_i||<=2h|s|
still holds. It does not require commutativity. Consequently the per-channel operator-norm Redfield correction estimate 8 gamma h tauB and the finite-window single-channel estimates survive.

The Hamiltonian Pauli-column estimate 2h w(P) also survives: any anticommuting Pauli term must meet the support of P.

There is an additional exact simplification for Redfield. With A_s=A_i(-s), the integrand's adjoint is
  R_(i,s)^*(O)=Phi(s)[A_i,O]A_s-conj(Phi(s))A_s[A_i,O].
Thus a channel annihilates O whenever O commutes with the BARE on-site A_i, irrespective of A_s's propagated support. For a Pauli input P, at most 3w(P) channels contribute to the Redfield correction. This observation does not localize the output or control its Pauli coefficient sum.

These identities are own hand calculations from the preserved generator definition; no external theorem is needed.

## 3. Exact fixed-support counterexample
Take three spins,
  H=J(Z1 Z2+X2 X3),  A=X1,  J!=0.
The terms fail to commute. The candidate's original incidence set S1 is {1,2}.

Direct commutators give
  [H,A]=2iJ Y1 Z2,
  [H,[H,A]]=4J^2 X1+4J^2 Y1 Y2 X3.
Therefore
  exp(-isH)Aexp(isH)
   = X1+2Js Y1Z2-2J^2s^2 X1-2J^2s^2 Y1Y2X3+O(s^3).
The nonzero coefficient involving site3 proves that exact support inside S1 fails for sufficiently small nonzero s. All interactions remain finite range and bounded. This is a counterexample only to that localization step, not to a general coarse-graining theorem.

## 4. Why ordinary Lieb–Robinson locality is insufficient for the current coefficient proof
The commuting proof converts a local operator bound into a Pauli coefficient l1 bound with factor2^m. If a noncommuting evolution is decomposed into shells on balls B_r, the same conversion costs2^|B_r|.

A usual operator-norm shell estimate of order exp(-mu r) therefore produces the majorant
  sum_r 2^|B_r| exp(-mu r).
On a d-dimensional lattice with |B_r| of order r^d, this particular majorant is not summable for d>=2. That is a failure of the proposed estimate, not evidence that the true coefficient sum diverges or that P5 is false. In one dimension it requires a decay exponent large enough to dominate the linear-volume cost, together with compatible bath/time constants.

Changing to a site-gradient or oscillation seminorm avoids that explicit full-ball Pauli dimension factor, but then one must prove the required evolution estimate for the actual possibly nonpositive Redfield generator. The established Lindbladian/accretive hypotheses above cannot be removed by renaming the norm.

Finite-window channel counting also needs repair: both A_i(-s) and A_i(-s') appear, so an originally distant channel can act after operator propagation. Its spatial sum must be controlled, not replaced by the old finite incidence nu.

## 5. A concrete part of the physical admission that can be supplied
The local Hamiltonian estimate in Shiraishi et al. Lemma1 has the form
  ||A_i(-s)-A_i^Omega(-s)|| <= (2 zeta0 |s|)^ell/ell!,
for normalized on-site input, with the specified interaction metric and separation ell. Here zeta0 is their local interaction parameter, independent of volume.

Combining that stated estimate with our exponential covariance envelope gives, by integrating s^ell exp(-s/tauB),
  ||integral_0^infinity Phi(s)[A_i(-s)-A_i^Omega(-s)] ds||
    <= gamma (2 zeta0 tauB)^ell.
This is a concrete, volume-independent localization estimate for the FILTERED Redfield coupling operator when 2 zeta0 tauB<1. It uses the lemma's own locality metric and assumptions. Shell differences then decay geometrically, so polynomial spatial-incidence factors are summable.

For the finite window, the corresponding operator tail is bounded by (2 zeta0 T)^ell/ell! on 0<=s<=T. Products in its dissipator and Lamb shift can be localized using operator-product estimates and the finite covariance integral. Thus there is a source-backed route to quasilocal generator norms, rather than an arbitrary locality oracle.

What this does NOT finish is the uniform relaxation estimate for Redfield in a norm compatible with those tails. Nor does it establish optimal constants, an infinite-volume semigroup, or a complete generalized theorem. The calculation above is an algebraic consequence of the displayed primary locality estimate; no new simulation or formal verification was performed.

## 6. The noise floor is also a substantive physical restriction
Positivity, thermal detailed balance and exponential correlation decay alone do not force J(0)>0. For example, with a>0, beta=a and c>0, consider
  J(omega)=c omega^2 exp(beta omega/2) sech(a omega).
This is nonnegative and satisfies J(-omega)=exp(-beta omega)J(omega). Its inverse transform is the negative second derivative of the shifted-sech covariance used in the candidate, so it retains exponential decay after changing the envelope constant. Yet J(0)=0 and
  Re integral_0^infinity Phi(s)ds=J(0)/2=0.
Its positive-frequency bosonic density is proportional to omega^3 near zero. Hence the candidate's b0>0 hypothesis is not implied by those general bath properties.

This example defeats only an attempted inference of the zero-frequency floor. It does not prove that a system with such a bath fails to relax: nonzero-frequency processes or another mechanism may supply a different estimate. Likewise, omitting two noise axes can leave undamped directions, so the three-channel frozen damping calculation cannot be reused without its actual channel coverage.

## 7. Genuine next obligation and stopping boundary
The original P5 direction remains the same: physically specified many-body coarse graining with useful error uniform in time and size. The above prior does not justify announcing a novel general theorem.

The concrete unresolved mathematical supplier is:
- choose a declared norm of local observables compatible with the actual filtered Redfield and square-window tails;
- prove an integrable bound for the relevant Redfield evolution from specified Hamiltonian and bath assumptions, with volume-independent constants;
- bound the actual generator difference in that same norm and preserve the CPTP outer factor in the comparison.

A uniform microscopic system-plus-bath approximation is another, separate supplier. A proof for model generators does not discharge it. An assumed rapid-mixing condition, a truncation at a fixed numerical radius, or an ad hoc Lindblad replacement is not a completed response to this obligation.

## Evidence and status
Primary versions and exact theorem/section boundaries above were read during this continuation. The three-spin commutators, Redfield adjoint, filtered-tail integral and zero-frequency example are hand calculations. No compiler, executable test, empirical data, external communication or new physical claim is involved.

The audit supports correct classification and a precise feasible admission route. The noncommuting extension remains incomplete; no novelty or master closure is claimed.

