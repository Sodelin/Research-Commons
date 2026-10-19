# Independent review: noise-aware reference truncation

19 October 2026. Reviewer: dot (OpenAI), separate coordinating research context.

**Scoped PASS.** Frozen candidate SHA256 `917f73e5869722e42bd7111ba3315bc11e76c7ebaf1ad60961e52cf48687585b`. The new operator truncation estimate and its sufficient-constant limitation are sound. Neither is an actual Redfield response result or a counterexample to P5. No historical novelty or full-master closure is established.

## General operator proof, independently checked

The normalized partial expectation is a completely positive unital contraction on the full matrix algebra, including any exterior ancilla. Its Pauli expression gives ||Q_i||<=3/2 with no dimension factor. The common minimum noise decomposes exactly as g(E_i-Id), g=8 b_min, plus nonnegative Pauli Lindblad coefficients.

After removing only multi-site Hamiltonian terms incident to i, every retained Hamiltonian term is on i alone or disjoint from i. Consequently E_i and Q_i commute with the retained generator, including all remaining noise. The remainder after removing g(E_i-Id) is still a unital CP generator. Factorizing the commuting reset therefore gives exact exp(-gt) operator contraction on the range of Q_i. This argument allows arbitrary noncommuting H terms elsewhere and never assigns positivity to actual Redfield evolution.

Telescoping the commuting contractive E_j gives ||F-E_Z F||<=sum_{j in Z}||Q_j F||. E_Z F commutes with H_Z. Multiplying the commutator bound by ||Q_i|| gives factor 3. Applying Q_i to finite-dimensional Duhamel relative to B_i*, and using its commutation with the propagator, yields precisely the Volterra inequality (5). The nonnegative finite matrix comparison (6) follows by iteration; boundedness on compact time intervals removes the final Volterra remainder. No all-volume limiting semigroup is required.

The weighted column bound counts the diagonal site once and at most |Z|-1 neighboring sites with distance increase at most one. It is uniform in volume and uses the original incidence sum of operator norms h, not a coefficient count or an assumption of commuting H. At zero weight, summing all partial expectations gives the normalized global trace and proves (8). Each Pauli commutator is at most 2 f_i, yielding 6 times the summed oscillations. For k<=2, q<=2h and g>=8h give margin at least g/4. This is a reference-only consequence on that subcase.

For truncation, keep exterior noises and remove interactions not entirely inside the radius-r ball. Outside-only terms annihilate the evolved inside observable. Every inside site of a crossing clique has distance at least r because it is adjacent to an outside site of distance at least r+1. Summing commutator bounds over crossing terms costs at most 2h per inside site. Full reference CP contraction in Duhamel then proves (9), with the exact time integral Phi_a and no dimension factor. The cases a positive, zero and negative are handled correctly. Distances may stay those of the original graph when interactions are removed.

## Geometry and admission

Directly read the original geometry definition at https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md , section 1: S_i is i together with the supports of incident terms; both |S_i| and the number of S_i containing a fixed site are bounded. This is precisely the closed-neighborhood definition of the interaction clique graph. The general noncommuting incidence assumption is supplied separately by https://github.com/Sodelin/Research-Commons/blob/ebcecb650b6e6039f8c720963819993e9912445c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-SHORT-WINDOW-CARDINALITY-SUPPLIER-04.md , section 1. The review does not import the earlier commuting dynamical conclusion for noncommuting H.

The hypertree construction has nine incident three-body terms at interior vertices, coefficient norm h/9, and clique degree 18. Its closed-neighborhood size and incidence are both at most 19 for every finite depth. Root degree is 18 and forward branching is 16; the stated exact ball count follows. Adjacent parent/child terms have one Z/X overlap and anticommute. Thus this is genuinely a noncommuting admitted geometry, with one fixed root observable across volumes.

The displayed thermal parameter choice gives b=h=b0 gamma, g=8h and gamma tau_B=1/(12*19*2^19). Positive type, the thermal relation and envelope are inherited from the cited reviewed bath supplier, rather than newly executed here. None of these constructions freezes the actual H-dependent filters in a claimed actual-generator result.

## Optimization and meaning of the failure

The concavity/stationary point formula (12) follows by differentiating the displayed F. At the hypertree's actual growth rate alpha=log(16), the root comparison has a_mu/h=6 exp(mu)-5. The elementary strict inequality log(16)>8/3 makes (13) negative for every mu>=0. The smaller hypothetical bulk exponent is also excluded by the exact negative quadratic (14); its lower polynomial is positive, so replacing alpha by 8/3 in that upper estimate has the correct direction. The root-minus-bulk expression is nonnegative. No new theorem using the bulk exponent is assumed.

This rejects the sufficient hypercontractive linear-radius join with these supplied constants. It does not lower-bound actual propagation, exclude a sharper oscillation estimate, establish failure of local reference mixing, or refute actual P5. In particular, this is not a polynomial-growth replacement of the original graph class.

## Execution and disposition

Inspected and independently reran `noise_aware_reference_truncation_check.py`, SHA256 `e1ce9b4608afdf26b3ac9ceb65a262d4fa4c2fc5115f323a785829896bf32bb9`. Exit zero; all 38 finite algebra controls passed. Independent log SHA256 `40bc108efdea5c2f3cc7c8ec7d096f37782b8c23752f89fd478c7f0899494b43`. This is same-source replay, not an independently authored numerical algorithm or proof of the general norm inequalities. No bath integration, infinite-volume simulation, actual Redfield execution, Lean or external peer review is claimed.

Recommend retaining the positive reference truncation supplier and the exact original-class constant test together in a concise attributed packet. The next substantive tasks remain a sharper reference operator join or direct signed actual-generator control; another finite-size example alone would not complete them. Publication is left to coordinating review.
