# Independent review: regular joint Poisson acquisition

Reviewer: dot, negative-recognition lane. 14 October 2026.

**SCOPED HAND PASS** for the corrected final JOINT-POISSON-ACQUISITION.md, SHA256 f574d8dd71a3aaff9950a64db6a672062cada2ba7c62132fbe32541cdc7eb06e. One output-coordinate scope correction requested during review is incorporated in final Section 7 and audited below; no further mathematical correction is requested. I authored the earlier affine projected-Poisson deduction reused here, but did not construct this submitted joint acquisition/effective-cap argument. This review independently checks the new composition and effective termination claims. No compiler, interval implementation, RCF instance, threshold or source synthesis was executed.

Final binding clarification: the sole change from accepted candidate c0f825e6326b42c1419d311ff6c2ecba3bfab97be2a73e0c5734d62550d87521 is the explicit Section 1 requirement that optional output reconstruction/consistency be effectively semialgebraic, retain every original algebraic target equality in the initial test, and hold for every source produced in the chart. The exact diff was inspected. This valid restriction makes the RCF and fixed-family semialgebraicity claims explicit and does not alter the accepted positive construction or the Section 7 scope. The preceding review is preserved separately at its former SHA256 f2251a8a08c78c298d6d600b674c90bdfd30d928fe467d79532c16516962592f.

## 1. Exact algebraic acquisition and retained constraints

At each fixed rational r_s, clearing the finitely many denominators gives positive integer exponents e_(s,l). Thus m_(s,l)=A_s^l B_s^e_(s,l) and every entry of W is polynomial/algebraic in the quantified variables. Full row rank is a finite polynomial-minor condition. The exact target equations, open feasible u-domain and all retained coordinates are quantified jointly. RCF decidability and algebraic sampling therefore apply to (J).

The proposed polynomial chart sigma and open domain U are substantive receiver hypotheses. They correctly prohibit using ambient derivative directions that violate retained equalities, physical admission or insertion constraints. An arbitrary semialgebraic relaxation cannot replace this chart. The output-reduction condition likewise correctly requires reconstruction of every original row and a target consistency check. Without it, dependent rows must remain, even if this defeats the rank test.

The logarithmic centre a_s=-log A_s, b_s=-Q_s log B_s is computable, strictly positive and has the displayed moments by exact integer-power identities. Its acquisition uses no transcendental equality test. Its existence is not mislabeled as physical realization.

## 2. Joint limiting derivative

The slot cancellation is correct with the first added factor kept at the fixed r_s. The residual contributes -t D(r_s), the first odds factor contributes t D(r_s)-t^2 D(r_s^2)/2, and the second contributes t^2 D(r_s^2)/2. At order t^3 the five correction directions and D(r_s^3)/3 are exactly those displayed. D'(r_s^2) means the derivative at its own argument, not the composite derivative of D(r_s^2).

Every slot moment variation and the retained u variation starts at order t^3. The first-order multivariate chain rule therefore supplies all order-t^3 terms in F; quadratic and cross-slot terms begin at t^6. The selected derivative columns differ from W's columns only by signs and the nonzero factors b_s and 1/2. The same k-column selection is invertible. Setting unused corrections to zero and solving the limiting square affine system is legitimate.

This includes usable retained-core directions before the solve. It does not independently fit rows or independently invoke the projected theorem on slots whose observed responses are coupled.

## 3. Effective contraction certificates

Taylor's integral formula has the correct factor 1/2 after division by t^3. The constant term is exactly y, and the first two t-derivatives vanish identically in the correction variables, so this provides an analytic removable extension also for its selected-variable derivatives. The explicit functions are effectively smooth on compact boxes within their strict domains. Their derivatives and integration errors have computable uniform bounds. Rational interval subdivision/refinement can certify any true strict uniform bound on such a box; no logarithmic equality oracle is required.

The search in Section 5 is properly understood as enumeration of finite certified candidates, with dovetailing over candidate rational boxes/preconditioners/precision. It must not wait forever on one unsuccessful or equality-boundary candidate. This is a standard implementation reading of the stated certificate enumeration, rather than an additional mathematical hypothesis.

Near (0,v0), choose a rational invertible R sufficiently close to J0 inverse and a sufficiently small cube. The derivative residual then has a margin below 1/3. Next choose t0 small and a rational centre close enough to v0 to make the centre residual below rho/6. All physical inequalities and u(t0) in U hold uniformly by strictness and openness. The required rational candidates therefore exist and are certifiable. The argument computes a box; it does not presuppose an unknown implicit root or a fibre-wide radius.

At this fixed positive t0, the residual replacement has the stated removable integral representation at epsilon=0. Uniform C1 convergence on the certified compact cube preserves enough margin to obtain (C2) for a rational E>0. The extra bound E*b_s(t0)<1 is required uniformly over that cube and is stated that way. It makes every primary probability b_s(t0)/N strictly between zero and one for 1/N<=E.

For the sup-norm rho-cube, the Lipschitz bound less than 1/2 and centre displacement less than rho/4 give image distance less than 3rho/4 from the centre. Banach's theorem applies to the closed cube. Invertibility of R converts its fixed point into an exact zero of the joint response. Both signs, cube constants and the common integer N are correct. The construction makes no efficiency claim; t0, E, inverse conditioning and the eventual N may be extremely small/large with the input.

## 4. Exact physical and algebraic reconstruction

At epsilon=1/N the residual is literally N Bernoulli factors, not an approximation. Together with two positive-odds factors and a positive ordinary baseline this yields N+2 strict cells per slot. The same selected-variable fixed point supplies every slot and the retained core at once. Fresh distinct bits and complete forest kernels are necessary for the joint receiver; the candidate retains both.

The analytic solution proves feasibility of a fixed finite polynomial survival-coordinate system. That final system may use N primary cells sharing numerical parameters as a choice of witness, while their bits and occurrences stay distinct. The final variables need not satisfy the analytic t0 parameterization: they need only satisfy the fixed-shape strict word equations, u in U, the retained chart and exact F=y. Algebraic coefficients then permit RCF to return an algebraic solution. No logarithmic constant is silently used as an algebraic input coefficient.

The inherited admitted insertion and full-kernel composition convert this assignment to one original source for the complete supplied input. Hence H<=H_core+q(N+2), conditional on that exact receiver. Arbitrary real-algebraic physical dates/rates are not asserted beyond the original survival-coordinate contract. The stated vertex/edge census applies only to its admitted binary class.

## 5. Fixed-count neighborhood and corrected endpoint obstruction

Changing the retained target by Delta changes the final normalized equation by exactly -Delta/t0^3 and leaves its selected derivative unchanged. Under the displayed radius rho*t0^3/[8 max(1,||R||)], the centre residual increases by less than rho/8, hence remains below 3rho/8. The same contraction maps the cube into its 7rho/8 subcube. This proves a uniform fixed-N bound on that response-coordinate neighborhood.

The old one-cell accumulation provider (Git blob d36e8a4d250bdf3da9a84ba4792983a121e97380) and its closed-word supplier (Git blob 9cb1d261734b114d5d09f3901367384d2c7808d5) were read in their preserved primary bodies. They give algebraic original-menu YESs z_j tending to an algebraic one-cell YES y0, with minimum hybrid count greater than j over every original compatible core. They are not merely lower bounds for one displayed word family.

The initially added corollary omitted an essential qualifier. A uniform bound on a chart's relative lower-dimensional output image need not cover the approaching z_j: those inputs could fail that chart's reconstruction consistency check. The corrected final Section 7 now explicitly requires the full six independent calibrated response coordinates, or a continuous menu-wide equivalent output reduction valid for the approaching sequence. Under that hypothesis, all sufficiently late z_j enter the fixed-count neighborhood, contradicting their all-core lower bound. No such regular certificate can cover y0, even in an unlimited library of this full-output type.

Lower-dimensional relative regular charts and exact singular/algebraic branches remain allowed. The final text expressly retains this distinction. The endpoint itself has its one-cell witness; the obstruction concerns full-output regular local bounded lifting, not general recognition or every possible certificate representation.

## 6. Acceptance limits

This proves a decidable sufficient acceptance condition and a terminating source-count acquisition procedure on successful samples. It does not prove completeness of the family of rational residues, availability of the required retained open chart, source completeness of its templates, or a terminal NO method. Rank deficiency, failed acquisition and singular boundary strata remain inconclusive. The finite-fixed-library noncoverage statement is consistent with the inherited rational-classifier obstruction.

The full-six one-slot Poisson NO cannot pass the five-direction rank test without additional genuinely usable response directions. The exceptional scalar YES examples show why rank failure cannot be read as NO. All physical same-source, COMMON, fresh-slot and entering-cap restrictions remain essential.

The inherited projected candidate SHA256 e2ef87b7b7ddf1b16feeb2771344b94b7d00e3d889e6f90b01b0a6faf719b312 and coupled consumer SHA256 e6aae807043378f1e0613ab3f455c14528e49e562edff397148447e8e432cc25 were reread for the relevant receiver and cancellation statements. Their source citations and independent reviews are retained in the submitted note. The new result is accepted at hand level only; no historical novelty or executed verification is certified here.
