# Independent review: transverse coarsened Poisson fibre

Reviewer: dot, separate physical-count/protection lane, 14 October 2026. I did not construct the submitted Poisson proof. Prior involvement in the wider G3 project is disclosed. **SCOPED HAND PASS** for the stated conditional projected-attainment theorem and its coordinate-projection corollary. No counterexample or required mathematical correction found. This is not Lean verification, numerical witness extraction, a threshold algorithm, or general G3 recognition.

Reviewed: COARSENED-POISSON-FIBRE-ATTEMPT.md in the source-specific negative-recognition lane. Read the complete candidate and freshly fetched exact prior blobs c0fde3337fcd6be1b0fd1618d87d041e017ee4e7 (dyadic/Poisson sharp caps), 063a5ffe4dc9e9890d71d895a7f6d6f15a36fa28 (calibrated full A/B compiler), and8c1138f489ca44710deed6e2f9b4bf08c1d97ca6 (conditional algebraic rank-five barrier). No compiler, source search, QE, simulation or new external mutation.

## 1. First IFT: cancellation and actual rank

The odds expansion H(z,q)=zD(q)−z²D(q²)/2+z³D(q³)/3+… has the correct signs. With b_t=b−t+t³B and r_t=r+t³Z, the residual contributes −tD(r)+t³[B D(r)+bZ D'(r)]+O(t⁴). The first odds-t factor cancels the order-t residual and contributes −t²D(r²)/2+t³D(r³)/3. The second odds t²(1/2+tU), node r²+tX, contributes +t²D(r²)/2+t³[U D(r²)+(X/2)D'(r²)]+O(t⁴). Its quadratic odds term starts only at order t⁴. Thus all displayed coefficients are correct.

The vanishing through order two holds identically in the five correction variables, so analytic division by t³ is joint in those variables, not merely pointwise. At t=0 the derivative columns are −C diag(m) times Lambda,D(r),bD'(r),D(r²),D'(r²)/2. Since b>0, its rank is exactly the proposed condition(T).

Choose a nonsingular k-column minor and fix the other variables. Surjectivity permits a finite solution to the limiting affine equation, including its D(r³)/3 inhomogeneous term. The analytic IFT then applies at that solution. Taking sufficiently small positive t preserves positive drift/residue, both nodes in(0,1), and positive second odds even if U at the limiting solution is negative. The undivided response derivative is t³ times the corresponding derivative of G, hence remains nonsingular at the selected positive t0. The first step still has a Poisson residue and is correctly NOT called an actual finite source.

## 2. Second IFT: exact finite integer source

Fix that positive t0. The function

  exp(log(1−s b_t D_lambda(r_t))/s)

has a joint analytic continuation near s=0 and the selected correction point: log(1−su)/s=−u−su²/2−… . All six logarithm arguments stay positive on one sufficiently small common neighborhood. At s=0 the full response and its selected-variable derivative equal the first-stage response and nonsingular derivative. Therefore the second IFT is legitimate with the SAME output F(m).

At any sufficiently large integer N, s=1/N gives exactly

  (1−b_t/N+(b_t/N)r_t^lambda)^N.

The perturbed b_t remains positive and locally bounded, so0<b_t/N<1 for large N; r_t remains strict, as do the other two factors and exp(−a_t). This is a finite product of N+2 actual Bernoulli factors, not a fractional-power or infinite-factor source. Repetition of numerical parameters does not identify their natural coins. All six coordinates use the same finite word and same parameter assignment. There is no limit exchange that weakens equality to approximation.

When C,d and F(m) are effectively algebraic, the fixed-N equations in survival and inheritance variables are polynomial with effectively algebraic coefficients and strict inequalities. Real feasibility implies feasibility over the real algebraic numbers by real-closed-field transfer; exhaustive finite-shape RCF YES enumeration therefore eventually reaches a witness. This does NOT compute N from arbitrary input, acquire a hidden Poisson presentation, or establish a terminating NO branch. Calendar/rate realization may still use logarithms of those survival coordinates, as in the inherited source contract; it is not an assertion that all physical rates/dates become algebraic.

## 3. Descartes minors and exceptional condition

For any selected FIVE distinct positive integer exponents, a nonzero left-null vector produces P(x)=sum c_lambda(1−x^lambda), with double positive roots at1,r,r². These are three distinct points because0<r<1. The Lambda column gives P'(1)=0; the two derivative columns give P'(r)=P'(r²)=0 with the stated derivative convention. Six positive roots counted with multiplicity contradict Descartes because P has at most six monomials, hence at most five sign changes. If its constant term vanishes the bound is only stronger. Distinct exponent monomials ensure that P identically zero forces all c_lambda=0.

Thus every five-row minor is nonzero, and every smaller selected row set is independent by extension to five. Positive diagonal multiplication preserves this. The all-five-coordinate deletion corollary is valid; it is not an arbitrary-observed-row deletion theorem.

V has rank five in six dimensions. Its nonzero left normal c has no zero component: deleting a coordinate with c_i=0 would contradict the corresponding five-row minor. Full row rank of C then proves rank loss exactly when diag(m)^(-1)c belongs to rowspace(C). This is only a necessary exceptional gate for the proposed coarsened-NO strategy, not proof that any exceptional fibre is empty. The unrestricted open/dense observation is valid and is correctly not promoted to every legal family of channels.

## 4. Exact original-source transfer

The inherited compiler admits natural COMMON sources on original four taxa, with every actual row still sampling all taxa but readout restricted to A/B. Its two exact B calibration rows must remain. It produces one rational affine map of one common word moment vector and gives a reverse pendant-A embedding into one admitted source with B survival1/2.

Therefore the candidate correctly fits the entire supplied calibrated A/B menu whenever its actual compiled matrix has rank k≤5 and satisfies(T), retaining all rows jointly and all calibration constants. No independent row-wise witnesses, extra identifying observations or deterministic control summands are introduced.

This transfer excludes C/D-retaining readouts, timed/ranked observations, exposed controls, new cross-register ties, and INDEPENDENT/BOTH inheritance unless separately proved. Rich A/B menus may still have rank six at cap seven; removing one arbitrary probability row need not reduce their spectral rank. The candidate explicitly retains these boundaries. Its phrase that a fibre 'contains an actual source' is existential, not a claim that every point of that fibre is realizable.

## 5. Prior-work and value of the deduction

The October2 DYADIC-POISSON-SHARP-CAPS Section2 already supplies the two-factor t³ split, analytic IFT, positive-drift one-residue attainment through cap six without a small-loss restriction, and sparse-root rank mechanism. Its cap-seven small-loss rejection is preserved and not contradicted by any projection result. Ordinary finite-word realization and calibrated reverse embedding are also inherited.

The present candidate is a useful explicit projected-rank corollary plus direct binomial-removal argument. The latter bypasses a need to re-invoke an abstract closure-interior absorption theorem for a projected response. The nonconsecutive-five-coordinate conclusion follows from the same inherited sparse-root proof. These are scoped deductions from prior suppliers, not a new discovery of the cap-six/cap-seven phenomenon; historical novelty remains unassessed.

Conclusion: the suggested route 'hide enough coordinates of a Poisson closure-NO point to make an algebraic original input' fails whenever(T) holds, because the whole affine fibre then contains a finite strict source. The note exhibits no exceptional legal algebraic NO fibre and leaves the conditional rank-five arithmetic branch unresolved. This is progress in excluding a proposed counterexample construction, not a solution of certificate completeness or the original G3 master.
