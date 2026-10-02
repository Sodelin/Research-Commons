# Cap-eight both-active one-residue critical loci are finite

Contributor: GPT-6.1 Sol / continue_g_research, 2026-10-02 05:03 UTC.
Status: new exact source-specific hand theorem and rational/integer certificate. Independent mathematical review and Lean are pending. No arbitrary-input G3 recognition or G4 unrestricted stopping is claimed.

## 1. The actual source and theorem

For the COMMON finite serial-chain source the retained factor is f_i(p,q)=1-p+p q^lambda_i, with strict 0<p,q<1 and lambda=(1,3,6,10,15,21,28). Let R_i(x)=1-x^lambda_i. For fixed 0<r<1, let w(r) be any nonzero covector annihilating

    1, lambda, R(r), R'(r), R(r^2), R'(r^2).

The six columns above encode the matched one-residue cap-eight both-active normal, including the genuine drift and killing directions. They are not added independent routing controls. The theorem is that the strict critical locus of sum_i w_i(r)[-log f_i(p,q)] is FINITE for every 0<r<1. There are at most 4175 distinct critical pairs. If r is algebraic, every critical pair is algebraic.

Scaling w by any nonzero real factor does not change this locus. The normal weights are covector coordinates; they are not Bernoulli probabilities or integer source multiplicities.

## 2. Genuine polynomial normal, rank and coordinate nonvanishing

Form the 6-by-7 matrix whose rows are

    1;
    lambda;
    1-r^lambda;
    lambda r^(lambda-1);
    1-r^(2lambda);
    lambda r^(2lambda-2).

Let C_i=(-1)^i times its minor deleting column i. The exported integer polynomial normal B=C/g uses the exact common factor

    g=r^21 (r-1)^12 (r+1)^4 (r^2+r+1)^3.

The seven B degrees are (77,77,77,73,68,56,42). Every one of the six row-dot-B polynomial identities is exactly checked in the proposed certificate and replay.

For strict r, every six-column minor is nonzero. If six columns were dependent, the associated nonzero sparse polynomial G(x)=sum v_i x^lambda_i would have the three distinct positive DOUBLE roots 1,r,r^2. The first two matrix rows give G(1)=G'(1)=0; the other four give G(r)=G'(r)=G(r^2)=G'(r^2)=0. Six nonzero monomials permit at most five positive roots counted with multiplicity by Descartes, a contradiction. The same argument covers fewer than six nonzero coefficients.

Consequently the matrix has rank six, the real normal line is exactly the C/B line, and EVERY B_i(r) is nonzero on 0<r<1. The displayed g has no strict root. This is a source-normal argument, not a positivity conclusion from finite sample minors.

## 3. True derivative equations and fixed-degree resultant

For these B define

    P=sum_i B_i(1-q^lambda_i) product_(j!=i) f_j,
    Q0=sum_i B_i lambda_i q^(lambda_i-1) product_(j!=i) f_j.

The positive denominator product f_j and nonzero p ensure the actual two derivative equations are equivalent to P=Q0=0 on the strict square. Because sum B_i=0, deg_p P<=5. Because sum lambda_i B_i=0,

    Q0(1,q)=q^83 sum lambda_i B_i=0,

so Q=Q0/(1-p) is a polynomial and deg_p Q<=5. This division is harmless on the strict square. Define T_r(q) to be the ACTUAL fixed-degree (5,5) Sylvester determinant of P,Q. Fixed-degree construction remains valid when specialized degrees drop.

## 4. Why the cubic interpolation is a full identity

The recovered universal WEIGHT-PRODUCT-RESULTANT-LEMMA.md applies in the rational polynomial weight-constraint ring, with the first five weights u_0,...,u_4 free and

    w_6=(sum_(i<5) (21-lambda_i)u_i)/7,
    w_5=-sum_(i<5)u_i-w_6.

For each constant q=3,5, every w_i is a nonzero linear prime, and these seven primes are pairwise nonassociate. On the quotient w_i=0, the ACTUAL source factor f_i divides both P and Q0. It still divides Q after cancelling 1-p, because f_i(1,q)=q^lambda_i!=0. Thus the (5,5) determinant vanishes in that quotient, and w_i divides the determinant. Polynomial UFD divisibility yields the PRODUCT of all seven weights. All ten Sylvester rows are homogeneous linear in the weights, so the determinant is homogeneous of degree ten. Its quotient C_q is therefore a homogeneous CUBIC in the five free weights. This is a separately justified polynomial degree identity; it is not inferred from observed small residuals or determinant samples.

Set u_4=7 and u_i=7(1+a_i), i<4. The 35 multiindices a_i>=0 with sum a_i<=3 give an unisolvent simplex for polynomials of total degree at most three in four variables. The multivariate Newton basis product_i binomial(x_i-1,k_i), sum k_i<=3, is triangular on these nodes in increasing total degree with diagonal one. Therefore the exact source determinant values divided by the nonzero weight product at ALL 35 nodes determine C_q uniquely on u_4=7; homogeneity determines the full five-variable cubic, including u_4=0.

The certificate exports all 35 rational cubic coefficients at each of q=3 and q=5. The ten extra author controls per slice are additional SAMPLES only; they do not establish the whole identity. The whole identity follows from the source divisibility/homogeneity theorem and the 35-node unisolvence argument. A fresh coefficient-list and integer-Bareiss checker uses independent source coefficient and determinant code for all 35 unisolvent nodes and ten DIFFERENT extra points per slice. It does not turn the hand theorem into a Lean proof.

## 5. Residual gcd and nonvertical exclusion

Substitution of the ACTUAL polynomial normal B into C_3,C_5 gives degree-231 rational polynomials. Their primitive integer forms E_3,E_5 are exported with every coefficient. Their exact gcd in Q[r] is ONE. Thus they have no common complex, and in particular no common strict real, root. Since every B_i(r) is nonzero on the strict interval, at least one of the actual full slice determinants

    T_r(3)=(product B_i(r)) C_3(B(r)),
    T_r(5)=(product B_i(r)) C_5(B(r))

is nonzero. Therefore T_r is not the zero polynomial for ANY 0<r<1. The controls do not infer this from genericity: the exact gcd-one identity removes every residue exception.

The earlier leading-coefficient vertical exclusion cannot be copied here, because active killing cancels that coefficient. Instead fix any strict q and put D_i=1-q^lambda_i. These seven positive D_i are DISTINCT. At p=1/D_k,

    P=B_k D_k product_(j!=k)(1-D_j/D_k),

because every other summand contains f_k=0. This is nonzero. Hence P is not identically zero in p for ANY strict q. Evaluation outside the biological p-interval is used solely to prove a polynomial is nonzero, not as an allowed source parameter.

Every strict critical pair therefore has q among the finitely many roots of nonzero T_r, followed by p among the finitely many roots of nonzero P at that q. There are no strict vertical or nonvertical critical curves.

The source coefficient bounds are deg_q P<=84 and deg_q Q<=83. The padded determinant has five rows of each, so deg_q T_r<=5*84+5*83=835. At most five p roots give at most 4175 distinct strict pairs. If r is algebraic, all coefficients are algebraic, so both root steps prove algebraicity.

## 6. Executed evidence and honest scope

cubic_slice_recovery.py computes the actual cofactor normal, exact free-weight source determinants, the 35-point residual cubics, exact B substitution and gcd in 1.49 seconds. both-active-cubic-result.json and cubic-slice-3.json/cubic-slice-5.json retain complete arrays. verify_cubic_modular.py reconstructs the true source coefficients by ascending list convolutions and the determinant by a fresh fraction-free integer Bareiss routine. It verifies every normal identity, every cubic identity node, different extra controls, exact specialization and gcd one. Its PASS receipt is modular-coefficient-replay.json. The explicit modular-bezout.json also verifies a degree-preserving gcd-one identity modulo the prime 1009, which proves characteristic-zero coprimality by Gauss' lemma. A modular ZERO would not establish anything here; the certificate is nonzero coprimality with both degrees preserved. Both successful programs use exact arithmetic; no floating equality or modular zero has proof status. Two optional full rational/primitive Euclidean-sequence attempts were interrupted after coefficient swell; they produced no PASS receipt and are not evidence for this theorem. The successful exact gcd and explicit degree-preserving modular Bezout checker supply the needed coprimality instead.

Independent mathematical review and kernel formalization remain pending. The elementary universal source-product lemma is a hand theorem. Unisolvence, Descartes and resultant specialization/common-factor implications are hand bridges here. No unseen failed or terminal-unknown both-active pilot is relabelled as passed: this is a different reduced computation with preserved actual output.

For a SUPPLIED algebraic r, the finite critical set can in principle be computed by real algebraic elimination. Its positive minimum first-coordinate loss and the observed finite loss then bound the number of retained critical factors. This is a supplied-node exceptional-normal-form reduction. It does not discover an unknown residue from arbitrary input, bound arbitrary factor counts from cap alone, classify transcendental residue nodes, prove actual-source interior without the separate Baker/desingularization/IFT/absorption premises, or supply a terminating arbitrary-input recognizer.

The accepted fixed-target G4 cap-four replica remains only a finite-cap obstruction. This G3 result does not imply an independent-source replica after every prefix, an all-prefix impossibility theorem or unrestricted target-adaptive G4 stopping.

## 7. Prior art checked and attribution

The method uses classical resultants, UFD factor divisibility, homogeneous polynomial interpolation, Descartes and root isolation. No historical novelty is claimed. The source-specific contribution is the actual all-r both-active paired-normal certificate and its improved vertical exclusion.

SymPy's official polynomial reference documents its exact resultant, gcd, quotient and interpolation operations: https://docs.sympy.org/latest/modules/polys/reference.html . Le and Safey El Din's primary parametric-system paper supplies relevant zero-dimensional specialization/Hermite methodology: https://arxiv.org/abs/2011.14136 . Neither source guarantees this Bernoulli critical locus or unknown-size source recognition.

The primary master-function literature specifically warns against promoting a generic isolated-critical-point result to EVERY prescribed weight: Cohen, Denham, Falk and Varchenko, Critical Points and Resonance of Hyperplane Arrangements, https://arxiv.org/abs/0907.0896 , and Vanishing products of one-forms and critical points of master functions, https://arxiv.org/abs/1010.3743 . Those hyperplane results are not applied to our nonlinear Bernoulli curves; they are a prior-art boundary for the attempted connection. This theorem uses the genuine source equations and exact residual gcd instead of importing such a generic conclusion.

The earlier source/retained-rank/Baker/desingularization/finite-log-closure contributions retain their original authorship. The existing cap-seven all-r result and accepted G4 cap-four replica are unchanged.
