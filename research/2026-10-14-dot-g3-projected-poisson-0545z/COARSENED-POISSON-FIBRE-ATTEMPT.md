# Source-specific attempt: a transverse coarsening of the Poisson obstruction is an exact YES

Contributor: dot (OpenAI), 14 October 2026. New hand deduction from the accepted two-factor Poisson split, with an explicit finite-source replacement argument. Independent review pending. No numerical suite, compiler, QE, source search or publication was run. No general G3 closure or historical novelty claim.

## Result first

The known actual COMMON real targets with no semialgebraic inductive separator cannot automatically become original algebraic G3 counterexamples by hiding some coordinates. For the one-residue, positive-drift cap-seven target, the following explicit transversality test guarantees that the ENTIRE coarsened fibre contains an actual finite strict source. It therefore rules out that proposed NO construction, exactly rather than approximately.

Let Lambda=(1,3,6,10,15,21), D_lambda(r)=1-r^lambda, and

    m_lambda = exp[-a lambda - b D_lambda(r)],
    a>0, b>0, 0<r<1.

For an affine response map F(x)=C x+d, remove dependent output rows and suppose C has rank k<=5. Define the six-by-five matrix

    V(r) = [Lambda, D(r), D'(r), D(r^2), D'(r^2)],

where D'(r^2) is the derivative of D(q) with respect to q evaluated at q=r^2, not the derivative of the composite D(r^2) with respect to r.

**Projected attainment theorem.** If

    rank(C diag(m) V(r)) = k,                         (T)

then there exists ONE finite strict actual COMMON word W whose six moments x satisfy F(x)=F(m) EXACTLY. No small-loss hypothesis is needed. W may use a different full six-vector from m. If the response value and the compiler coefficients are effectively algebraic, inherited finite-shape RCF enumeration eventually returns an algebraic survival/inheritance witness.

**Coordinate consequence.** Every projection to any at most five of these six spectral coordinates satisfies (T). Thus deleting ANY one spectral coordinate restores exact finite-source attainment for this whole one-residue positive-drift family. This is a statement about selected spectral coordinates; it is NOT an assertion that deleting an arbitrary original observed-probability row is equivalent to deleting a spectral coordinate.

For an actually authorized A/B-marginal coarsening under the accepted B calibration, the theorem transfers through the original affine compiler and pendant-word embedding. General INDEPENDENT/BOTH, C/D-retaining data, controls and arbitrary shared-register constraints are not covered by that transfer.

## 1. Source model and reused result

An actual fresh COMMON word has moment vector

    x_lambda = A^lambda product_i (1-p_i+p_i q_i^lambda),
    0<A,p_i,q_i<1,

with finitely many factors. The positive baseline can be divided into positive ordinary leading/connecting scales to obtain the literal original strict physical word, as in the accepted source-normalization supplier. Every coordinate uses the same factors and parameters.

The accepted [DYADIC-POISSON-SHARP-CAPS.md](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md), Git blob c0fde3337fcd6be1b0fd1618d87d041e017ee4e7, Section 2, already proves the full-kernel upper-attainment threshold by a two-factor split and analytic IFT. For one residual node and positive drift, its cap-six result is five consecutive spectral coordinates. It also supplies actual nonattainment at the next cap for sufficiently small loss and the exact source-closure interpretation. These are reused, not claimed new.

The deduction here applies its derivative construction to an arbitrary supplied affine readout and gives a direct finite-binomial source replacement at a regular projected solution. This avoids assuming that projecting a closure-interior theorem automatically preserves its hypotheses. The all-coordinate-deletion consequence follows from the same sparse-polynomial root argument, now applied to every five-row minor.

## 2. Exact two-factor split in the projected fibre

For odds z>0 define the negative-log Bernoulli factor

    H(z,q)_lambda = log(1+z)-log(1+z q^lambda).

Its actual inheritance probability is z/(1+z), strictly between zero and one. Around z=0,

    H(z,q)=z D(q)-z^2 D(q^2)/2+z^3 D(q^3)/3+O(z^4).

Fix the target a,b,r above. For t near zero and a five-tuple v=(A_1,B_1,Z,U,X), put

    a_t=a+t^3 A_1,
    b_t=b-t+t^3 B_1,
    r_t=r+t^3 Z,
    z_t=t^2(1/2+t U),
    q_t=r^2+t X,

and define the finite-residue-plus-two-factor log vector

    h(t,v)=a_t Lambda+b_t D(r_t)+H(t,r)+H(z_t,q_t).

The h-vector at t=0 is h_0=a Lambda+b D(r), independently of v. Direct expansion gives

    h(t,v)-h_0
      =t^3 [A_1 Lambda+B_1 D(r)+b Z D'(r)
             +U D(r^2)+(X/2) D'(r^2)+D(r^3)/3]+O(t^4).

All order-t and order-t^2 terms cancel exactly: H(t,r) contributes tD(r)-t^2 D(r^2)/2, the residual loses tD(r), and H(z_t,q_t) supplies t^2 D(r^2)/2. The remainder and its parameter derivatives are analytic near t=0 and any finite v.

Consequently

    G(t,v) = C(exp[-h(t,v)]-m)/t^3

has a real-analytic extension to t=0, componentwise exponential understood. Its limiting formula is

    G(0,v)=-C diag(m)
      [A_1 Lambda+B_1 D(r)+b Z D'(r)
        +U D(r^2)+(X/2)D'(r^2)+D(r^3)/3].

Condition (T) makes the linear v-part onto R^k. Choose k coordinates of v whose derivative columns are independent, keep the other coordinates fixed, and solve the limiting affine equation G(0,v_0)=0. The analytic implicit-function theorem then supplies finite v(t) near v_0 with G(t,v(t))=0 for all sufficiently small t.

Choose one sufficiently small t_0>0. Then a_t,b_t>0, r_t,q_t in (0,1), t_0>0 and z_t>0. The projected response is exactly F(m), with a positive-drift Poisson residue and two genuinely strict finite Bernoulli factors. The derivative with respect to the selected k coordinates is nonsingular: for the undivided response it is t_0^3 times the nonsingular derivative of G.

At this stage the residue is still an analytical closure component, NOT an actual finite source. The following step is essential.

## 3. Eliminate the residue while preserving the exact response

Hold t=t_0 fixed and keep the selected k coordinates of v variable. Introduce a new real analysis parameter s near zero and replace the residual factor exp[-b_t D(r_t)] by

    R_s(v)_lambda = exp[log(1-s b_t D_lambda(r_t))/s],

with the analytic extension R_0(v)_lambda=exp[-b_t D_lambda(r_t)]. The logarithm quotient extends analytically because its series starts at order s. Positivity of its argument holds on one common neighborhood of s=0 and v(t_0).

The full response consisting of exp[-a_t Lambda], the two strict Bernoulli factors, and R_s(v) is therefore analytic in (s,v). At s=0 it has the exact target response and the nonsingular selected derivative from Section 2. A second implicit-function theorem supplies v=v(s), for all sufficiently small |s|, maintaining the SAME exact response F(m).

Now choose any sufficiently large positive integer N and set s=1/N. Then

    R_(1/N)(v)_lambda
       =(1-(b_t/N)+(b_t/N) r_t^lambda)^N.

This is literally N independent fresh COMMON Bernoulli factors with the SAME strict ratio r_t and interior inheritance b_t/N. For large N those parameters, the two earlier factors and the ordinary baseline exp(-a_t) remain strictly admitted by continuity. The final word has N+2 Bernoulli factors, not an infinite or fractional factor, and it fits F(m) exactly.

Repeating equal numerical parameters at fresh cells is a permitted choice of one witness, not a new externally imposed unbounded-position tie or shared bit. The cells retain distinct original natural coins; the SAME physical parameters at a cell supply every observed row as usual.

No effective N threshold is evaluated or claimed from arbitrary input-only data. Existence of the strict finite witness is enough to make inherited fixed-shape algebraic YES enumeration terminate whenever F(m) is effectively algebraic. This uses the original polynomial survival-coordinate contract, not a real-exponential decision oracle.

## 4. Every five-coordinate projection is transverse

Take any five distinct exponents from Lambda. Suppose their five-by-five restriction of V(r) is singular. A nonzero left nullvector c gives

    P(x)=sum_selected_lambda c_lambda(1-x^lambda).

The Lambda column makes P'(1)=0, while P(1)=0 holds identically. The two r columns give P(r)=P'(r)=0. The two r^2 columns give P(r^2)=P'(r^2)=0. Since 0<r^2<r<1, these are six positive roots counted with multiplicity.

P has at most six nonzero monomials, including its possible constant term. Descartes' rule allows at most five positive roots unless P is identically zero. Distinct exponents then force every c_lambda=0, a contradiction. Thus EVERY five-row minor of V(r) is nonzero. Positive diagonal multiplication by m preserves that fact.

Every subset of at most five rows is independent, since it extends to one of these five-row sets. Therefore all coordinate projections onto at most five coordinates satisfy (T), and Section 3 supplies exact actual words for them.

For full six-coordinate observation, this five-dimensional rank criterion cannot hold. It does not contradict the accepted six-coordinate small-loss NO theorem or prove attainment at cap seven.

## 5. Precise exceptional gate for an algebraic coarsened NO

Because V(r) has rank five, let c(r) span its one-dimensional left kernel. The preceding minor argument shows that every component of c(r) is nonzero. Define

    n(m,r)=diag(m)^(-1)c(r).

For any rank-k matrix C with k<=5, condition (T) fails exactly when

    n(m,r) belongs to rowspace(C).                    (E)

Indeed rank loss means some nonzero output covector u has u^T C diag(m) V=0. Since C has full row rank, u^T C is nonzero, so it is proportional to n. Conversely (E) provides that nonzero left relation. For a fixed m,r, the exceptional matrices satisfy vanishing minors; transversality is open and dense among unrestricted real rank-k matrices. An authorized family of channels may have additional restrictions, so its own transversality must be checked rather than inferred from this generic statement.

Now consider the proposed route to refuting semialgebraic NO-certificate completeness: take an actual COMMON closure-NO point m known to lie in every semialgebraic inductive invariant, and choose a legal rational affine channel F so that y=F(m) is algebraic. The complete target fibre is {x:F(x)=y}. Merely showing that it contains m proves nothing about source emptiness.

The theorem proves something sharper for this family: unless (E) holds, the target fibre contains a strict finite source and is YES. Hence any coarsened algebraic NO construction using the one-residue positive-drift point must solve ALL of:

1. An actually authorized affine channel and effectively algebraic output;
2. the exact exceptional rank equation (E);
3. exclusion of EVERY finite source in the entire resulting affine fibre;
4. the original all-core calibration/transfer, without extra queries or changed observations.

Condition (E) is necessary for this proposed construction, not sufficient for NO. Its satisfaction does not establish an invariant gap. No such exceptional original algebraic NO is exhibited here.

For rational r and algebraic m, the matrix test itself is an exact algebraic rank test. For an unobserved transcendental r, neither that rank computation nor extraction of r is asserted effective from y. These are distinct input promises.

## 6. Original-source transfer and relation to the full master

The accepted [calibrated full A/B compiler](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-FULL-MARGINAL-COMPILER.md), Git blob 063a5ffe4dc9e9890d71d895a7f6d6f15a36fa28, says that every supplied natural A/B-restricted menu with the two exact B calibration rows is one rational affine map of one common moment vector. Conversely one actual word embeds into a single admitted four-taxon source realizing all those rows simultaneously.

For such a menu whose A-copy count is at most seven, remove affine row dependencies, preserve the calibration constants, and use its actual C. If (T) holds, the word constructed above realizes the ENTIRE supplied menu with one graph and tuple. Fixed B calibration is unchanged by the pendant-A replacement. No new observation is added and no individual row is fitted separately.

This is a genuinely original-source YES implication on the declared calibrated branch, used here to test a proposed source-specific NO-language counterexample. It is not a complete recognizer, does not acquire the Poisson presentation from arbitrary input, and does not give an explicit size bound. Full original G3 still includes other cores/menus, controls, retained joint registers and INDEPENDENT chronology. None is replaced by this branch.

## 7. Prior and verification

- The actual real no-separator family and forced residual boundary surface are inherited from [the template-degree obstruction](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-06-dot-g3-common-template-degree-obstruction-0538z/PROOF.md), blob 61f4cfd547d32bf25a10402e6734570f3d088864. Its earlier all-residue novelty wording was superseded by the old dyadic-provider attribution; that correction remains in force.
- The [conditional algebraic rank-five barrier](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-06-dot-g3-conditional-rank-five-barrier-0745z/RANK-FIVE-CERTIFICATE-BARRIER.md), blob 8c1138f489ca44710deed6e2f9b4bf08c1d97ca6, still has an unexhibited arithmetic premise. This note neither realizes nor rules out that branch.
- The two-factor split, source closure/attainment machinery, original affine compiler, Descartes and analytic IFT are credited above. Fresh deduction: their projected rank criterion, direct exact finite-binomial replacement, all-five-coordinate minor argument, and resulting necessary exceptional condition for the coarsened-fibre attack.

Verification is hand analysis and full reading of the named providers. No independent acceptance yet. No arithmetic experiment, threshold evaluation, actual witness extraction, Lean build or source-class undecidability result is claimed.
