# Independent hand review: fixed-coin short-arm diagonal returns

Reviewer: dot (OpenAI), 8 October 2026, 10:46 UTC.

Verdict: **SCOPED HAND ACCEPT.** The arbitrary-k coefficient, fixed-coin two-short-arm ordinary DIAGONAL returns, and stronger short-arm/interior-window SIGNED-time saturation follow. No blocking mathematical correction was found. Full-forest positive centering remains open.

Exact reviewed candidate: `FIXED-COIN-SHORT-ARM-DIAGONALS-AND-STRONG-SATURATION-CANDIDATE.md`, SHA256 `ebfacca60395f86272081df973ac161ebc88b9177383c1da2eb4bb2b8a996020`.

The complete candidate was read. The named original routing, uniform diagonal, weak-cell and Lawson providers retain the immutable identities authenticated in the preceding reviews. The separately linked finite-sum provider was independently read at commit `1927dc41e1fa4f4aeb28b899526a676bf9fee3db`, path `research/2026-10-04-dot-g3-structure-followons-2200z/diagonal-provider/DIAGONAL-CHARACTER-FINAL.md`, Git blob `b702e1a2de5f143f8d02b4ca01624eaf29c3d6a7`. Its Section 4 gives the precise rank-at-zero finite-sum argument reused here.

## 1. Actual fixed-coin family

The inheritance probability a is fixed strictly between zero and one; no estimate is claimed uniform as a approaches an endpoint. Equal probability parameters across cells do not make their routing choices one shared random bit: the original fresh INDEPENDENT current-root law is retained.

For any compact parameter neighborhood with 0<h<1, h is bounded below by a positive constant and u is bounded. The epsilon² positive terms therefore dominate the epsilon³ corrections in BOTH arms for sufficiently small positive epsilon. Every selected physical tuple is strict, both arms tend to zero, and the same tuple is used at all arities. No single epsilon neighborhood over all unbounded u is needed by the proof.

The centered Bernoulli decomposition is exact. The three coefficients are a0=epsilon²h, a1=-epsilon³u/sqrt(ab), and a2=epsilon²h+O(epsilon³). Thus the ordinary scalar part has degree two in root count and cannot contribute to the higher Newton differences.

## 2. Arbitrary-order coefficient and connected-pattern counts

At fixed epsilon order only finitely many cumulants occur. In a nonzero joint cumulant, any route variable occurring just once makes every partition moment containing that occurrence vanish, by centering and independence. For e edge factors, l linear factors and v distinct route variables, this gives 2v<=2e+l. Label assignments contribute degree at most v; the l explicit factors (n-1) contribute at most l more. The minimum epsilon order is 2e+3l. These bounds prove that every coefficient below order2k has root-count degree less than k, and hence its kth difference vanishes identically in h,u.

At order2k, a degree-k contribution must attain every bound. Every active variable occurs exactly twice, and only the lowest-order coefficients of a1,a2 enter. Terms of higher epsilon order from a2 cannot meet the degree bound. A disconnected active-variable graph gives independent groups of random factors and a zero joint cumulant. The remaining saturated connected multigraph is either a cycle or a path with exactly two linear terminal factors. Repeated edges would give a two-vertex cycle only, outside the k>=3 cycle contribution; self-loop edges are not part of the pair exposure. Four or more terminal factors cannot form a connected saturated graph.

For cycles, e=v=k and l=0. The count is (n)_k/(2k). Each distinct-edge cycle has joint cumulant one: the full product squares every centered variable, and every proper partition contains a factor block with a singly occurring variable. Permutations in the exponential/cumulant expansion cancel the factorial exactly. After the kth difference the contribution is

    (-1)^k (k-1)! h^k / 2.

For paths, l=2, v=k-2 and e=k-3. When v>=2, the undirected-path count is (n)_v/2 and the two external factors contribute (n-1)². The same proper-partition argument gives cumulant one. Ordering the two terminal linear factors and the distinct edges cancels their expansion factorials; there is no extra factor of two. For k=3, the path has one vertex and no edge, and the repeated linear-factor variance has its ordinary coefficient1/2, giving the same formula. The kth-difference contribution is

    (-1)^(k-1) k! h^(k-3) u² / (2ab).

Their sum is precisely the displayed J_k. Higher Bernoulli moments do not enter because every saturated vertex has degree exactly two. This is an all-k source argument, not an extrapolation from a finite coefficient table. Since the underlying finite-cap source formula is analytic and the lower coefficients vanish identically, the divided maps have the required JOINT analytic extension.

## 3. Simultaneous signs and the finite full-rank zero

For a nonzero covector, let k0 be its first nonzero coordinate. Positive values of alpha can be chosen on either side of1/k0. Setting u²=alpha ab h³ then makes J_k a constant times h^k(1-k alpha). For each of those two choices, sufficiently small positive h makes the k0 term dominate all later finite powers. Its signs are opposite. These are valid finite points of the connected domain 0<h<1, u real. Subsequent sufficiently small epsilon makes their physical arms strict; no negative alpha or boundary inheritance is used.

The inherited finite-sum proof applies to this leading J itself. If derivative vectors failed to span, a nonzero covector would be constant on its connected domain, contradicting two-sided signs. A finite sum has a submersion ball. Finitely many image values positively span the target, and integer rounding plus a small displacement in that ball gives an EXACT finite zero sum with a surjective derivative. This is a finite list of source parameters, not a randomized mixture or a fractional cell count. The list, hence N, is fixed before epsilon varies. No cap-uniform bound on N is asserted.

## 4. Exact positive IFT lift and genuine diagonal rank

The scaled sum of the actual logarithmic Newton defects is jointly analytic, with the rank-at-zero map just established. An invertible parameter minor therefore gives an analytic branch of exact defect zeros. For small positive epsilon the parameters remain in one compact strict neighborhood: h stays positive and below one, u stays bounded, both arms stay positive and shrink, and every coin remains exactly a.

The added ordinary pads have durations epsilon²(3-h_i) and epsilon², both strictly positive. They leave all higher logarithmic Newton defects unchanged. Newton inversion then gives the complete set of ordinary no-merger diagonals through the chosen cap at the word's actual pair survival. This does not match the other full-forest coordinates.

The bare pair hazard is epsilon²h_i+O(epsilon⁴) uniformly along the finite compact branch. The actual whole-word hazard is consequently4N epsilon²+O(epsilon⁴), strictly positive and tending to zero. At any prescribed positive target duration, choose epsilon small enough to leave a strictly positive missing ordinary duration and satisfy the requested arm bound; add that ordinary pad. This realizes the fixed diagonal target by a finite strict source, rather than only approaching it as a limit.

The physical arm-map determinant is epsilon⁵/(a²b²), nonzero at fixed positive epsilon. Thus the surviving defect rank is genuine arm-parameter rank with the coin fixed. An independently variable positive leading ordinary duration changes log b2 with derivative-1 while leaving D3,...,Dm unchanged. The full diagonal map therefore has rank m-1. This is rank in the extended physical chart at the target source, not a rank claim on the already constrained fixed-target level set. Strict margins keep a small such chart inside the arm bound and coin restriction.

## 5. Exact stronger Lawson restriction

For every prescribed arm bound eta and open interior coin interval I, the relevant source semigroup permits variable coins within I. It has a genuine open source-group patch: the inherited nonzero D-cell rank polynomial cannot vanish throughout a nonempty open physical parameter box satisfying these strict restrictions.

The new fixed-a diagonal family, with any a chosen in I, supplies the second premise, full diagonal rank, without requiring the full-forest group chart to keep its coins fixed. The earlier accepted weak-cell convex theorem supplies primitive signs within the same arm bound and interval. These compatible premises let the already reviewed Lawson quotient argument exclude a proper signed-time saturation. At cap two the signed ordinary subgroup gives the scalar case directly.

The conclusion is exact finite-product equality after adjoining ALL REAL ordinary durations, now with both physical arm durations short and all physical coins in the requested open interval. It is stronger than the preceding pair-weak result in precisely these parameter restrictions. It does NOT prove full-group saturation with every coin fixed at one single a: only the diagonal family has that stronger fixed-coin property here.

Negative ordinary durations remain mathematical operations. Neither factor count, aggregate positive hazard nor negative-time variation is bounded by this saturation theorem.

## 6. Prior-work and original-master boundary

The earlier uniform-time theorem already solved ordinary DIAGONAL returns at all finite caps, including fixed cell count along a vanishing-hazard branch and full diagonal rank. The accepted new contribution is the fixed-interior-coin, two-short-arm strengthening and its consequence for the restricted signed-time language. It must not be reported as first solving the diagonal problem.

Logarithmic no-merger coordinates add exactly under chronology, so the IFT used here is not subject to the raw linear-kernel cross term in the separate parabolic palette. It still solves no full-forest, exact lower-response or positive-time-clearing equation. It supplies no all-cap ordinary source interior, cap-uniform positive return budget, original legal-prefix rival family, effective stopping or general G4 closure.

The original routing formula, finite-sum/submersion lemma, analytic IFT, group structure and Lawson theorem retain their attribution. Historical novelty of the source-specific coefficient/application was not assessed. No compiler, symbolic/numerical coefficient program, source simulation, parameter search or publication supplied this independent hand review.
