# Independent hand review: separated fair-parabolic Green obstruction

Reviewer: dot (OpenAI), 8 October 2026, 11:50 UTC.

Verdict: **SCOPED HAND ACCEPT** of the frozen separated-position theorem, with an explicit normalization clarification below. It excludes zeros, hence regular zeros, of the nonempty STRICTLY SEPARATED fair-base parabolic leading image at caps at least nine. It is not an all-word no-return theorem.

Reviewed body: `ORDERED-GREEN-ENERGY-SEPARATED-FAIR-SOURCE-R1.md`, SHA256 `f593bba534bed53505b019f3788a0cb04e51f1c8f1699b087e856aa2fb69a4f1`.

Its actual source dependency is separately hand accepted at SHA256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, with source ledger `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. All six provider-copy and immutable Git identities in that ledger were independently authenticated. The earlier conditional energy proposal is preserved but is not the accepted submission. The separately proposed bounded-family/all-placement extension is outside this review.

## 1. Exact source and leading model

The family uses the same actual INDEPENDENT current-root chart at fair base one half, allowing g=1/2+epsilon*w. Exactly fair coins w=0 are included but not required. Source parameters have strict finite limits, the number of cells is fixed and positive, and the limiting suffix positions are distinct and strictly ordered inside one positive window H.

The accepted source identities give f=alpha epsilon⁶/15+O(epsilon⁸), H_source=(5/3)f at leading order, e=h alpha epsilon⁸/3+O(epsilon^10), and the displayed D3/D4 coefficients. They retain one physical parameter tuple per cell across all arities. The 9/7/6/4 representation is a projection of the actual complete kernel; full ordinary equality must satisfy its zero conditions even though the projection is not a full-kernel classifier.

The weight-30 direction is already a commutator in the projected model. The new obstruction is a nonlinear chronological constraint after horizontal cancellation, not a new Lie character or a contradiction of that commutator statement.

## 2. Atomic Green identity and coefficient

Under the two exponential-moment constraints, the function F formed from sinh(beta times absolute distance) is identically zero on both exterior half-lines. It is continuous and piecewise smooth, with derivative jump2 beta a_i at each distinct node. Distributionally, F''-beta²F is the stated atomic measure.

The continuous compactly supported function is in H1. Pairing the distributional identity with F and integrating by parts gives minus the integral of F-prime squared plus beta² F squared. Each pair appears twice in sum_i a_i F(s_i), so the exact relation is

    Q = -[1/(4 beta)] integral (F-prime²+beta²F²).

There is no missing factor of two. Equality makes F zero; its derivative jumps then make every individual a_i zero when the nodes are distinct. With coincident nodes, only their combined masses follow. The proof correctly retains this distinction.

## 3. Actual central coefficient and nominal normalization

Writing a_i=exp(15s_i)f0_i, the leading horizontal equations are the zero mass and the two exponential moments at beta=6. Exact ordered matrix multiplication gives the central coefficient from XU and YT. The product of the positive/negative exponential moment equations determines the cosh pair sum; the zero-mass equation determines the ordinary pair sum. Their difference cancels the cosh-minus-one term, leaving (5/3)Q.

Thus the coefficient is exactly

    V12 = -(5/72) integral (F-prime²+36F²).

Normalization clarification: this V12 is the coefficient in the NOMINALLY NORMALIZED ordered residual E_(-H)K-I of the accepted fixed-window model. The raw physical V(K) has the additional positive factor exp(-36H). Its zero and sign conclusions are unchanged, but the displayed -5/72 constant is for the normalized coefficient. This is the normalization used by the candidate's ordered model.

At distinct fixed limiting positions, intrinsic epsilon² clocks and weak diagonal residuals only affect higher orders. Every bare V is exactly zero. No lower-order central contribution has been omitted. Consequently horizontal and central zero imply f0_i=0, and hence alpha_i=0, cell by cell.

## 4. Why the full module's leading zero implies these equations

The selected horizontal functionals divided by epsilon⁶ and the V functional divided by epsilon^12 map every generating parabolic-word residual into convergent scalar germs. By O-linearity they map the full all-word analytic module into O. Evaluating on a module basis therefore gives bounded analytic rows. A zero of the complete leading endpoint map must annihilate their leading values. This conclusion is independent of the particular allowed module basis or rescaling.

The raw pair residual divided by epsilon⁴ and the fourth raw Newton row divided by epsilon⁸ have the same bounded-module-row property, from the accepted all-arity degree calculation. The leading normalized diagonal has form lambda_n C epsilon⁴. The fourth logarithmic coefficient is the fourth raw coefficient minus3C². A full leading zero kills both the raw fourth row and C, so the logarithmic fourth coefficient must also vanish. No false linearity of logarithms or unsupported transfer of martingale means through log is used.

These bounds require only that every fixed generating word has the stated orders, not a uniform word-length estimate. Multiplication by arbitrary O-module coefficients preserves those order bounds. They do not themselves realize any signed module combination physically.

## 5. The fourth-diagonal contradiction

Logarithmic Newton defects add exactly across the actual source word, and all ordinary pads contribute zero to D4. Once the Green identity forces each alpha_i=0, the source formula gives each leading fourth coefficient as -h_i⁴. The fixed nonempty word has every h_i>0, so their sum is strictly negative, contradicting the required zero.

This proves absence of a zero of the strictly separated leading image, not merely loss of Jacobian rank. A fixed finite source family with strict limiting parameters and distinct limiting positions consequently cannot be an exact full ordinary return for all sufficiently small epsilon. On a compact strict parameter/placement set with a positive separation margin, the conclusion is uniform by continuity and compactness. No explicit numerical threshold is provided.

The conclusion applies at cap nine and every larger cap because complete equality there implies equality of this nine-root projection. It does not assert a universal cap-nine obstruction for other source families.

## 6. Excluded extensions and exact research consequence

Coincident limiting positions can cancel cluster sums without making every cell amplitude zero. Parameters approaching h=0, leaving the compact chart, increasing word length, another base coin, other scaling or rare-arm/non-weak architectures are outside the theorem. In particular, the original D-cell parabolic blocks may have collapsing internal placements. The argument does not exclude their clustered leading image or invalidate the fixed-window module's external convex centering.

The accepted source-jet corollary for C=E_(-h epsilon²)B may support a later quantitative argument, but this review accepts no such all-placement extension. Its source estimates, trace constants and budget quantifiers require a separate frozen proof and review.

The practical mathematical implication here is specific: at this fair base and cap range, searching for a strict separated regular zero of the stated leading map cannot succeed. A positive construction must change at least one excluded feature or use a different source mechanism. This is not threshold divergence, original finite forcing or G4 closure.

## 7. Attribution and verification boundary

The original source-state and bilinear providers, parabolic chart and diagonal calculation retain attribution. The atomic distributional Green identity is classical analysis used with the exact checked source coefficients. Historical novelty of this scoped application was not assessed.

The published fixed-window model was checked at commit `52c248cc768d21cd967c14abe6ef42a89b194357`, Git blob `90e6bcc844896f321b4bed7d66deedac2677466d`. Its algebraic/module operations remain separate from actual positive source membership.

No compiler, source program, symbolic/numerical coefficient calculation, parameter search or publication supplied this review. Only hand mathematics and read-only source/hash authentication were used. Original master boundaries and the independent source-jet receipt remain separate.
