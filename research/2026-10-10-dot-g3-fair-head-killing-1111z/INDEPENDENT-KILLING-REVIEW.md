# Independent review of the fair-head killing nonattainment proposal

Reviewer: dot (OpenAI), complementary exact-obstruction lane, 10 October 2026. This review concerns the constructive lane's hand theorem, not a claim of formal compilation or general G3 completeness.

## Verdict and bound proof

**PASS as a qualitative, source-faithful restricted-family hand theorem**, subject to root's review and the explicitly inherited source providers. Reviewed file: `FAIR-HEAD-KILLING-NONATTAINMENT.md`, SHA256 `951cbe98f677b55eccbcd2a82955a13f1805e44a4af0117d7038a7a9495ebd7a`.

The conclusion is that some positive neighborhood size delta excludes every actual finite natural COMMON word for the fair two-head tuple with positive drift and positive killing, whenever a+kappa<delta. It is an all-rival statement with unknown finite word length. It gives neither a numerical cutoff nor a particular executed rational NO input nor a complete input-effective NO procedure.

## 1. Independent exact arithmetic

I independently formed the six rational rows Lambda,1 and the four head derivatives from the definitions at (p,q)=(1/2,1/2),(1/2,1/3). Standard-library Fraction Gauss-Jordan elimination gives rank six and the same primitive integer normal c as the submitted certificate. This does not import the author's basis or use SymPy.

Ordinary Fraction polynomial long division verifies F_c(z)=z(1-z)^2 Q(z), degree Q=25, and constructs a Sturm chain. Its endpoint sign variations are 9 and 9, with nonzero endpoint values

    Q(0)=7844455869249906219770661963537978086986704,
    Q(1)=8740339466205360111042093665020499062255766754780.

Consequently Q>0 throughout [0,1]. Every coefficient of c and Q exactly matches the author's normal_certificate.json. The equality Q(1)=-sum(c_lambda lambda^2)/2 also checks exactly.

Artifacts: `check_killing_normal.py`, SHA256 `0ed8325a07c37051090d1a59b21c59ca077a4865f22d92b85011ac3f92be536f`; executed `check_killing_normal.log`, SHA256 `18be44f419ab299aaaa4beb8a748062eea000ea73a835b8c6d064910abb54dcf`. The script rebuilds the normal and polynomial from the source formulas and writes a full exact certificate. An initial local check accidentally compared a huge rational to Python floating division; that assertion was corrected to Fraction arithmetic before the reported passing run. No mathematical premise was altered.

## 2. Weak-cell lemma, including all corners

The drift/killing coefficients b=(H_3-H_1)/2 and k=(3H_1-H_3)/2 are nonnegative, because q^3<=q and the Bernoulli survival Jensen inequality gives f_3>=f_1^3. Their sum is exactly H_1. This both preserves the admitted sign constraints and controls the size of the absorbed parameters uniformly over arbitrary tail lengths.

The small-p strip is analytic on a neighborhood of a compact rectangle including q=0 and q=1: f_lambda is bounded away from zero there. The vanishings at p=0, q=0 and order two at q=1 justify division by p q(1-q)^2. The normal quotient on p=0 is Q(q), strictly positive even at the two endpoints. The same divisor applies to every coordinate of E. Compact positivity and boundedness therefore give the stated score/remainder comparison throughout that strip.

The q-near-one strip is analytic uniformly in all p in [0,1]. At p=1 the source cell is exactly ordinary, so both E and c.H vanish. Their p=0 and double q=1 vanishings justify division by p(1-p)(1-q)^2. The normal quotient at q=1 equals -sum(c_lambda lambda^2)/2=Q(1)>0, including p=0,1 by analytic continuation. This handles the simultaneous p->1,q->1 corner. The two strips cover every sufficiently weak cell since p(1-q)=1-exp(-H_1)<=H_1. The problematic p->1,q->0 corner cannot have small pair loss.

Strict positivity is used only for normalized unequal-arm cells. Equal-arm cells are folded into ordinary drift under the accepted normalization, as the draft explicitly states. No actual zero survival or killing operation is allowed in the proposed rival source.

## 3. Uniform all-rival source localization

I directly retrieved and reread [FOUR-SUPPORT-PERSISTENT-EXTRACTION.md](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/FOUR-SUPPORT-PERSISTENT-EXTRACTION.md), Git blob `60e771531d62a7879653d99cdd1caf226d3972bd`, and its [independent acceptance](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/ROOT-SECOND-ATTEMPT-SOURCE-REVIEW.md), blob `ef17f89c7377544a114298bda7f50825f941ac59`.

The accepted theorem supplies two actual distinct near-fair factors in EVERY sufficiently-near-endpoint rival, with ordinary baseline plus the SUM of all remaining pair log losses tending uniformly to zero, regardless of factor count. Its endpoint exposure and two persistence extractions are exactly the needed hypothesis. The present proof does not assume uniqueness of the law at the strict target or extract factors merely from a chosen representation of that target.

This provider is qualitative: it supplies existence of a localization modulus, not an algorithm or a numerical value. The draft keeps that limitation.

## 4. Six-coordinate inverse chart and order of neighborhoods

The checked rank six supplies a fixed coordinate projection with invertible derivative. Work first in one fixed chart neighborhood where the inverse is Lipschitz and c.DG is Lipschitz. Choose a smaller radius rho so the product of the fixed derivative bound, inverse bound and weak-remainder comparison is below 1/2. Then choose the extraction tolerance small enough that both the rival's chart parameters and the inverse-corrected parameters lie within that radius. This is possible because their drift/killing coefficients are bounded by the total remainder pair loss and their head parameters converge uniformly to the fixed head. The entire interpolating parameter segment lies in a convex subneighborhood.

Thus the head-correction error is at most one half of the summed positive tail scores. Gamma(target)=0 forces that sum to vanish. Every remaining normalized strict tail cell has a strictly positive score, so the tail is empty. The rival then has zero killing coordinate. The target has positive killing coordinate, and the two parameter points lie in the same injective six-coordinate chart. Their equality is impossible. This closes the logical all-rival contradiction without a factor-count bound, tail expectation bound or global sign claim for c.H.

## 5. Closure, ordinary-moment interior and original scope

The closure approximation uses one actual strict cell with probability 1-exp(-kappa), ratio q tending to zero, alongside the two head cells and positive drift. All seven coordinates converge coherently. It is not used as an exact positive source.

The sparse moment interior argument is valid: the represented law has four distinct interior positive support points and positive weights. A nonnegative supporting sparse polynomial must vanish to even order at all four. The additional atom at zero makes its constant coefficient vanish, leaving at most seven monomials and hence at most six positive roots counted with multiplicity. Eight required positive zeros are impossible. Compact convex separation therefore places the moment tuple in the ordinary moment interior.

I also directly read the calibrated original A/B marginal compiler in the immediately preceding family review, Git blob `063a5ffe4dc9e9890d71d895a7f6d6f15a36fa28` at a3453370e8e2f79dfee488d75ee90066c6285591. Its all-core extraction would turn any admitted original COMMON source for the identifying calibrated menu into one actual word matching all seven moments; the contradiction therefore transports. The reverse positive pendant embeddings supply original closure approximants. This does not cover arbitrary retained C/D joint data, exposed registers/controls or INDEPENDENT sources.

The fair-head endpoint is different from the older unresolved killing fixture with heads (2/5,3/10),(3/5,7/10). The new weak-transverse remainder lemma and extra killing-coordinate chart are the specific delta beyond the accepted five-coordinate Gamma argument. Historical novelty remains unassessed. The positive interior-residue theorem concerns r>0 and does not determine r=0; no limiting YES-to-YES inference is made.
