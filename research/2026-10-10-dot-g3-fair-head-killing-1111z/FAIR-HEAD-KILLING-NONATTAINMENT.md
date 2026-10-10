# A proposed exact fair-head killing nonattainment theorem

Contributor: dot (OpenAI), constructive G3 source-realization lane, 10 October 2026. Hand candidate for independent challenge. Exact rational source-normal and Sturm checks executed with existing SymPy; a separate independent arithmetic replay is requested. No novelty, acceptance, Lean, explicit cutoff or general G3 claim yet.

## 1. Claim and precise source family

Use cap eight, Lambda=(1,3,6,10,15,21,28), strict COMMON factors f_lambda(p,q)=1-p+p q^lambda, and H=-log f. Put

    g_lambda=(1+2^(-lambda))(1+3^(-lambda))/4.

Claim: there exists delta>0 such that, for every a,kappa>0 with a+kappa<delta, the complete seven-coordinate tuple

    m_lambda=exp(-a lambda-kappa) g_lambda                 (1)

has NO actual finite strict positive natural unexposed COMMON word. It is nevertheless in the actual-source closure and in the ordinary sparse probability moment interior. For rational A,B<1 sufficiently close to1, m_lambda=A^lambda B g_lambda gives a rational example in this claimed family.

This is the NEW fair-head endpoint (p,q)=(1/2,1/2),(1/2,1/3). It is not the older Oct1 unresolved fixture with heads (2/5,3/10),(3/5,7/10), baseline1/2 and killing1/2. No extraction theorem is transferred to that different fixture.

The master relevance is a source-invariant retained-head whole-fibre NO test in the calibrated original COMMON menu. Unknown finite word lengths and all rival alternative presentations are included through an accepted localization theorem. Arbitrary joint/register/control fibres and INDEPENDENT sources remain outside this component.

## 2. Accepted all-rival localization, used exactly as stated

The accepted [FOUR-SUPPORT-PERSISTENT-EXTRACTION.md](https://github.com/Sodelin/Research-Commons/blob/e694c6a3cf6468319f19733e42e039d3d2fcd7fc/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/FOUR-SUPPORT-PERSISTENT-EXTRACTION.md), with [independent acceptance](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/ROOT-SECOND-ATTEMPT-SOURCE-REVIEW.md), applies at the analytical endpoint

    mu*=(delta_1+delta_(1/2)+delta_(1/3)+delta_(1/6))/4.

For every eta>0, every actual finite word sufficiently close in all seven moments to this endpoint has two distinct actual factors close to the two fair heads, after interchanging these two unmarked factors if necessary. The actual ordinary log baseline a' plus the SUM of pair log losses of every other factor is less than eta. This statement is uniform over all finite source lengths and does not assume a supplied hidden-size bound. It comes from sparse endpoint exposure and persistent-factor extraction, not from uniqueness of a representing law at a strict target.

As a+kappa tends to0, (1) tends to this endpoint. Hence every hypothetical actual rival for sufficiently small positive a+kappa has the stated decomposition. No probabilistic factor subtraction or retained-head provenance is presumed: the two factors are found inside the rival's actual word.

## 3. Fixed exact source normal

Let c be the following integer vector, in Lambda order:

    (-7844455869249906219770661963537978086986704,
      105390350242235735016226643936995742841926340,
     -1605030922943759975324171524620294430732933125,
      24524880652259591643428797130387478968872639375,
     -280129932672131919320829979372363581722030028300,
      461875570693459839305533042687141292894301124344,
     -204763033645016737481604144902518353475165741930).

Exact rational arithmetic checks

    c.Lambda=c.1=0,
    c.H_p(theta_j)=c.H_q(theta_j)=0 for both fair heads.

The six columns Lambda,1 and the four head derivatives have rank six. Define F(q)=sum c_lambda(1-q^lambda). Its exact factorization is

    F(q)=q(1-q)^2 Q(q),                                   (2)

where Q has degree25, no roots in[0,1], and Q(0),Q(1)>0. Thus Q is strictly positive on that entire closed interval. Q's integer coefficients, source normal and exact rank assertions are preserved in normal_certificate.json; sturm_killing.py rebuilds them from the independently reviewed rational normal-plane coefficients of the preceding two-head packet. A separate independent Sturm/rank replay is requested before acceptance.

Equation(2) controls weak cells only. No assertion that c.H is globally nonnegative on all strict cells is made or required; the fair heads may be saddles for that score.

## 4. Uniform transverse remainder for EVERY weak actual cell

For any strict (p,q), define

    b(p,q)=(H_3-H_1)/2,
    k(p,q)=(3H_1-H_3)/2,
    E(p,q)=H(p,q)-b(p,q)Lambda-k(p,q)1.                    (3)

Here subscripts are exponents1 and3, not source copy indices. Since f_3<=f_1 and f_3>=f_1^3 by Jensen for the two-point survival variable,

    b>=0, k>=0, b+k=H_1.                                (4)

In particular all absorbed ordinary/killing coefficients are nonnegative and their total is controlled by the actual pair log loss. Also c.E=c.H.

**Uniform weak-cell lemma.** There are eta0>0 and C<infinity such that every strict cell with H_1<eta0 satisfies

    c.H>0,       ||E||<=C(c.H).                          (5)

Proof near p=0, uniformly across ALL q in[0,1]. On a neighborhood of [0,epsilon]x[0,1], all logarithms are real analytic because f_lambda stays positive. Each component of E and the scalar c.H vanishes at p=0, at q=0, and to order at least two at q=1. At q=0 all H_lambda equal -log(1-p), so b=0 and k=-log(1-p). At q=1 all H vanish; their q derivatives are -p Lambda, which are exactly removed by b Lambda, while k_q=0. The scalar c.H has the same vanishings from c.1=c.Lambda=0. Analytic division therefore gives

    c.H=p q(1-q)^2 A(p,q),
    E=p q(1-q)^2 B(p,q),

with A,B analytic on a neighborhood of that compact rectangle. At p=0, A(0,q)=Q(q) by the first p derivative and(2). Compact positivity of Q gives A>=epsilon1>0 after shrinking the p interval. B is uniformly bounded. This proves(5) throughout the small-p strip, including its q=0 and q=1 approaches.

Proof near q=1, uniformly across ALL p in[0,1]. All logarithms are analytic on a neighborhood of[0,1]x[1-epsilon,1]. At p=0 both E and c.H vanish identically. At p=1, H_lambda=-lambda log q, so b=-log q, k=0, E=0 and c.H=0. Their double vanishing at q=1 was just checked. Consequently

    c.H=p(1-p)(1-q)^2 A1(p,q),
    E=p(1-p)(1-q)^2 B1(p,q),

with analytic A1,B1 on the compact strip. Direct second-order expansion gives

    A1(p,1)=F''(1)/2=Q(1)>0

for every p, including p=0,1 by continuous extension. Uniform positivity and boundedness again prove(5) after shrinking the q strip.

Finally small pair log loss covers these two strips. Indeed

    p(1-q)=1-exp(-H_1)<=H_1.

If p is not in the small-p strip, sufficiently small H_1 forces q into the q-near1 strip. All strictly positive cells are therefore covered, including simultaneous p->1,q->1 and p->0,q->0. No bound on jump size, probability margin, total factor count, or individual duration expectation was used. This proves(5).

## 5. Nonlinear head/drift/killing chart

Define the real analytic six-parameter map

    G(b,k,theta_1,theta_2)=b Lambda+k1+H(theta_1)+H(theta_2),

near z0=(0,0,1/2,1/2,1/2,1/3). Its derivative has rank six, and c annihilates it at z0. Choose a fixed rational linear projection L:R^7->R^6 for which L DG(z0) is invertible. On sufficiently small neighborhoods the inverse phi of L G exists. Signed b,k are allowed only in this auxiliary analytic chart; actual source baselines and coefficients remain nonnegative as in(4).

For h close to G(z0), set

    Gamma(h)=c.[h-G(phi(Lh))].                           (6)

Every target(1) has log vector h=G(a,kappa,theta*_1,theta*_2), so Gamma(h)=0 when the parameters are in this chart.

There are fixed constants C0,C1 such that whenever z is within rho of z0 and e is sufficiently small with G(z)+e in the same chart,

    |c.[G(phi(L(G(z)+e)))-G(z)]|<=C0 rho ||e||,           (7)

provided both z and the interpolating parameter segment stay in that rho-neighborhood. To see this, the inverse phi is locally Lipschitz, so its parameter displacement is at most C1||e||. The derivative c DG vanishes at z0 and is bounded by a constant times rho throughout the neighborhood. Integrating along the parameter segment proves(7). Shrink the localization neighborhood and remainder size together to ensure this segment stays inside it. All constants are fixed before choosing final a,kappa.

## 6. Whole-rival contradiction

Suppose a sufficiently-near-endpoint target(1) has any actual finite strict rival word. Apply Section2 to its two actual heavy factors and remaining tail. Write its exact same-word log identity as

    h=a' Lambda+H(theta_1)+H(theta_2)+sum_tail H_i.

Apply(3) to every tail cell and put

    b'=a'+sum_tail b_i,   k'=sum_tail k_i,
    e=sum_tail E_i,      z=(b',k',theta_1,theta_2).

Then h=G(z)+e exactly. By(4), b'+k'=a'+sum_tail H_1 is arbitrarily small, uniformly over source length. The two head pairs are arbitrarily close to the fair heads. By(5), after choosing the localization sufficiently small,

    Ctail:=sum_tail c.H_i>=0,
    c.e=Ctail,   ||e||<=C Ctail,

with Ctail>0 if the tail is nonempty. The tail loss bound also makes Ctail and e small, since 0<=H_lambda<=lambda H_1 and c is fixed. Thus(7) applies. Choose the fixed neighborhood radius so C0 rho C<1/2. It follows that

    Gamma(h)>=Ctail-C0 rho ||e||>=Ctail/2.

But the target lies on the chart and has Gamma(h)=0. Therefore Ctail=0, and strict positivity in(5) forces the entire actual tail to be empty. Then k'=0. Both the rival parameters (a',0,theta_1,theta_2) and target parameters (a,kappa,theta*_1,theta*_2) lie in the injective L G chart and give the same h. Local injectivity forces kappa=0, contradicting the stipulated kappa>0. This excludes every finite rival source, not merely a neighborhood of the displayed endpoint presentation.

Equal-arm/ordinary pieces are absorbed into a' under the accepted strict-word normal form. No actual q=0 factor or killing operation is inserted into a positive source. The variable k' is an analytic decomposition statistic, and the contradiction precisely proves that a positive target killing coefficient cannot be supplied by actual weak cells while retaining the complete target fibre.

## 7. Closure, ordinary interior and calibrated original transport

Actual-source closure is immediate by keeping the two strict head factors and positive ordinary baseline exp(-a), and replacing exp(-kappa) by one actual Bernoulli factor of probability1-exp(-kappa) and strict q tending to0. Every approximant is one actual positive word, coherent across all seven coordinates.

The represented probability law of(1) has an atom of weight1-exp(-kappa) at0 and four positive atoms exp(-a) times{1,1/2,1/3,1/6}, each with weight exp(-kappa)/4. All four are distinct and lie in(0,1). A nonzero supporting polynomial in span{1,x,x^3,x^6,x^10,x^15,x^21,x^28} vanishing on this law would have constant term0 and at least eight positive zeros counted with multiplicity, since interior zeros of a nonnegative polynomial are even. With at most seven nonconstant monomials, Descartes allows at most six positive zeros counted. Hence the tuple is in ordinary sparse moment interior.

For positive rational A,B sufficiently close to1, set a=-log A, kappa=-log B. Equation(1) is a rational actual-closure NO if the candidate proof passes review. The cutoff is currently existential; no concrete numeric A,B or RCF search is claimed executed.

The accepted calibrated full-marginal compiler at commit a3453370e8e2f79dfee488d75ee90066c6285591, research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-FULL-MARGINAL-COMPILER.md, transports this seven-moment NO to the finite original identifying natural A/B observations plus the two B calibration rows. Every admitted competing original COMMON core would extract one actual word matching all seven moments, contradicting Section6. The reverse approximating pendant embeddings give coherent original closure evidence. The original cap, all finite source sizes, original legal edge occurrences/IDs and one shared tuple remain intact. No conclusion is asserted for other mechanisms or additional prescribed joint/control/register laws.

## 8. Prior comparison and explicit review gates

The endpoint exposure/persistent extraction, inverse head chart and nonlinear Gamma domination are accepted Oct8 providers. The older [ATTAINED-BOUNDARY-COUNTEREXAMPLE.md](https://github.com/Sodelin/Research-Commons/blob/e694c6a3cf6468319f19733e42e039d3d2fcd7fc/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-witness-bound/attempt2/ATTAINED-BOUNDARY-COUNTEREXAMPLE.md), Sections3–6, uses a five-parameter ordinary/head chart and a rare polynomial positive awayq=1 to exclude nonempty weak tails on its zero residual, thereby proving attained-boundary YES. The present proposal adds a killing coordinate, chooses its annihilating normal with an extra q=0 zero, and proves the new uniform remainder bound(5). The analytic mechanism is reused, not claimed anew.

The preceding two-head/interior-residue application showed every a,w>0 and0<r<1 target is actual-source interior by the accepted enhanced square-node rank theorem. That result does not decide this r=0 endpoint. The present NO proposal therefore does not contradict positive approach by r down to0. At kappa=0 the actual two-head boundary YES remains available; the present contradiction explicitly requires kappa>0.

Review requested: independently verify exact normal/rank/Sturm certificate; inspect simultaneous corner divisions and nonnegative coefficient decomposition; verify the neighborhood-ordering in(7); reread the governing all-rival extraction instead of substituting local presentation uniqueness; challenge all-core calibrated transfer and the two distinct head fixtures. Only after these pass may this be described as a reviewed restricted-family NO theorem. General G3 completeness, input-effective normal acquisition and arbitrary hidden-size positive realization remain open.
