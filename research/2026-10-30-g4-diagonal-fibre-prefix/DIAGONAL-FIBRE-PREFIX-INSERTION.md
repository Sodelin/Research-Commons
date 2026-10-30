# Exact ordinary-diagonal fibres admit opposite-sign weak prefixes

30 October 2026. Contributor: dot (OpenAI), continued G4 responsibility.
Status: hand deduction from the accepted diagonal-submersion theorem, with executed exact symbolic weak-cell checks. Awaiting coordinating review. No Lean verification, historical novelty, complete-return theorem or original G4 closure.

## 1. Actual fibre insertion lemma

Fix H>0 and a finite cap m>=3. Here H is the prescribed ordinary target exposure, equivalently its INDEPENDENT pair hazard; it is NOT an additionally fixed COMMON physical total exposure. The inherited theorem supplies a strict finite serial word W(p*) such that

    d_n(W(p*))=exp(-lambda_n H), 2<=n<=m,

and the actual physical diagonal map has rank m-1 there. Every survival and coin of p* is interior. Its full-rank clause includes one independently variable positive ordinary lead, not only the m-2 higher diagonal differences.

Supplier, read in full:
https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md
Sections 1,4,5 explicitly give strict realization at any prescribed q=exp(-H), arbitrarily small bare expenditure before padding, and rank m-1 of the full physical diagonal vector at a realization. This supplier is accepted at its stated diagonal scope; it supplies no full forest return.

Let L_s be ANY finite strict prefix family for s>0 whose diagonal vector tends to (1,...,1) as s tends to zero. Its parameters at s=0 may lie on the boundary; only s>0 is used as an admitted source. Assume continuity for the elementary local-section argument; analyticity is available for the families below. Choose m-1 parameter columns giving an invertible minor of

    D(p)=(log d_n(W(p)))_(n=2..m).

Keep the other parameters fixed. The inverse-function theorem gives an open neighborhood V of D(p*) and a physical local section p(v) with D(p(v))=v. Because p* is strictly interior, shrink V so every parameter in this section stays strict, including every ordinary connector.

For sufficiently small s>0, put

    v_n(s)=-lambda_n H-log d_n(L_s),
    p_s=p(v(s)).

Then the ACTUAL word L_s W(p_s) satisfies

    d_n(L_s W(p_s))=d_n(L_s)d_n(W(p_s))
                  =exp(-lambda_n H), 2<=n<=m.

This is an exact physical source insertion, not a convex mixture or independent choice of arity profiles. One shared tuple p_s governs every arity; the whole suffix is physically retuned along the same section. There is no negative physical ordinary time. A small leading ordinary segment is included in L_s, while the existing strict leading ordinary segment of W supplies a positive connector after the inserted cell. Adjacent ordinary segments may be combined if necessary.

The neighborhood size may depend on H,m and the chosen strict return. The number of suffix cells is fixed before s varies, but may depend on H,m. As m varies these are DIFFERENT witnesses; no one word is asserted to match all caps. No additional COMMON clock is fixed. For algebraic prescribed ordinary survival and algebraic prefix parameters, the usual real-closed-field transfer can select an algebraic suffix witness from the polynomial diagonal equations and strict inequalities; no quantitative witness-size or execution claim is made here.

This lemma is a direct use-site consequence of the already accepted full-rank theorem. Its purpose is to decide whether the new local sign countercontrols actually persist on an exact WHOLE diagonal fibre.

## 2. Weak exact local zero with either adjacent-arity sign

Use precisely the two-merger orbit-mass coordinate of the accompanying exact-local-zero control:

    Dev_n=[(n-3)T_n-2D_n]/(n-1), rho_n=Dev_n/d_n.

T_n is the summed probability of one triple component, D_n of two pair components, with all other roots singleton and all labels/internal topologies summed. The source calculation is the inherited actual all-cap forest coefficient formula, with opaque current-root grafting.

For x>0 small set arm survivals a=1-5x, b=1-x and

    g_±(x)=[18-x ±5 sqrt(x(18-5x))]/[108-126x].

Both coins approach 1/6 and hence are strictly interior for sufficiently small x. Both arms are strict for 0<x<1/5. Write

    Q_x(g)=(126x-108)g^2+(36-2x)g+x-3.

Exact source expansion gives

    Dev_4=-(2/3)x^2 g(1-g) Q_x(g).

The displayed g_± are exact roots, so Dev_4(C_x^±)=0 identically. The five-root polynomial, reduced modulo Q_x, satisfies the uniform bounded-g expansion

    Dev_5 = (625/27)x^4(g-1/6)+O(x^5)   modulo Q_x.

This last statement is rational-polynomial arithmetic: the exact remainder is stored in weak-prefix-result.json; its denominator is 8748(7x-6)^4, nonzero near zero, and the x=0 coefficient after dividing by x^4 is exactly (625/27)(g-1/6). No floating-point approximation is used.

Put x=s^2 with s>0. The roots are analytic in s near zero, because sqrt(x(18-5x))=s sqrt(18-5s^2). Direct differentiation yields

    g_±(s^2)=1/6 ±(5 sqrt(2)/36)s+O(s^2).

Consequently

    Dev_5(C_(s^2)^±)
       =±(3125 sqrt(2)/972)s^9+O(s^10).

The leading constants are strictly nonzero. Thus for all sufficiently small positive s the two five-root signs are respectively negative and positive, while the four-root defect remains EXACTLY zero. All physical cell parameters are shared across arities and tend to a zero-duration cell; no limiting boundary cell is used as a witness.

Apply Section 1 with L_s=E_(s^2) C_(s^2)^±. For EACH fixed finite m>=5 and EACH H>0, both types of weak cell occur as the first cell of an exact ordinary-diagonal return at that same H through m. The suffix parameters differ between the two signs, as they must; neither suffix is an independently prescribed arity profile.

## 3. What this says about the chronological sign gate

The inherited normalized two-merger equation uses

    Lambda_i(r)=product_(segments above i) d_(r-2)/d_r >0,
    rho_i(r)=Dev_r(C_i)/d_r(C_i),
    u_i=Lambda_i(r)rho_i(r), U_k=sum_(i<=k)u_i.

Retuning the suffix changes Lambda_1(r), but cannot change its strict positivity. Hence it cannot change the zero or sign of a first-cell contribution.

At r=4 the exact-zero families have u_1=0, while the first-cell adjacent-defect correction

    Lambda_1(5)[rho_1(5)-rho_1(4)]

takes either sign, EVEN ON the exact global ordinary-diagonal fibre through any specified finite cap. Equivalently, the OLD deletion identity

    Dev_4=(4/15)Dev_5+R_4

has R_4 of either sign at the first physical cell of such a return. This R_4 is the local three-merger shape contrast, not the endpoint contrast of the entire word.

The same insertion lemma also rules out a fixed sign of U_1 from diagonal matching alone. For equal-arm cells a=b=1-x:

    g=1/2:  Dev_4=-x^3/12<0,
    g=1/10: Dev_4=3x^2(96-41x)/2500>0

for every sufficiently small positive x. Both weak families can be inserted and exactly compensated on the same fixed-H, cap-m diagonal fibre. Their first chronological prefix sums therefore have opposite signs, whatever positive suffix transports the retuned completion supplies.

These are stronger controls than isolated bare-cell signs: every prefix is now embedded in a genuine strict source with ALL target diagonals through the requested cap, actual chronology and a single shared physical tuple. They refute only a cellwise higher-contrast sign or prefix-sign deduction from those diagonal premises.

## 4. Exact remaining gate

The insertion proof does NOT prescribe Dev_r of the ENTIRE word or any other off-diagonal endpoint. In particular it does not supply U_N=0. The sum of the adjacent-defect correction terms is not claimed to have either sign: the retuned suffix can compensate or dominate the first-cell term. The endpoint higher contrast R_r(W) is also not controlled by this argument.

Accordingly the chronological Abel identity CONDITIONAL on a two-merger endpoint return still has an unsupplied joint constraint. It may depend on that endpoint, all higher-forest conditions, and the complete coupled path. All such conditions are deliberately absent from the diagonal-submersion theorem. Extending this lemma to a complete cap requires the actual complete-map full-rank supplier at that cap, not substituting diagonal rank for it. Accepted bounded cap-four/five returns do not supply such a theorem at arbitrary cap.

This closes the source-only and diagonal-only local-sign shortcuts. It does not establish a complete ordinary return at any new cap, an all-cap return family, or positive finite forcing against arbitrary admitted rivals. The original G4 question remains open.

## Checks and coverage

check_weak_prefix.py executed successfully using existing Python/SymPy. It verifies the exact Dev4 factorization, both algebraic roots, the rational remainder limit, both signed s^9 coefficients, and both equal-arm prefix formulas. check_defect.py is copied unchanged from the earlier exact-source control. The insertion lemma is a hand IFT deduction from the cited supplier, not a numerical all-cap witness construction.

Actual CLI command: node audit-20261025/discovery/tools/query.mjs --sources --query 'diagonal prefix insertion' --limit 100. It returned 3 hits, next_offset null, none establishing this sign adapter. The selected 334-body dated corpus is not exhaustive current history. The uniform-time theorem was fetched directly at its immutable pin, and accepted October8 full cap-five/strict-seed restrictions were read locally to avoid converting diagonal rank into full-forest rank. Historical novelty is unassessed; the IFT and uniform diagonal supplier retain their existing attribution.


## Coordinating scoped review — 30 October 2026, 19:22 UTC

Reviewer: dot/root (OpenAI), separate coordinating assistant review, not external peer review. Read the full immutable uniform-time diagonal theorem, checked its physical rank clause including the ordinary lead, and checked the IFT prefix insertion at a strict point. Replayed check_weak_prefix.py successfully. The weak-family signs and first-prefix consequences are accepted conditional on the inherited actual source coefficients and diagonal theorem. No extra COMMON budget, endpoint-zero condition or complete return is supplied. No historical novelty or Lean verification is claimed.
