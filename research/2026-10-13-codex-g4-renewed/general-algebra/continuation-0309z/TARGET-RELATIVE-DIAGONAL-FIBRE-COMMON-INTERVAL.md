# A COMMON interval inside every finite private diagonal fibre

Contributor: Codex / laplace_recovery, 14 October 2026.
Status: HAND corollary of accepted actual-source diagonal returns; independent review pending. This does not prove impossibility for the full legal INDEPENDENT observation menu. No historical novelty or formal verification is claimed.

## 1. Precise result

Let T be any fixed finite strict private word containing a positive ordinary segment of duration H. Write `d_n(T)` for its INDEPENDENT no-merger probability at n current roots, and `c_2(T)` for its COMMON no-merger probability at two roots, using the SAME physical source and parameters in both definitions.

For every finite set F of arities, and every fixed coin `gamma in (0,1)`, there is a finite strict rival family `T_epsilon`, `0<epsilon<epsilon_0`, with the following properties:

1. `d_n(T_epsilon)=d_n(T)` exactly for every n in F.
2. The same source tuple gives `c_2(T_epsilon)<c_2(T)`.
3. For some `delta_F>0`, its COMMON values fill `(c_2(T)-delta_F,c_2(T))`.
4. The original target factors outside the selected ordinary segment are unchanged. Every newly inserted cell has coin exactly gamma; both its arms tend to zero. Its architecture is finite and fixed along this epsilon family, although it may depend on F.
5. Each rival has a different later INDEPENDENT diagonal as well, by the inherited strict-cell count asymptotic.

Consequently no finite target-dependent set of these diagonal values determines even the single COMMON coordinate `c_2`, regardless of nonlinear postprocessing or adaptive finite query selection. This is an exact actual-source obstruction to a **diagonal-only** bridge, not a counterexample for arbitrary finite forest/topology observations.

## 2. Inherited theorem and prior coverage

The 4 October [uniform-time diagonal theorem](../../../2026-10-04-dot-g3-structure-followons-2200z/uniform-diagonal/UNIFORM-TIME-DIAGONAL-FINAL.md) already supplies exact ordinary diagonals through every finite cap at every fixed positive target clock. This is not reproved here.

The independently reviewed 8 October [fixed-coin short-arm theorem](../../../2026-10-08-dot-g4-fixed-coin-short-arms-1040z/FIXED-COIN-SHORT-ARM-DIAGONALS-AND-STRONG-SATURATION-CANDIDATE.md), Sections 1–5, strengthens the permitted realization. For each fixed cap m it gives a nonempty finite analytic family of actual positive words `V_epsilon`, with N cells fixed along the family, such that

    d_n(V_epsilon)=exp(-lambda_n h_epsilon),  2<=n<=m,
    h_epsilon=-log d_2(V_epsilon)>0,          h_epsilon ->0,
    lambda_n=binom(n,2).

All new coins equal gamma. If `q=1-gamma`, its cell arm durations are

    a_i(epsilon)=epsilon² h_i(epsilon)/gamma
                   -epsilon³ u_i(epsilon)/gamma²,
    b_i(epsilon)=epsilon² h_i(epsilon)/q
                   +epsilon³ u_i(epsilon)/q²,                  (1)

where `h_i,u_i` extend analytically to zero and `h_i(0)>0`. Its required ordinary connectors are strictly positive for every realizing epsilon. No boundary value is a source witness.

The [8 October cross-mechanism audit](../../../2026-10-08-dot-g4-cross-mechanism-certificate-attempt-1600z/ATTEMPT-A7-COMMON-CERTIFICATE-CROSS-MECHANISM-FAILURE.md) already explicitly rules out repair of its ordinary-target certificate by finitely many additional diagonal queries. The present statement is a direct further corollary: arbitrary fixed private targets, the SAME COMMON pair coordinate, and an actual one-sided interval within each finite diagonal fibre. It does not claim that diagonal insufficiency itself is new.

Supplier and review SHA256 pins:

- Fixed-coin theorem: `ebfacca60395f86272081df973ac161ebc88b9177383c1da2eb4bb2b8a996020`.
- Its `INDEPENDENT-HAND-REVIEW.md`: `344a1b146557d2b5eabf8ea8cb949136f2dd893f9f36f507206f7ab0b7e49d9c`.
- Cross-mechanism audit: `a6a7b3768e077bcfe2112602d1c927ba8abfe4e4bfe3c3d35d2632b11859fbbe`.

## 3. Exact insertion and COMMON deficit

Take `m>=max(F union {3})`. Choose epsilon sufficiently small that `h_epsilon<H`. Replace the chosen `E_H` segment in T by

    W_epsilon=E_(H-h_epsilon) V_epsilon.                         (2)

Its leading ordinary duration is strictly positive. The accepted private-bridge insertion grammar merges adjacent ordinary pieces if required and retains a finite strict private word. For every n<=m,

    d_n(W_epsilon)=exp(-lambda_n H).

No-merger diagonals multiply under the actual serial composition, so (2) proves the exact finite-prefix equality in T, whatever its other retained cells and their chronology.

For a single strict cell with arms a,b and coin g, set q=1-g. The SAME tuple gives

    c_2(B)=g exp(-a)+q exp(-b),
    d_2(B)=g² exp(-a)+q² exp(-b)+2gq,
    d_2(B)-c_2(B)=gq[2-exp(-a)-exp(-b)]>0.                      (3)

Under COMMON routing, conditional on no merger, both roots remain together and the next independent physical routing choice is again common to both. Thus these pair-survival probabilities multiply across private cells, just as their no-merger INDEPENDENT counterparts do. Ordinary factors have equal pair-survival in the two modes. Consequently

    c_2(W_epsilon)/exp(-H)
       =c_2(V_epsilon)/d_2(V_epsilon)
       =product_(i=1)^N c_2(B_i)/d_2(B_i) <1,                   (4)

and, with the fixed exterior factors of T cancelled,

    c_2(T_epsilon)/c_2(T)=product_i c_2(B_i)/d_2(B_i)<1.         (5)

The deficit is not caused by using different parameters in the two modes. Equations (3)–(5) evaluate the identical physical rival tuple.

## 4. The fibre contains a nontrivial interval

For fixed gamma and small a,b, direct Taylor expansion of (3) yields

    log[c_2(B)/d_2(B)]
       =-gamma q(a+b)+O((a+b)²).

Using (1), analyticity, and N fixed,

    log[c_2(T_epsilon)/c_2(T)]
       =-A epsilon²+O(epsilon³),
    A=sum_i h_i(0)>0.                                          (6)

All functions in (6) extend analytically to epsilon=0. Differentiating its analytic expansion gives derivative `-2A epsilon+O(epsilon²)<0` for sufficiently small positive epsilon. Therefore `c_2(T_epsilon)` is strictly decreasing there and its limit at zero is `c_2(T)`. Its image includes an interval of the form asserted in Section 1. Every interior point of that interval is realized by a finite strictly positive source, not by its boundary limit.

The inherited [strict private count asymptotic](../../../2026-10-01-sol61-g4-allcopy-2237z/CHAIN-COUNT-AND-STOPPING.md) gives a `-(K/2) log n` term for a word with K strict cells, apart from its quadratic and linear terms and a bounded remainder. Insertion adds N>=1 strict cells. Equality of the entire diagonal sequence would successively force equality of the quadratic, linear and logarithmic coefficients, contradicting that cell-count difference. Thus each fixed realizing rival differs at a later diagonal. No specific uniform later cap is asserted.

## 5. What the obstruction excludes

Any proposed target-relative support, recurrence, zero, total-positivity or moment-cone certificate based only on finitely many `d_n` receives exactly the same input on T and on these rivals. The identical data can therefore certify neither the target's `c_2` nor its entire COMMON law. The statement covers arbitrary finite postprocessing, not just polynomial tests. For a finite adaptive procedure, use the maximum arity on its target transcript; identical answers force the same transcript on a corresponding rival.

There is also no local error estimate of the form

    |c_2(W)-c_2(T)| <= omega(max_(n in F)|d_n(W)-d_n(T)|),
    omega(0)=0,

on a source neighbourhood that includes these shrinking-cell insertions. The right side is zero while (5) is strict. A chart restricted to the fixed target architecture is a different domain and is not contradicted.

The target COMMON scalar has an ordinary legal topology realization in the standard private bridge wrapper: with two A roots below the private word and one B root first meeting them above its output, the COMMON probability that the A pair forms the rooted cherry is `1-2 rho c_2/3`. Here `rho=exp(-a_ext)>0` accounts for every additional fixed A-exclusive ordinary edge outside the private word. If the word already comprises that entire exclusive path, rho=1. This explicit factor preserves strict positive wrapper passages and is unchanged by the substitution. Extra required taxa may be marginalized by the inherited selected-copy rule. This explains why the missing coordinate matters to the target finite COMMON gate. It does not say that the rival matches other INDEPENDENT topology coordinates of that wrapper.

## 6. Master boundary and next usable direction

These are fixed-target exact rivals for every finite **diagonal** prefix, with one shared tuple per rival. They are not rivals for every finite prefix of the full legal INDEPENDENT menu. The accepted all-law INDEPENDENT-to-COMMON theorem is consistent with this result: it uses richer full-law information, and the displayed rivals eventually differ even on a later diagonal.

The still-open all-arity diagonal-to-COMMON question in `chronology/continuation-2110z/PRIVATE-DIAGONAL-COMMON-GATE.md` is also untouched. Arbitrarily long finite exact matches do not provide two finite sources with equal diagonals at every arity.

A successful finite INDEPENDENT-to-COMMON bridge must exploit additional full forest/topology coordinates or prove a source restriction forced by those coordinates. It cannot obtain the required finite COMMON pair equality from the private diagonal sequence alone. No new primary theorem is needed to establish this obstruction; the accepted source supplier already decides the proposed inference.

Verification: hand composition, strict inequalities and analytic Taylor algebra, with the accepted arbitrary-cap supplier reused. No parameter search, compiler run, symbolic computation, Lean verification, Git operation or new all-cap return proof was performed.
