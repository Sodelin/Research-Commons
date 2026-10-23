> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Rational paired cap-three kernels with arbitrarily large exact word minimum

21 October 2026. Authored HAND theorem and exact finite controls. No historical
novelty, independent review, Lean pass or complete G3 recognition is claimed.
This is a private-word kernel theorem; it does not add those coordinates to an
original observation menu, or exclude alternative original cores.

## A universal gain bound for one physical paired cell

For one strict natural bigon, write h=1-p and

    C=p*x+h*y,                       (COMMON pair no-merger)
    Q=p^2*x+h^2*y+2*p*h,             (INDEPENDENT pair)
    R=p^3*x^3+h^3*y^3+3*p^2*h*x+3*p*h^2*y. (INDEPENDENT triple)

The same physical x,y,p must occur in all three. Direct expansion gives

    3*C*Q-2*R
      = p^3*x^2*(3-2*x) + h^3*y^2*(3-2*y) + 3*p*h*x*y > 0.     (1)

All summands are positive for 0<x,y,p<1. Thus

    R/(C*Q) < 3/2.                                           (2)

NO equal-arm/ordinary-COMMON-face assumption is needed. The bound is sharp
as a supremum: at p=1/2 and x=y=s, its left side is

    rho(s)=(s^2+3)/(2*(1+s)) -> 3/2 as s->0+.

For any legal private word with L bigons and positive ordinary passage
product A<1, all three no-merger coordinates multiply on serial current-root
composition. An ordinary survival a contributes a,a,a^3 respectively. Hence
the entire paired word satisfies

    T := R_word/(C_word*Q_word)
       = A * product_i [R_i/(C_i*Q_i)] < (3/2)^L.             (3)

This includes L=0: T=A<1. Each multiplying scalar comes from the SAME word
and parameter tuple. No independent mode-by-mode refit is used. For any
supplied budget B, the exact comparison `T >= (3/2)^B` excludes EVERY word
of length at most B, even with unequal arms and freely chosen strict coins.
This is a LOWER bound on required length, never a stopping UPPER bound.

## Every positive integer occurs as an exact minimum

Given N>=1, choose N identical bigons with

    x=y=s=1/(10*N), p=1/2,

and give their N+1 ordinary passages product A=9/10. All can be rational
and strict: let M=10(N+1) and use passage survivals

    a_j=(M-j)/(M-j+1), j=1,...,N+1.

The telescoping product is 9/10. This is an actual legal positive word on
an eligible bridge, not a fractional cell or source mixture. Its coordinates
are the rational numbers

    C_N=A*s^N,
    Q_N=A*((1+s)/2)^N,
    R_N=A^3*(s*(s^2+3)/4)^N.

Its COMMON triple also equals C_N^3, but competitors do not need that extra
coordinate for the following lower bound. Its gain is

    T_N=A*rho(s)^N.

Because rho(s)>(3/2)/(1+s), and

    (1+1/(10N))^N
      = sum_(k=0)^N binom(N,k)/(10N)^k
      <= sum_(k=0)^N 10^(-k) < 10/9,

we have

    T_N > (81/100)*(3/2)^N
        = (243/200)*(3/2)^(N-1) > (3/2)^(N-1).               (4)

Every competing representation with L<=N-1 contradicts (3). The displayed
N-cell word attains the target, so its minimum number of bigons is EXACTLY N
among all strict paired private words. Full paired cap-three forest-kernel
agreement would in particular match the three coordinates used here.

## Consequence and limits for G3

There is no universal fixed bigon cap for paired cap-three private kernels,
even on four taxa with a fixed eligible bridge type and rational source
parameters. This rules out extending the I-only one-bigon theorem to any
input-independent constant for BOTH at this interface. The older scoped
minimum-two example remains valid; (1)--(4) give an unbounded exact family.

The bound is computable from SUPPLIED target coordinates and useful for
rejecting a supplied search budget. It does not give an input-effective
upper bound on ONE witness. Input encodings grow in this family. Nor does
it prove a lower bound over ALL original core templates under an arbitrary
coarsened topology menu. The inherited fixed-alphabet pair-budget upper
bound is consistent with this result: its positive pair target decreases
with N here. There is no undecidability inference.

The general G3 recognition/NO-termination goal remains OPEN. A complete
solver must retain the real same-source count issue for BOTH, while using
the separately scoped I-only cap-three branch where justified.

`paired-cap3-count-checks.wl` checks (1), the sharp limit, telescoping strict
passages and exact two-sided gain bounds for N=1,...,12. These are finite
controls; the arbitrary-N proof is the hand argument above.
