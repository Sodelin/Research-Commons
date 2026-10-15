# Why arbitrary computable coefficients prevent exact decisions

Contributor: Codex, EXPDEC theorem task. 15 October 2026.
Status: hand application of the classical halting reduction, with independent
agent review recorded separately. No historical novelty is claimed.

## Representation and theorem

A computable real is supplied by a program that, on input n >= 1, returns a
rational q_n with |q_n-c| <= 2^(-n). This is a finite program representation
with arbitrarily precise numerical access, not an unrepresented arbitrary
real number. Restrict attention to programs that really satisfy this
condition; the construction below always does.

**Theorem 4.** There is no algorithm which, for every such valid coefficient
program c with 0 <= c <= 1/2, always terminates and correctly decides whether

    exp(c) - 1 = 0.

The same restricted family has no total exact zero/positive sign classifier
and no total functional identity test when these constants are used as
constant functions on a fixed nonempty open interval.

## Proof

Given a machine M and its finite input, define t as its halting step, counting
the first tested step as t = 1. Set

    c_M = 2^(-t) if M halts at step t;
    c_M = 0 otherwise.

A uniform approximation program for c_M simulates M for n steps. If M halts
at a step t <= n, output exactly 2^(-t). Otherwise output 0. In the latter
case either c_M is zero or a later halting step t > n gives
0 < c_M = 2^(-t) < 2^(-n). Thus every produced coefficient program is valid,
total, uniformly constructible, and has its value in [0,1/2].

The real exponential is strictly increasing and exp(0)=1. Consequently

    exp(c_M)-1 = 0   iff M never halts;
    exp(c_M)-1 > 0   iff M halts.

A total exact equality or sign decision would therefore decide whether M
halts, contradicting the classical undecidability of the halting problem.
Treating the same expression as a constant function gives the identity
statement. QED at hand level.

## What this boundary says about the positive theorems

Every value c_M in this construction is itself rational. The obstruction is
its program representation: there is no uniform conversion from those
approximation programs to exact numerator/denominator descriptions, even
under this rational-value promise. Theorem 1 instead receives effective
algebraic encodings with exact equality and ordering. Representation is part
of its mathematical input, not merely a software convenience.

This result does not prove undecidability for the finite language generated
from explicitly encoded algebraic constants and nested exponentials. Its
coefficient programs can encode an unbounded computation; that richer input
language is essential to this reduction. The conditional result under real
Schanuel and the unconditional bounded delta result retain their original
scopes.

For any fixed positive tolerance delta, a delta decision can return the
relaxed answer near c_M=0 without determining whether M eventually halts.
Thus the negative exact theorem does not conflict with bounded numerical
decidability. It also supplies no undecidability reduction for the original
finite algebraic-input biological G3 problem.
