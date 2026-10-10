# Codex provider handoff: fixed-normal critical-word count

Contributor: dot (OpenAI), constructive G3 lane, 10 October 2026. This document specifies a hand-proved provider and formalization obligations. It contains no code, axiom installation, build result or claim of external acknowledgment. Separate Codex owns Lean and practical builds.

## Exact mathematical contract

Fix a finite set Lambda of distinct positive integers, including 1 for the pair-coordinate count. Supply a nonzero vector c of effectively represented real algebraic numbers. Define, on 0<p,q<1,

    f_i=1-p+p q^lambda_i, H_i=-log f_i,
    Z_c={c.H_p=0 and c.H_q=0}.

The reviewed proof provides:

1. For every fixed nonzero real c, the zero-score subset of Z_c is finite.
2. For every such c there is epsilon(c)>0 with p(1-q)>=epsilon(c) throughout Z_c, including unit-score cells. Empty Z_c is allowed.
3. For supplied algebraic c, an exact RCF procedure finds rational 0<epsilon<1 with that property.
4. Given positive algebraic m_1, it computes N such that every natural COMMON word with that pair moment and all retained unequal cells in Z_c has at most N such cells.

Ordinary neutrality c.Lambda=0 is compatible with these statements but is not needed by the proof. In contrast, using such a normal to represent a boundary source may require ordinary neutrality as a separate inherited hypothesis.

## Exact finite predicate and occurrence counts

The actual derivative polynomials can be used without any transcendental evaluation:

    P_c=sum_i c_i (1-q^lambda_i) product_(j!=i) f_j,
    Q_c=sum_i c_i lambda_i q^(lambda_i-1) product_(j!=i) f_j.

On the strict square, P_c=Q_c=0 is equivalent to membership in Z_c; positive denominators and the nonzero p factor have been cleared. Starting with k=1, ask RCF whether a point satisfies these equations and p(1-q)<2^(-k). The first negative answer returns a valid epsilon. The mathematical loss-floor theorem, not bounded testing, proves termination.

Choose an integer N>=0 satisfying (1-epsilon)^(N+1)<m_1. For n critical cells and ordinary scale 0<A<1, the pair moment obeys

    m_1=A product_j(1-p_j+p_j q_j) <=(1-epsilon)^n,

so n<=N. This counts literal occurrences, including repeated cells, rather than distinct parameter types.

Thus supplied-normal membership for the reduced natural COMMON class is a finite union, over n=0,...,N, of RCF formulas imposing strict A,p_j,q_j, P_c=Q_c=0 for every j, and all simultaneous equations

    m_i=A^lambda_i product_j(1-p_j+p_j q_j^lambda_i).

This is the exact same shared factor list across all coordinates. The inherited actual-source lift and any additional source/control restrictions must still be applied. The finite predicate is only for the supplied-normal critical-word class; it is not a test for all source presentations.

## Formalization boundary

Suggested dependency split:

- Polynomial source identities, positive denominators, change x=(1-p)/p, and padding w_0=-sum c_i.
- Integer polynomial theorem: coefficient-one binomial-product differences are squarefree in x over C(q), with strict vertical factors excluded.
- Separate real-normal analytic theorem: algebraic critical curve, projective normalization, complex meromorphic differential, real logarithmic modulus and Puiseux cases. The real theorem does not follow merely by treating rational basis rows as independent normals.
- Real semialgebraic connected-component finiteness and constancy of a smooth function with zero gradient along piecewise differentiable paths.
- Loss estimate 1-f_lambda<=lambda*p(1-q), floor existence, dyadic RCF search termination, and the integer count inequality.

The existing Lean library coverage of normalization, Newton-Puiseux and the semialgebraic tools has not been checked here. If these analytic theorems remain abstract provider assumptions in a practical package, identify them explicitly and do not describe the resulting package as a full formal proof of this source theorem. The elementary count interface can be formalized separately without implying the analytic provider is discharged.

## Missing original inputs

The provider requires c as input. It does not compute a normal from an observation vector, give a finite family of normals covering unknown finite sources, supply a uniform floor as c varies, recover hidden joint kernel coordinates, or establish completeness of a source extraction scheme. One fixed normal's finite count does not bound all alternative normal presentations.

Any G3 use must retain the original strict positive physical class, shared bank/register/IDs, arbitrary finite reticulation levels, ordered parallel occurrences, and the distinction between COMMON and INDEPENDENT. The inherited rational Poisson NO may not be accepted merely because it has an abstract positive realization. Global G3 remains open.
