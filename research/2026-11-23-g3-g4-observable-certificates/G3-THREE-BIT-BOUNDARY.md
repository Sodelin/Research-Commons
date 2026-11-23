# Exact boundary for the three-bit G3 summary

23 November 2026. Hand proof; not a characterization of physical G3 sources.

Let three same-event block indicators in one row have an exchangeable law. Write
\(p=\mathbb E X_1\), \(q=\mathbb E X_1X_2\), and
\(r=\mathbb E X_1X_2X_3\). Put
\[
H=\begin{pmatrix}1&p\\p&q\end{pmatrix},\qquad
A=\begin{pmatrix}p&q\\q&r\end{pmatrix},\qquad
B=H-A.
\]
These are the exact tests for extendibility of this binary summary to
exchangeable block laws of arbitrarily large size: **both A and B must be
positive semidefinite, and that is sufficient for this summary**. Not
necessarily for the remaining topology readouts or for one admitted source.

## Necessity

In an exchangeable N-block extension let T be the fraction of successes.
The first three ordinary moments of T approach p, q, r as N tends to infinity:
draw j indices independently with replacement; conditional on no repeats
their joint success probability is the supplied j-block moment, and the
chance of a repeat is at most choose(j,2)/N. Nonnegativity of
T(a+bT)^2 and (1-T)(a+bT)^2 now gives A and B PSD by taking limits. No
assumption of conditional independence in the physical source is needed.

## Sufficiency

Equip R²/ker(H) with inner product <u,v> = uᵀHv. Since 0≤A≤H, the bilinear
form uᵀAv vanishes on ker(H) and so defines a self-adjoint operator M there,
by <u,Mv>=uᵀAv. It satisfies 0≤M≤1. For the images f=[(1,0)] and g=[(0,1)],
Af has the same coordinates as Hg on representatives, hence Mf=g.
Therefore the first four spectral moments of f are 1, p, q, r:
< f,f>=1, <f,Mf>=p, <Mf,Mf>=q, <Mf,M(Mf)>=r.
The spectral theorem produces at most two atoms of a probability measure
on [0,1], at the eigenvalues of M, with weights the squared components of
f on the corresponding eigenspaces. This also covers singular H by the
quotient construction. Draw a latent Bernoulli parameter from that measure
and then draw any number of conditionally independent bits. The first
three mixed success probabilities are p, q, r, and inclusion–exclusion
gives the entire exchangeable three-bit table.

## Consequence for the pilot

The two matrices subsume the previous q≥p² screen (their sum is H). No
stronger obstruction can come from demanding exchangeable extendibility
of these three balanced-quartet bits alone. To reject more data with this
strategy, expose other events jointly, use more blocks when already
available, or use additional constraints of the actual G3 source class.
The rational checker determines signs exactly. This hand proof of
sufficiency does not make its non-reject outcome a G3 YES.
