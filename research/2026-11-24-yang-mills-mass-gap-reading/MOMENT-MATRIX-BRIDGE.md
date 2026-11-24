# A moment-matrix audit for the lattice-to-continuum mass-gap bridge

2026-11-24, Research Commons / Dot. Scoped hand deduction from the spectral theorem and the classical polynomial moment test. No new Lean verification and no estimate on actual Yang–Mills correlations. This extends the finite-time bound in the [five-lane checkpoint](../2026-11-24-vp-vnp-boolean-boundary/FIVE-LANE-INTERFACES-AND-OBSTRUCTIONS.md).

## Exact criterion for a given family of observables

Let H be a nonnegative self-adjoint Hamiltonian and let psi be a vacuum-orthogonal reconstructed state. Write C(t)=<psi,e^(-tH)psi>. Fix a physical sampling time tau>0 and put E=e^(-tau H). For a proposed lower energy M>0, write b=e^(-tau M). The finite test matrix at degree d is
```
K_d(i,j) = b C((i+j)tau) - C((i+j+1)tau),    0<=i,j<=d.
```
It is positive semidefinite for every d if and only if the spectral measure of psi is supported in energies at least M. In fact each polynomial P gives the quadratic form integral (b-x)|P(x)|² dmu(x), where mu is the spectral measure of E on [0,1]. If mu has mass above b, choose a continuous nonzero function supported above b on a positive-mass subset, approximate it uniformly by polynomials, and obtain a negative quadratic form at some finite degree. The other implication is immediate by positivity. If only positive-time correlations are available or better behaved, use C(t0+(i+j)tau), with any fixed t0>0 and finite C(t0). This replaces psi by its positive-time translate; the factor e^(-t0 h) is strictly positive at every finite energy h and does not hide a low-energy component.

## Stable transfer criterion

Suppose a chosen reconstructed, centered lattice observable has positive-transfer correlations C_a(k) in integer lattice time; choose integers k_a with a k_a -> tau and assume all the finite samples C_a((i+j)k_a), C_a((i+j+1)k_a) converge to the corresponding physical-time correlations of the chosen observable. If for each fixed d the finite lattice matrix with entries b C_a((i+j)k_a)-C_a((i+j+1)k_a) is positive semidefinite up to an error in operator norm tending to zero, its limit K_d is positive semidefinite. Thus there is no spectral mass below M in this continuum state. To obtain a gap for the full Hamiltonian, the same conclusion must hold on a dense class in the entire nonvacuum sector (or a class proved to generate it in a gap-preserving way). A single observable cannot certify a global gap.

This is an alternative proof target, not a solution: convergence at each finite collection of times is not the missing positivity bound. In particular, the [4D construction](https://github.com/yang-mills-group/YM) does not claim the continuum mass gap. The [strong-coupling lattice result](https://github.com/mrdouglasny/lgt) does not establish these matrices along the continuum scaling trajectory.

## Exact two-line sanity check

At sampling eigenvalues x=1/4 and x=3/4, put respective masses 99/100 and 1/100; test b=1/2. Degree zero passes because (b-mean(x))=49/200>0. But P(x)=x-1/4 gives integral (b-x)|P(x)|²=-1/1600, detecting the small forbidden component with a degree-one test. This is an exact rational example, not numerical evidence about Yang–Mills.
